import RequestProject.DVPCos1215o2Table

/-!
# The cosine partial-sum floor, `t = 1215/2` (N = 1000)
-/

open Finset

noncomputable section

namespace CriticalLinePhasor.DVP

/-- The cosine sequence of the `t = 1215/2` segment certificate. -/
def cos1215o2c (n : ℕ) : ℝ := Real.cos (((1215:ℕ):ℝ) * (Real.log n / 2))

theorem psum1215o2_11 : ((2794459/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 11, cos1215o2c k := by
  rw [Finset.Icc_self, Finset.sum_singleton]
  have h : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 11 - ((2794959/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_11).1
  push_cast at h ⊢
  linarith

theorem psum1215o2_12 : ((5132877/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 12, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 12, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 11, cos1215o2c k) + cos1215o2c 12 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 11) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_11
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 12 - ((-455041/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_12).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_13 : ((756459/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 13, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 13, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 12, cos1215o2c k) + cos1215o2c 13 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 12) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_12
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 13 - ((9997303/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_13).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_14 : ((10201821/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 14, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 14, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 13, cos1215o2c k) + cos1215o2c 14 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 13) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_13
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 14 - ((2637731/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_14).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_15 : ((25343411/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 15, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 15, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 14, cos1215o2c k) + cos1215o2c 15 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 14) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_14
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 15 - ((4940769/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_15).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_16 : ((34329397/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 16, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 16, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 15, cos1215o2c k) + cos1215o2c 16 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 15) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_15
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 16 - ((4493493/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_16).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_17 : ((43476881/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 17, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 17, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 16, cos1215o2c k) + cos1215o2c 17 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 16) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_16
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 17 - ((2287121/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_17).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_18 : ((3378541/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 18, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 18, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 17, cos1215o2c k) + cos1215o2c 18 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 17) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_17
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 18 - ((-9690471/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_18).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_19 : ((29979251/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 19, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 19, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 18, cos1215o2c k) + cos1215o2c 19 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 18) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_18
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 19 - ((-3805159/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_19).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_20 : ((11980733/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 20, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 20, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 19, cos1215o2c k) + cos1215o2c 20 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 19) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_19
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 20 - ((-1203357/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_20).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_21 : ((17365779/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 21, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 21, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 20, cos1215o2c k) + cos1215o2c 21 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 20) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_20
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 21 - ((-6594687/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_21).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_22 : ((23857887/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 22, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 22, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 21, cos1215o2c k) + cos1215o2c 22 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 21) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_21
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 22 - ((1623277/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_22).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_23 : ((1824733/625000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 23, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 23, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 22, cos1215o2c k) + cos1215o2c 23 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 22) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_22
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 23 - ((5338841/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_23).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_24 : ((1380557/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 24, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 24, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 23, cos1215o2c k) + cos1215o2c 24 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 23) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_23
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 24 - ((-395897/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_24).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_25 : ((36681/12500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 25, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 25, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 24, cos1215o2c k) + cos1215o2c 25 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 24) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_24
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 25 - ((86733/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_25).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_26 : ((39303073/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 26, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 26, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 25, cos1215o2c k) + cos1215o2c 26 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 25) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_25
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 26 - ((9959273/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_26).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_27 : ((6824553/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 27, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 27, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 26, cos1215o2c k) + cos1215o2c 27 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 26) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_26
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 27 - ((-1294827/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_27).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_28 : ((4800133/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 28, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 28, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 27, cos1215o2c k) + cos1215o2c 28 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 27) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_27
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 28 - ((4279299/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_28).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_29 : ((14709631/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 29, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 29, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 28, cos1215o2c k) + cos1215o2c 29 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 28) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_28
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 29 - ((-4490401/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_29).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_30 : ((3531149/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 30, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 30, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 29, cos1215o2c k) + cos1215o2c 30 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 29) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_29
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 30 - ((1473307/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_30).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_31 : ((9045291/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 31, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 31, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 30, cos1215o2c k) + cos1215o2c 31 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 30) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_30
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 31 - ((1983193/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_31).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_32 : ((26828933/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 32, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 32, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 31, cos1215o2c k) + cos1215o2c 32 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 31) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_31
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 32 - ((8432411/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_32).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_33 : ((62821273/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 33, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 33, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 32, cos1215o2c k) + cos1215o2c 33 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 32) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_32
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 33 - ((9164407/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_33).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_34 : ((14473449/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 34, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 34, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 33, cos1215o2c k) + cos1215o2c 34 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 33) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_33
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 34 - ((2386743/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_34).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_35 : ((14531223/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 35, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 35, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 34, cos1215o2c k) + cos1215o2c 35 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 34) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_34
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 35 - ((28987/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_35).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_36 : ((3137369/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 36, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 36, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 35, cos1215o2c k) + cos1215o2c 36 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 35) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_35
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 36 - ((-1981547/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_36).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_37 : ((17426599/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 37, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 37, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 36, cos1215o2c k) + cos1215o2c 37 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 36) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_36
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 37 - ((435001/625000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_37).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_38 : ((8371521/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 38, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 38, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 37, cos1215o2c k) + cos1215o2c 38 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 37) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_37
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 38 - ((-683307/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_38).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_39 : ((69003831/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 39, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 39, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 38, cos1215o2c k) + cos1215o2c 39 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 38) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_38
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 39 - ((2032663/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_39).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_40 : ((12785891/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 40, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 40, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 39, cos1215o2c k) + cos1215o2c 40 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 39) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_39
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 40 - ((-158543/312500 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_40).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_41 : ((73384023/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 41, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 41, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 40, cos1215o2c k) + cos1215o2c 41 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 40) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_40
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 41 - ((590973/625000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_41).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_42 : ((32989663/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 42, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 42, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 41, cos1215o2c k) + cos1215o2c 42 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 41) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_41
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 42 - ((-7403697/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_42).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_43 : ((60501731/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 43, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 43, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 42, cos1215o2c k) + cos1215o2c 43 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 42) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_42
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 43 - ((-1095319/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_43).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_44 : ((3390673/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 44, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 44, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 43, cos1215o2c k) + cos1215o2c 44 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 43) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_43
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 44 - ((7312729/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_44).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_45 : ((19313939/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 45, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 45, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 44, cos1215o2c k) + cos1215o2c 45 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 44) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_44
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 45 - ((295103/312500 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_45).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_46 : ((81602069/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 46, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 46, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 45, cos1215o2c k) + cos1215o2c 46 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 45) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_45
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 46 - ((4347313/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_46).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_47 : ((81111597/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 47, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 47, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 46, cos1215o2c k) + cos1215o2c 47 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 46) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_46
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 47 - ((-3824/78125 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_47).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_48 : ((19604711/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 48, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 48, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 47, cos1215o2c k) + cos1215o2c 48 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 47) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_47
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 48 - ((-2691753/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_48).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_49 : ((19028847/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 49, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 49, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 48, cos1215o2c k) + cos1215o2c 49 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 48) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_48
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 49 - ((-287807/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_49).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_50 : ((9590301/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 50, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 50, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 49, cos1215o2c k) + cos1215o2c 50 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 49) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_49
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 50 - ((30401/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_50).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_51 : ((1286627/156250 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 51, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 51, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 50, cos1215o2c k) + cos1215o2c 51 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 50) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_50
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 51 - ((17571/31250 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_51).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_52 : ((719814/78125 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 52, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 52, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 51, cos1215o2c k) + cos1215o2c 52 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 51) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_51
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 52 - ((1224133/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_52).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_53 : ((24791993/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 53, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 53, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 52, cos1215o2c k) + cos1215o2c 53 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 52) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_52
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 53 - ((351639/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_53).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_54 : ((47494943/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 54, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 54, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 53, cos1215o2c k) + cos1215o2c 54 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 53) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_53
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 54 - ((-2088543/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_54).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_55 : ((3415069/400000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 55, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 55, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 54, cos1215o2c k) + cos1215o2c 55 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 54) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_54
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 55 - ((-9612161/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_55).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_56 : ((2215109/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 56, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 56, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 55, cos1215o2c k) + cos1215o2c 56 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 55) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_55
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 56 - ((645727/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_56).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_57 : ((97012531/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 57, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 57, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 56, cos1215o2c k) + cos1215o2c 57 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 56) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_56
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 57 - ((8409171/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_57).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_58 : ((88586697/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 58, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 58, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 57, cos1215o2c k) + cos1215o2c 58 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 57) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_57
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 58 - ((-4212417/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_58).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_59 : ((2225091/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 59, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 59, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 58, cos1215o2c k) + cos1215o2c 59 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 58) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_58
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 59 - ((417943/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_59).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_60 : ((5985813/625000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 60, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 60, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 59, cos1215o2c k) + cos1215o2c 60 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 59) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_59
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 60 - ((105787/156250 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_60).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_61 : ((21498079/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 61, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 61, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 60, cos1215o2c k) + cos1215o2c 61 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 60) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_60
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 61 - ((-2444923/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_61).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_62 : ((1495267/156250 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 62, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 62, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 61, cos1215o2c k) + cos1215o2c 62 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 61) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_61
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 62 - ((2426443/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_62).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_63 : ((87112043/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 63, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 63, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 62, cos1215o2c k) + cos1215o2c 63 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 62) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_62
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 63 - ((-1716809/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_63).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_64 : ((47440367/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 64, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 64, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 63, cos1215o2c k) + cos1215o2c 64 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 63) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_63
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 64 - ((7769691/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_64).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_65 : ((43536279/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 65, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 65, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 64, cos1215o2c k) + cos1215o2c 65 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 64) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_64
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 65 - ((-975897/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_65).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_66 : ((95723739/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 66, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 66, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 65, cos1215o2c k) + cos1215o2c 66 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 65) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_65
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 66 - ((8652181/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_66).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_67 : ((85999829/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 67, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 67, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 66, cos1215o2c k) + cos1215o2c 67 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 66) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_66
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 67 - ((-972291/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_67).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_68 : ((95821417/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 68, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 68, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 67, cos1215o2c k) + cos1215o2c 68 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 67) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_67
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 68 - ((2455647/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_68).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_69 : ((44233597/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 69, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 69, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 68, cos1215o2c k) + cos1215o2c 69 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 68) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_68
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 69 - ((-7353223/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_69).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_70 : ((89886371/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 70, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 70, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 69, cos1215o2c k) + cos1215o2c 70 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 69) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_69
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 70 - ((1420177/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_70).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_71 : ((96057017/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 71, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 71, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 70, cos1215o2c k) + cos1215o2c 71 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 70) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_70
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 71 - ((3085823/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_71).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_72 : ((43029267/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 72, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 72, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 71, cos1215o2c k) + cos1215o2c 72 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 71) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_71
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 72 - ((-9997483/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_72).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_73 : ((4543909/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 73, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 73, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 72, cos1215o2c k) + cos1215o2c 73 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 72) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_72
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 73 - ((2410323/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_73).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_74 : ((48489801/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 74, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 74, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 73, cos1215o2c k) + cos1215o2c 74 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 73) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_73
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 74 - ((3051211/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_74).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_75 : ((21901243/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 75, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 75, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 74, cos1215o2c k) + cos1215o2c 75 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 74) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_74
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 75 - ((-937363/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_75).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_76 : ((21494463/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 76, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 76, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 75, cos1215o2c k) + cos1215o2c 76 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 75) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_75
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 76 - ((-40653/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_76).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_77 : ((23986993/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 77, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 77, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 76, cos1215o2c k) + cos1215o2c 77 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 76) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_76
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 77 - ((124639/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_77).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_78 : ((6053597/625000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 78, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 78, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 77, cos1215o2c k) + cos1215o2c 78 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 77) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_77
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 78 - ((45529/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_78).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_79 : ((2176711/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 79, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 79, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 78, cos1215o2c k) + cos1215o2c 79 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 78) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_78
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 79 - ((-611757/625000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_79).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_80 : ((83002769/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 80, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 80, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 79, cos1215o2c k) + cos1215o2c 80 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 79) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_79
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 80 - ((-4064671/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_80).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_81 : ((22620203/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 81, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 81, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 80, cos1215o2c k) + cos1215o2c 81 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 80) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_80
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 81 - ((7479043/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_81).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_82 : ((6219119/625000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 82, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 82, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 81, cos1215o2c k) + cos1215o2c 82 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 81) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_81
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 82 - ((2256523/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_82).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_83 : ((49978513/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 83, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 83, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 82, cos1215o2c k) + cos1215o2c 83 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 82) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_82
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 83 - ((226061/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_83).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_84 : ((1434981/156250 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 84, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 84, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 83, cos1215o2c k) + cos1215o2c 84 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 83) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_83
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 84 - ((-4058621/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_84).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_85 : ((41117147/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 85, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 85, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 84, cos1215o2c k) + cos1215o2c 85 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 84) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_84
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 85 - ((-960349/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_85).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_86 : ((4858693/625000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 86, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 86, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 85, cos1215o2c k) + cos1215o2c 86 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 85) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_85
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 86 - ((-2247103/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_86).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_87 : ((402217/50000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 87, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 87, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 86, cos1215o2c k) + cos1215o2c 87 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 86) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_86
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 87 - ((84541/312500 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_87).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_88 : ((88480633/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 88, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 88, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 87, cos1215o2c k) + cos1215o2c 88 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 87) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_87
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 88 - ((8038233/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_88).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_89 : ((49232023/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 89, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 89, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 88, cos1215o2c k) + cos1215o2c 89 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 88) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_88
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 89 - ((9984413/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_89).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_90 : ((107472931/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 90, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 90, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 89, cos1215o2c k) + cos1215o2c 90 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 89) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_89
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 90 - ((1801977/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_90).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_91 : ((113856133/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 91, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 91, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 90, cos1215o2c k) + cos1215o2c 91 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 90) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_90
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 91 - ((3192101/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_91).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_92 : ((29288613/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 92, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 92, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 91, cos1215o2c k) + cos1215o2c 92 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 91) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_91
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 92 - ((3299319/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_92).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_93 : ((117671171/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 93, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 93, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 92, cos1215o2c k) + cos1215o2c 93 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 92) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_92
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 93 - ((517719/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_93).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_94 : ((58026579/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 94, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 94, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 93, cos1215o2c k) + cos1215o2c 94 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 93) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_93
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 94 - ((-1617013/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_94).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_95 : ((113022007/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 95, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 95, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 94, cos1215o2c k) + cos1215o2c 95 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 94) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_94
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 95 - ((-3030151/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_95).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_96 : ((21851259/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 96, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 96, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 95, cos1215o2c k) + cos1215o2c 96 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 95) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_95
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 96 - ((-470589/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_96).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_97 : ((105377697/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 97, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 97, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 96, cos1215o2c k) + cos1215o2c 97 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 96) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_96
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 97 - ((-1938799/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_97).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_98 : ((101986841/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 98, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 98, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 97, cos1215o2c k) + cos1215o2c 98 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 97) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_97
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 98 - ((-105933/312500 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_98).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_99 : ((49851883/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 99, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 99, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 98, cos1215o2c k) + cos1215o2c 99 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 98) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_98
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 99 - ((-91283/400000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_99).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_100 : ((99176927/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 100, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 100, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 99, cos1215o2c k) + cos1215o2c 100 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 99) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_99
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 100 - ((-525839/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_100).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_101 : ((101022363/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 101, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 101, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 100, cos1215o2c k) + cos1215o2c 101 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 100) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_100
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 101 - ((461609/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_101).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_102 : ((52835627/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 102, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 102, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 101, cos1215o2c k) + cos1215o2c 102 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 101) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_101
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 102 - ((4649891/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_102).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_103 : ((11311653/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 103, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 103, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 102, cos1215o2c k) + cos1215o2c 103 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 102) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_102
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 103 - ((1861569/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_103).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_104 : ((24523307/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 104, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 104, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 103, cos1215o2c k) + cos1215o2c 104 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 103) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_103
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 104 - ((1900201/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_104).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_105 : ((33124879/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 105, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 105, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 104, cos1215o2c k) + cos1215o2c 105 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 104) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_104
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 105 - ((9883981/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_105).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_106 : ((1122327/80000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 106, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 106, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 105, cos1215o2c k) + cos1215o2c 106 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 105) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_105
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 106 - ((7792359/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_106).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_107 : ((35845973/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 107, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 107, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 106, cos1215o2c k) + cos1215o2c 107 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 106) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_106
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 107 - ((3094017/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_107).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_108 : ((140261789/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 108, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 108, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 107, cos1215o2c k) + cos1215o2c 108 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 107) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_107
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 108 - ((-3121103/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_108).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_109 : ((131837907/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 109, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 109, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 108, cos1215o2c k) + cos1215o2c 109 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 108) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_108
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 109 - ((-4211441/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_109).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_110 : ((121974221/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 110, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 110, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 109, cos1215o2c k) + cos1215o2c 110 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 109) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_109
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 110 - ((-4931343/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_110).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_111 : ((116166811/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 111, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 111, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 110, cos1215o2c k) + cos1215o2c 111 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 110) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_110
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 111 - ((-580641/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_111).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_112 : ((118301679/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 112, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 112, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 111, cos1215o2c k) + cos1215o2c 112 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 111) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_111
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 112 - ((533967/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_112).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_113 : ((25441063/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 113, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 113, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 112, cos1215o2c k) + cos1215o2c 113 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 112) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_112
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 113 - ((2226159/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_113).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_114 : ((851077/62500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 114, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 114, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 113, cos1215o2c k) + cos1215o2c 114 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 113) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_113
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 114 - ((1793601/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_114).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_115 : ((34379359/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 115, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 115, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 114, cos1215o2c k) + cos1215o2c 115 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 114) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_114
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 115 - ((336529/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_115).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_116 : ((129755617/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 116, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 116, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 115, cos1215o2c k) + cos1215o2c 116 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 115) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_115
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 116 - ((-7760819/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_116).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_117 : ((120490993/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 117, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 117, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 116, cos1215o2c k) + cos1215o2c 117 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 116) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_116
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 117 - ((-1157953/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_117).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_118 : ((29943397/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 118, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 118, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 117, cos1215o2c k) + cos1215o2c 118 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 117) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_117
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 118 - ((-143281/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_118).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_119 : ((128615213/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 119, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 119, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 118, cos1215o2c k) + cos1215o2c 119 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 118) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_118
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 119 - ((70741/80000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_119).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_120 : ((17021823/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 120, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 120, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 119, cos1215o2c k) + cos1215o2c 120 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 119) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_119
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 120 - ((7560371/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_120).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_121 : ((132423303/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 121, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 121, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 120, cos1215o2c k) + cos1215o2c 121 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 120) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_120
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 121 - ((-3750281/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_121).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_122 : ((24493821/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 122, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 122, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 121, cos1215o2c k) + cos1215o2c 122 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 121) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_121
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 122 - ((-4976599/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_122).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_123 : ((60486721/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 123, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 123, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 122, cos1215o2c k) + cos1215o2c 123 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 122) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_122
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 123 - ((-1494663/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_123).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_124 : ((5213721/400000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 124, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 124, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 123, cos1215o2c k) + cos1215o2c 124 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 123) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_123
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 124 - ((9370583/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_124).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_125 : ((16918037/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 125, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 125, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 124, cos1215o2c k) + cos1215o2c 125 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 124) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_124
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 125 - ((5002271/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_125).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_126 : ((127395509/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 126, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 126, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 125, cos1215o2c k) + cos1215o2c 126 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 125) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_125
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 126 - ((-7947787/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_126).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_127 : ((120636043/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 127, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 127, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 126, cos1215o2c k) + cos1215o2c 127 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 126) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_126
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 127 - ((-3379233/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_127).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_128 : ((127641689/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 128, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 128, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 127, cos1215o2c k) + cos1215o2c 128 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 127) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_127
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 128 - ((3503323/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_128).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_129 : ((67440971/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 129, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 129, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 128, cos1215o2c k) + cos1215o2c 129 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 128) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_128
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 129 - ((7241253/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_129).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_130 : ((6391589/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 130, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 130, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 129, cos1215o2c k) + cos1215o2c 130 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 129) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_129
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 130 - ((-3524581/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_130).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_131 : ((121152297/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 131, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 131, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 130, cos1215o2c k) + cos1215o2c 131 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 130) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_130
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 131 - ((-6678483/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_131).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_132 : ((64589947/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 132, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 132, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 131, cos1215o2c k) + cos1215o2c 132 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 131) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_131
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 132 - ((8028597/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_132).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_133 : ((33517903/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 133, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 133, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 132, cos1215o2c k) + cos1215o2c 133 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 132) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_132
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 133 - ((2446359/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_133).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_134 : ((124674951/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 134, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 134, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 133, cos1215o2c k) + cos1215o2c 134 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 133) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_133
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 134 - ((-9395661/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_134).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_135 : ((61571109/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 135, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 135, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 134, cos1215o2c k) + cos1215o2c 135 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 134) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_134
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 135 - ((-1531733/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_135).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_136 : ((33278239/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 136, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 136, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 135, cos1215o2c k) + cos1215o2c 136 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 135) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_135
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 136 - ((4985869/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_136).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_137 : ((25961109/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 137, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 137, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 136, cos1215o2c k) + cos1215o2c 137 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 136) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_136
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 137 - ((-3306411/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_137).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_138 : ((15216423/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 138, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 138, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 137, cos1215o2c k) + cos1215o2c 138 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 137) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_137
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 138 - ((-8073161/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_138).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_139 : ((129906573/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 139, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 139, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 138, cos1215o2c k) + cos1215o2c 139 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 138) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_138
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 139 - ((8176189/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_139).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_140 : ((132437779/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 140, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 140, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 139, cos1215o2c k) + cos1215o2c 140 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 139) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_139
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 140 - ((1266103/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_140).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_141 : ((3828891/312500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 141, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 141, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 140, cos1215o2c k) + cos1215o2c 141 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 140) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_140
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 141 - ((-9912267/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_141).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_142 : ((31941059/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 142, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 142, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 141, cos1215o2c k) + cos1215o2c 142 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 141) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_141
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 142 - ((1310181/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_142).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_143 : ((16644917/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 143, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 143, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 142, cos1215o2c k) + cos1215o2c 143 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 142) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_142
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 143 - ((53961/100000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_143).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_144 : ((123199721/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 144, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 144, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 143, cos1215o2c k) + cos1215o2c 144 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 143) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_143
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 144 - ((-1991723/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_144).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_145 : ((127250523/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 145, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 145, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 144, cos1215o2c k) + cos1215o2c 145 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 144) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_144
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 145 - ((2025901/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_145).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_146 : ((133031501/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 146, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 146, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 145, cos1215o2c k) + cos1215o2c 146 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 145) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_145
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 146 - ((2890989/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_146).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_147 : ((61521717/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 147, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 147, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 146, cos1215o2c k) + cos1215o2c 147 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 146) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_146
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 147 - ((-9987067/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_147).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_148 : ((25641657/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 148, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 148, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 147, cos1215o2c k) + cos1215o2c 148 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 147) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_147
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 148 - ((5165851/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_148).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_149 : ((26432279/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 149, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 149, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 148, cos1215o2c k) + cos1215o2c 149 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 148) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_148
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 149 - ((395411/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_149).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_150 : ((122452669/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 150, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 150, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 149, cos1215o2c k) + cos1215o2c 150 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 149) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_149
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 150 - ((-4853863/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_150).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_151 : ((130396533/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 151, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 151, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 150, cos1215o2c k) + cos1215o2c 151 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 150) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_150
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 151 - ((248277/312500 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_151).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_152 : ((129897451/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 152, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 152, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 151, cos1215o2c k) + cos1215o2c 152 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 151) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_151
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 152 - ((-249041/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_152).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_153 : ((61388729/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 153, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 153, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 152, cos1215o2c k) + cos1215o2c 153 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 152) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_152
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 153 - ((-7118993/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_153).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_154 : ((132769431/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 154, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 154, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 153, cos1215o2c k) + cos1215o2c 154 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 153) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_153
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 154 - ((9992973/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_154).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_155 : ((7875281/625000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 155, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 155, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 154, cos1215o2c k) + cos1215o2c 155 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 154) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_154
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 155 - ((-1352787/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_155).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_156 : ((125780273/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 156, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 156, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 155, cos1215o2c k) + cos1215o2c 156 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 155) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_155
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 156 - ((-223223/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_156).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_157 : ((3317171/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 157, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 157, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 156, cos1215o2c k) + cos1215o2c 157 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 156) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_156
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 157 - ((6907567/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_157).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_158 : ((12272879/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 158, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 158, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 157, cos1215o2c k) + cos1215o2c 158 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 157) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_157
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 158 - ((-199141/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_158).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_159 : ((13098943/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 159, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 159, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 158, cos1215o2c k) + cos1215o2c 159 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 158) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_158
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 159 - ((206541/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_159).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_160 : ((127984777/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 160, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 160, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 159, cos1215o2c k) + cos1215o2c 160 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 159) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_159
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 160 - ((-3003653/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_160).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_161 : ((124664367/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 161, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 161, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 160, cos1215o2c k) + cos1215o2c 161 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 160) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_160
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 161 - ((-331941/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_161).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_162 : ((132846141/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 162, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 162, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 161, cos1215o2c k) + cos1215o2c 162 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 161) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_161
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 162 - ((4091387/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_162).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_163 : ((6142317/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 163, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 163, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 162, cos1215o2c k) + cos1215o2c 163 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 162) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_162
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 163 - ((-9998801/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_163).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_164 : ((65662893/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 164, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 164, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 163, cos1215o2c k) + cos1215o2c 164 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 163) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_163
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 164 - ((4240223/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_164).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_165 : ((126877381/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 165, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 165, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 164, cos1215o2c k) + cos1215o2c 165 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 164) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_164
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 165 - ((-889481/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_165).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_166 : ((12619471/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 166, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 166, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 165, cos1215o2c k) + cos1215o2c 166 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 165) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_165
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 166 - ((-681671/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_166).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_167 : ((65817427/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 167, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 167, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 166, cos1215o2c k) + cos1215o2c 167 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 166) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_166
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 167 - ((680143/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_167).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_168 : ((30726871/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 168, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 168, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 167, cos1215o2c k) + cos1215o2c 168 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 167) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_167
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 168 - ((-872637/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_168).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_169 : ((132895711/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 169, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 169, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 168, cos1215o2c k) + cos1215o2c 169 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 168) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_168
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 169 - ((9989227/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_169).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_170 : ((30917201/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 170, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 170, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 169, cos1215o2c k) + cos1215o2c 170 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 169) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_169
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 170 - ((-9225907/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_170).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_171 : ((8156763/625000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 171, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 171, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 170, cos1215o2c k) + cos1215o2c 171 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 170) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_170
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 171 - ((1710101/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_171).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_172 : ((6352687/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 172, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 172, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 171, cos1215o2c k) + cos1215o2c 172 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 171) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_171
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 172 - ((-863367/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_172).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_173 : ((63388701/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 173, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 173, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 172, cos1215o2c k) + cos1215o2c 173 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 172) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_172
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 173 - ((-137669/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_173).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_174 : ((26110831/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 174, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 174, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 173, cos1215o2c k) + cos1215o2c 174 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 173) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_173
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 174 - ((3777753/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_174).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_175 : ((123905349/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 175, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 175, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 174, cos1215o2c k) + cos1215o2c 175 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 174) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_174
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 175 - ((-3323903/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_175).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_176 : ((132564327/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 176, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 176, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 175, cos1215o2c k) + cos1215o2c 176 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 175) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_175
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 176 - ((4329989/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_176).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_177 : ((30702887/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 177, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 177, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 176, cos1215o2c k) + cos1215o2c 177 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 176) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_176
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 177 - ((-9751779/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_177).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_178 : ((5311757/400000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 178, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 178, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 177, cos1215o2c k) + cos1215o2c 178 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 177) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_177
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 178 - ((9983377/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_178).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_179 : ((3853091/312500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 179, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 179, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 178, cos1215o2c k) + cos1215o2c 179 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 178) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_178
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 179 - ((-9494013/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_179).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_180 : ((5270337/400000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 180, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 180, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 179, cos1215o2c k) + cos1215o2c 180 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 179) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_179
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 180 - ((8460513/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_180).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_181 : ((124693027/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 181, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 181, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 180, cos1215o2c k) + cos1215o2c 181 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 180) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_180
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 181 - ((-3532199/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_181).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_182 : ((65081807/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 182, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 182, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 181, cos1215o2c k) + cos1215o2c 182 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 181) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_181
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 182 - ((5471587/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_182).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_183 : ((31586109/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 183, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 183, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 182, cos1215o2c k) + cos1215o2c 183 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 182) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_182
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 183 - ((-1909089/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_183).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_184 : ((64276149/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 184, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 184, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 183, cos1215o2c k) + cos1215o2c 184 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 183) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_183
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 184 - ((1104431/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_184).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_185 : ((127835861/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 185, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 185, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 184, cos1215o2c k) + cos1215o2c 185 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 184) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_184
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 185 - ((-715437/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_185).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_186 : ((63609059/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 186, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 186, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 185, cos1215o2c k) + cos1215o2c 186 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 185) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_185
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 186 - ((-616743/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_186).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_187 : ((32245791/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 187, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 187, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 186, cos1215o2c k) + cos1215o2c 187 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 186) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_186
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 187 - ((883023/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_187).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_188 : ((63128907/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 188, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 188, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 187, cos1215o2c k) + cos1215o2c 188 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 187) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_187
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 188 - ((-54487/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_188).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_189 : ((8109571/625000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 189, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 189, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 188, cos1215o2c k) + cos1215o2c 189 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 188) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_188
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 189 - ((1748161/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_189).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_190 : ((125662087/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 190, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 190, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 189, cos1215o2c k) + cos1215o2c 190 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 189) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_189
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 190 - ((-4090049/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_190).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_191 : ((3254477/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 191, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 191, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 190, cos1215o2c k) + cos1215o2c 191 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 190) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_190
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 191 - ((4517993/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_191).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_192 : ((125388277/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 192, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 192, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 191, cos1215o2c k) + cos1215o2c 192 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 191) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_191
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 192 - ((-4789803/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_192).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_193 : ((26060333/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 193, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 193, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 192, cos1215o2c k) + cos1215o2c 193 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 192) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_192
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 193 - ((1228597/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_193).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_194 : ((125403989/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 194, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 194, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 193, cos1215o2c k) + cos1215o2c 194 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 193) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_193
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 194 - ((-1224169/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_194).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_195 : ((32535061/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 195, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 195, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 194, cos1215o2c k) + cos1215o2c 195 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 194) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_194
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 195 - ((947451/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_195).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_196 : ((7856601/625000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 196, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 196, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 195, cos1215o2c k) + cos1215o2c 196 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 195) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_195
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 196 - ((-1108407/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_196).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_197 : ((25937009/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 197, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 197, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 196, cos1215o2c k) + cos1215o2c 197 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 196) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_196
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 197 - ((3980429/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_197).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_198 : ((25262779/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 198, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 198, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 197, cos1215o2c k) + cos1215o2c 198 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 197) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_197
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 198 - ((-67403/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_198).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_199 : ((128908967/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 199, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 199, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 198, cos1215o2c k) + cos1215o2c 199 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 198) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_198
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 199 - ((324509/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_199).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_200 : ((127254431/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 200, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 200, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 199, cos1215o2c k) + cos1215o2c 200 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 199) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_199
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 200 - ((-51673/312500 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_200).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_201 : ((12779807/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 201, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 201, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 200, cos1215o2c k) + cos1215o2c 201 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 200) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_200
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 201 - ((544639/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_201).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_202 : ((128519057/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 202, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 202, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 201, cos1215o2c k) + cos1215o2c 202 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 201) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_201
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 202 - ((721987/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_202).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_203 : ((126395947/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 203, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 203, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 202, cos1215o2c k) + cos1215o2c 203 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 202) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_202
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 203 - ((-212211/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_203).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_204 : ((130012729/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 204, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 204, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 203, cos1215o2c k) + cos1215o2c 204 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 203) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_203
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 204 - ((1808891/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_204).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_205 : ((31215251/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 205, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 205, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 204, cos1215o2c k) + cos1215o2c 205 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 204) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_204
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 205 - ((-206029/400000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_205).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_206 : ((65751171/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 206, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 206, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 205, cos1215o2c k) + cos1215o2c 206 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 205) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_205
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 206 - ((3321169/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_206).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_207 : ((123508029/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 207, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 207, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 206, cos1215o2c k) + cos1215o2c 207 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 206) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_206
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 207 - ((-7993313/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_207).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_208 : ((13259357/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 208, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 208, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 207, cos1215o2c k) + cos1215o2c 208 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 207) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_207
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 208 - ((9086541/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_208).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_209 : ((122797597/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 209, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 209, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 208, cos1215o2c k) + cos1215o2c 209 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 208) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_208
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 209 - ((-9794973/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_209).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_210 : ((66394503/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 210, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 210, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 209, cos1215o2c k) + cos1215o2c 210 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 209) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_209
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 210 - ((9992409/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_210).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_211 : ((7701171/625000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 211, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 211, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 210, cos1215o2c k) + cos1215o2c 211 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 210) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_210
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 211 - ((-956927/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_211).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_212 : ((26333963/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 212, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 212, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 211, cos1215o2c k) + cos1215o2c 212 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 211) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_211
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 212 - ((8452079/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_212).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_213 : ((125043483/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 213, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 213, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 212, cos1215o2c k) + cos1215o2c 213 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 212) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_212
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 213 - ((-1656333/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_213).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_214 : ((129193661/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 214, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 214, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 213, cos1215o2c k) + cos1215o2c 214 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 213) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_213
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 214 - ((2075589/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_214).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_215 : ((32002249/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 215, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 215, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 214, cos1215o2c k) + cos1215o2c 215 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 214) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_214
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 215 - ((-236733/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_215).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_216 : ((62991523/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 216, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 216, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 215, cos1215o2c k) + cos1215o2c 216 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 215) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_215
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 216 - ((-40499/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_216).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_217 : ((131119253/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 217, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 217, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 216, cos1215o2c k) + cos1215o2c 217 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 216) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_216
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 217 - ((5137207/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_217).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_218 : ((61680051/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 218, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 218, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 217, cos1215o2c k) + cos1215o2c 218 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 217) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_217
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 218 - ((-7758151/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_218).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_219 : ((132846591/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 219, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 219, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 218, cos1215o2c k) + cos1215o2c 219 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 218) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_218
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 219 - ((9487489/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_219).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_220 : ((122859317/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 220, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 220, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 219, cos1215o2c k) + cos1215o2c 220 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 219) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_219
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 220 - ((-4993137/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_220).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_221 : ((26382137/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 221, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 221, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 220, cos1215o2c k) + cos1215o2c 221 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 220) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_220
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 221 - ((565773/625000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_221).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_222 : ((25043787/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 222, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 222, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 221, cos1215o2c k) + cos1215o2c 222 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 221) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_221
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 222 - ((-26763/40000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_222).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_223 : ((128379911/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 223, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 223, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 222, cos1215o2c k) + cos1215o2c 223 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 222) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_222
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 223 - ((395247/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_223).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_224 : ((129394523/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 224, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 224, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 223, cos1215o2c k) + cos1215o2c 224 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 223) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_223
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 224 - ((253903/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_224).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_225 : ((124275501/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 225, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 225, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 224, cos1215o2c k) + cos1215o2c 225 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 224) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_224
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 225 - ((-2559011/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_225).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_226 : ((26521317/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 226, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 226, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 225, cos1215o2c k) + cos1215o2c 226 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 225) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_225
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 226 - ((2083021/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_226).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_227 : ((122685441/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 227, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 227, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 226, cos1215o2c k) + cos1215o2c 227 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 226) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_226
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 227 - ((-620009/625000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_227).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_228 : ((132095859/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 228, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 228, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 227, cos1215o2c k) + cos1215o2c 228 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 227) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_227
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 228 - ((4705709/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_228).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_229 : ((62664697/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 229, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 229, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 228, cos1215o2c k) + cos1215o2c 229 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 228) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_228
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 229 - ((-1353093/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_229).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_230 : ((127788187/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 230, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 230, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 229, cos1215o2c k) + cos1215o2c 230 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 229) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_229
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 230 - ((2459793/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_230).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_231 : ((130333677/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 231, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 231, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 230, cos1215o2c k) + cos1215o2c 231 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 230) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_230
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 231 - ((254649/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_231).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_232 : ((24667217/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 232, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 232, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 231, cos1215o2c k) + cos1215o2c 232 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 231) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_231
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 232 - ((-437287/625000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_232).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_233 : ((132980221/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 233, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 233, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 232, cos1215o2c k) + cos1215o2c 233 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 232) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_232
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 233 - ((602821/625000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_233).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_234 : ((123348617/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 234, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 234, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 233, cos1215o2c k) + cos1215o2c 234 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 233) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_233
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 234 - ((-2407651/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_234).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_235 : ((130143313/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 235, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 235, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 234, cos1215o2c k) + cos1215o2c 235 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 234) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_234
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 235 - ((424731/625000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_235).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_236 : ((6415039/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 236, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 236, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 235, cos1215o2c k) + cos1215o2c 236 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 235) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_235
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 236 - ((-1841533/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_236).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_237 : ((124519271/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 237, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 237, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 236, cos1215o2c k) + cos1215o2c 237 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 236) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_236
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 237 - ((-3780509/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_237).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_238 : ((132775057/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 238, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 238, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 237, cos1215o2c k) + cos1215o2c 238 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 237) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_237
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 238 - ((4128393/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_238).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_239 : ((122774181/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 239, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 239, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 238, cos1215o2c k) + cos1215o2c 239 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 238) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_238
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 239 - ((-2499969/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_239).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_240 : ((131026251/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 240, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 240, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 239, cos1215o2c k) + cos1215o2c 240 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 239) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_239
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 240 - ((825307/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_240).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_241 : ((127548053/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 241, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 241, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 240, cos1215o2c k) + cos1215o2c 241 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 240) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_240
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 241 - ((-1738599/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_241).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_242 : ((62435443/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 242, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 242, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 241, cos1215o2c k) + cos1215o2c 242 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 241) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_241
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 242 - ((-2676167/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_242).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_243 : ((26549743/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 243, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 243, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 242, cos1215o2c k) + cos1215o2c 243 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 242) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_242
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 243 - ((7878829/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_243).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_244 : ((122749113/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 244, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 244, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 243, cos1215o2c k) + cos1215o2c 244 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 243) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_243
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 244 - ((-4999301/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_244).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_245 : ((26153543/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 245, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 245, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 244, cos1215o2c k) + cos1215o2c 245 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 244) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_244
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 245 - ((4009801/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_245).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_246 : ((64080873/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 246, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 246, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 245, cos1215o2c k) + cos1215o2c 246 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 245) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_245
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 246 - ((-2604969/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_246).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_247 : ((62071061/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 247, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 247, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 246, cos1215o2c k) + cos1215o2c 247 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 246) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_246
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 247 - ((-62791/156250 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_247).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_248 : ((133055913/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 248, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 248, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 247, cos1215o2c k) + cos1215o2c 248 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 247) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_247
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 248 - ((8914791/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_248).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_249 : ((61655451/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 249, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 249, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 248, cos1215o2c k) + cos1215o2c 249 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 248) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_248
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 249 - ((-9744011/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_249).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_250 : ((2019699/156250 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 250, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 250, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 249, cos1215o2c k) + cos1215o2c 250 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 249) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_249
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 250 - ((2975417/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_250).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_251 : ((8128109/625000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 251, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 251, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 250, cos1215o2c k) + cos1215o2c 251 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 250) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_250
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 251 - ((98751/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_251).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_252 : ((24567817/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 252, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 252, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 251, cos1215o2c k) + cos1215o2c 252 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 251) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_251
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 252 - ((-7209659/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_252).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_253 : ((83021/6250 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 253, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 253, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 252, cos1215o2c k) + cos1215o2c 253 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 252) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_252
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 253 - ((1999103/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_253).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_254 : ((978772/78125 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 254, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 254, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 253, cos1215o2c k) + cos1215o2c 254 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 253) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_253
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 254 - ((-943723/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_254).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_255 : ((126290879/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 255, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 255, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 254, cos1215o2c k) + cos1215o2c 255 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 254) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_254
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 255 - ((1009063/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_255).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_256 : ((66221651/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 256, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 256, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 255, cos1215o2c k) + cos1215o2c 256 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 255) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_255
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 256 - ((6153423/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_256).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_257 : ((122532997/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 257, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 257, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 256, cos1215o2c k) + cos1215o2c 257 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 256) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_256
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 257 - ((-1981861/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_257).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_258 : ((130507437/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 258, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 258, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 257, cos1215o2c k) + cos1215o2c 258 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 257) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_257
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 258 - ((99693/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_258).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_259 : ((129192903/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 259, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 259, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 258, cos1215o2c k) + cos1215o2c 259 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 258) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_258
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 259 - ((-656767/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_259).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_260 : ((3074787/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 260, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 260, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 259, cos1215o2c k) + cos1215o2c 260 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 259) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_259
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 260 - ((-6200423/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_260).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_261 : ((132947749/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 261, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 261, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 260, cos1215o2c k) + cos1215o2c 261 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 260) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_260
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 261 - ((9957269/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_261).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_262 : ((15683527/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 262, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 262, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 261, cos1215o2c k) + cos1215o2c 262 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 261) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_261
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 262 - ((-7478533/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_262).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_263 : ((62821109/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 263, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 263, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 262, cos1215o2c k) + cos1215o2c 263 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 262) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_262
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 263 - ((87501/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_263).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_264 : ((132942901/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 264, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 264, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 263, cos1215o2c k) + cos1215o2c 264 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 263) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_263
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 264 - ((7301683/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_264).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_265 : ((61492367/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 265, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 265, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 264, cos1215o2c k) + cos1215o2c 265 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 264) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_264
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 265 - ((-9957167/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_265).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_266 : ((25766557/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 266, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 266, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 265, cos1215o2c k) + cos1215o2c 266 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 265) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_265
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 266 - ((5849051/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_266).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_267 : ((16397831/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 267, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 267, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 266, cos1215o2c k) + cos1215o2c 267 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 266) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_266
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 267 - ((2350863/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_267).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_268 : ((7639631/625000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 268, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 268, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 267, cos1215o2c k) + cos1215o2c 268 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 267) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_267
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 268 - ((-279611/312500 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_268).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_269 : ((65689897/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 269, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 269, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 268, cos1215o2c k) + cos1215o2c 269 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 268) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_268
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 269 - ((4573349/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_269).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_270 : ((25747527/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 270, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 270, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 269, cos1215o2c k) + cos1215o2c 270 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 269) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_269
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 270 - ((-2641159/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_270).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_271 : ((12285781/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 271, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 271, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 270, cos1215o2c k) + cos1215o2c 271 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 270) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_270
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 271 - ((-235153/400000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_271).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_272 : ((132849473/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 272, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 272, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 271, cos1215o2c k) + cos1215o2c 272 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 271) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_271
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 272 - ((9992663/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_272).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_273 : ((6321519/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 273, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 273, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 272, cos1215o2c k) + cos1215o2c 273 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 272) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_272
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 273 - ((-6418093/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_273).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_274 : ((124213191/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 274, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 274, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 273, cos1215o2c k) + cos1215o2c 274 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 273) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_273
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 274 - ((-2216189/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_274).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_275 : ((133348003/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 275, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 275, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 274, cos1215o2c k) + cos1215o2c 275 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 274) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_274
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 275 - ((2283953/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_275).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_276 : ((31164349/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 276, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 276, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 275, cos1215o2c k) + cos1215o2c 276 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 275) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_275
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 276 - ((-8689607/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_276).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_277 : ((3929399/312500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 277, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 277, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 276, cos1215o2c k) + cos1215o2c 277 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 276) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_276
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 277 - ((271093/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_277).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_278 : ((133211209/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 278, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 278, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 277, cos1215o2c k) + cos1215o2c 278 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 277) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_277
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 278 - ((7471441/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_278).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_279 : ((123481033/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 279, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 279, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 278, cos1215o2c k) + cos1215o2c 279 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 278) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_278
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 279 - ((-1216147/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_279).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_280 : ((127091677/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 280, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 280, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 279, cos1215o2c k) + cos1215o2c 280 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 279) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_279
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 280 - ((902911/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_280).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_281 : ((26557861/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 281, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 281, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 280, cos1215o2c k) + cos1215o2c 281 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 280) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_280
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 281 - ((1424657/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_281).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_282 : ((3069753/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 282, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 282, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 281, cos1215o2c k) + cos1215o2c 282 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 281) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_281
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 282 - ((-1999637/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_282).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_283 : ((25621179/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 283, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 283, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 282, cos1215o2c k) + cos1215o2c 283 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 282) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_282
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 283 - ((212671/400000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_283).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_284 : ((132347247/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 284, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 284, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 283, cos1215o2c k) + cos1215o2c 284 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 283) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_283
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 284 - ((265147/625000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_284).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_285 : ((122426011/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 285, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 285, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 284, cos1215o2c k) + cos1215o2c 285 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 284) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_284
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 285 - ((-2480059/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_285).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_286 : ((128739979/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 286, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 286, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 285, cos1215o2c k) + cos1215o2c 286 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 285) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_285
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 286 - ((789371/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_286).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_287 : ((132052087/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 287, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 287, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 286, cos1215o2c k) + cos1215o2c 287 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 286) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_286
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 287 - ((828277/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_287).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_288 : ((15282437/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 288, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 288, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 287, cos1215o2c k) + cos1215o2c 288 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 287) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_287
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 288 - ((-9791591/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_288).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_289 : ((128997223/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 289, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 289, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 288, cos1215o2c k) + cos1215o2c 289 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 288) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_288
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 289 - ((6738727/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_289).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_290 : ((65993221/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 290, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 290, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 289, cos1215o2c k) + cos1215o2c 290 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 289) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_289
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 290 - ((2990219/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_290).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_291 : ((122219391/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 291, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 291, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 290, cos1215o2c k) + cos1215o2c 291 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 290) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_290
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 291 - ((-9766051/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_291).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_292 : ((25777457/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 292, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 292, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 291, cos1215o2c k) + cos1215o2c 292 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 291) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_291
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 292 - ((3334447/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_292).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_293 : ((211473/16000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 293, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 293, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 292, cos1215o2c k) + cos1215o2c 293 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 292) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_292
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 293 - ((164217/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_293).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_294 : ((30576103/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 294, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 294, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 293, cos1215o2c k) + cos1215o2c 294 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 293) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_293
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 294 - ((-9865213/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_294).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_295 : ((128406121/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 295, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 295, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 294, cos1215o2c k) + cos1215o2c 295 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 294) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_294
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 295 - ((6102709/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_295).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_296 : ((66283957/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 296, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 296, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 295, cos1215o2c k) + cos1215o2c 296 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 295) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_295
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 296 - ((4162793/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_296).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_297 : ((30644701/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 297, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 297, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 296, cos1215o2c k) + cos1215o2c 297 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 296) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_296
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 297 - ((-998811/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_297).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_298 : ((31886571/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 298, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 298, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 297, cos1215o2c k) + cos1215o2c 298 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 297) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_297
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 298 - ((31053/62500 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_298).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_299 : ((133079311/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 299, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 299, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 298, cos1215o2c k) + cos1215o2c 299 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 298) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_298
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 299 - ((5534027/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_299).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_300 : ((123161219/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 300, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 300, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 299, cos1215o2c k) + cos1215o2c 300 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 299) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_299
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 300 - ((-2479273/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_300).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_301 : ((31581177/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 301, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 301, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 300, cos1215o2c k) + cos1215o2c 301 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 300) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_300
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 301 - ((3164489/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_301).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_302 : ((133529609/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 302, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 302, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 301, cos1215o2c k) + cos1215o2c 302 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 301) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_301
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 302 - ((7205901/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_302).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_303 : ((3104879/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 303, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 303, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 302, cos1215o2c k) + cos1215o2c 303 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 302) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_302
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 303 - ((-9333449/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_303).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_304 : ((4993221/400000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 304, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 304, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 303, cos1215o2c k) + cos1215o2c 304 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 303) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_303
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 304 - ((127273/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_304).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_305 : ((26732531/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 305, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 305, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 304, cos1215o2c k) + cos1215o2c 305 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 304) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_304
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 305 - ((883313/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_305).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_306 : ((31448259/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 306, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 306, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 305, cos1215o2c k) + cos1215o2c 306 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 305) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_305
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 306 - ((-7868619/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_306).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_307 : ((7705041/625000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 307, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 307, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 306, cos1215o2c k) + cos1215o2c 307 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 306) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_306
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 307 - ((-125569/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_307).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_308 : ((133165961/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 308, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 308, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 307, cos1215o2c k) + cos1215o2c 308 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 307) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_307
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 308 - ((1977261/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_308).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_309 : ((127943607/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 309, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 309, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 308, cos1215o2c k) + cos1215o2c 309 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 308) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_308
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 309 - ((-2610677/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_309).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_310 : ((2441119/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 310, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 310, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 309, cos1215o2c k) + cos1215o2c 310 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 309) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_309
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 310 - ((-5886657/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_310).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_311 : ((131759641/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 311, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 311, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 310, cos1215o2c k) + cos1215o2c 311 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 310) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_310
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 311 - ((9704691/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_311).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_312 : ((13040509/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 312, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 312, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 311, cos1215o2c k) + cos1215o2c 312 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 311) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_311
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 312 - ((-1353551/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_312).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_313 : ((3802239/312500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 313, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 313, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 312, cos1215o2c k) + cos1215o2c 313 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 312) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_312
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 313 - ((-4366221/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_313).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_314 : ((64676189/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 314, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 314, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 313, cos1215o2c k) + cos1215o2c 314 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 313) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_313
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 314 - ((768173/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_314).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_315 : ((66314539/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 315, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 315, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 314, cos1215o2c k) + cos1215o2c 315 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 314) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_314
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 315 - ((32777/100000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_315).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_316 : ((766439/62500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 316, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 316, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 315, cos1215o2c k) + cos1215o2c 316 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 315) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_315
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 316 - ((-4998919/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_316).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_317 : ((63119869/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 317, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 317, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 316, cos1215o2c k) + cos1215o2c 317 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 316) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_316
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 317 - ((1805249/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_317).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_318 : ((66904721/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 318, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 318, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 317, cos1215o2c k) + cos1215o2c 318 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 317) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_317
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 318 - ((473169/625000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_318).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_319 : ((15642641/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 319, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 319, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 318, cos1215o2c k) + cos1215o2c 319 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 318) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_318
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 319 - ((-4333657/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_319).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_320 : ((24647111/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 320, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 320, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 319, cos1215o2c k) + cos1215o2c 320 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 319) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_319
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 320 - ((-1904573/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_320).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_321 : ((133146111/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 321, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 321, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 320, cos1215o2c k) + cos1215o2c 321 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 320) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_320
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 321 - ((2477889/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_321).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_322 : ((25755727/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 322, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 322, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 321, cos1215o2c k) + cos1215o2c 322 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 321) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_321
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 322 - ((-1091619/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_322).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_323 : ((60781243/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 323, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 323, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 322, cos1215o2c k) + cos1215o2c 323 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 322) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_322
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 323 - ((-7215149/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_323).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_324 : ((5213707/400000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 324, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 324, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 323, cos1215o2c k) + cos1215o2c 324 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 323) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_323
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 324 - ((8781189/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_324).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_325 : ((33076221/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 325, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 325, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 324, cos1215o2c k) + cos1215o2c 325 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 324) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_324
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 325 - ((1963209/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_325).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_326 : ((122351827/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 326, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 326, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 325, cos1215o2c k) + cos1215o2c 326 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 325) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_325
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 326 - ((-9952057/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_326).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_327 : ((126132497/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 327, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 327, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 326, cos1215o2c k) + cos1215o2c 327 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 326) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_326
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 327 - ((378167/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_327).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_328 : ((4186161/312500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 328, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 328, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 327, cos1215o2c k) + cos1215o2c 328 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 327) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_327
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 328 - ((1565131/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_328).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_329 : ((31454751/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 329, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 329, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 328, cos1215o2c k) + cos1215o2c 329 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 328) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_328
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 329 - ((-2034287/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_329).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_330 : ((61206843/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 330, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 330, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 329, cos1215o2c k) + cos1215o2c 330 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 329) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_329
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 330 - ((-1702159/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_330).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_331 : ((26476131/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 331, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 331, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 330, cos1215o2c k) + cos1215o2c 331 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 330) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_330
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 331 - ((9967969/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_331).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_332 : ((32643089/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 332, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 332, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 331, cos1215o2c k) + cos1215o2c 332 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 331) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_331
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 332 - ((-1807299/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_332).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_333 : ((12151529/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 333, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 333, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 332, cos1215o2c k) + cos1215o2c 333 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 332) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_332
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 333 - ((-4528033/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_333).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_334 : ((63935127/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 334, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 334, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 333, cos1215o2c k) + cos1215o2c 334 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 333) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_333
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 334 - ((1588991/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_334).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_335 : ((133814143/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 335, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 335, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 334, cos1215o2c k) + cos1215o2c 335 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 334) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_334
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 335 - ((5944889/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_335).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_336 : ((124589777/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 336, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 336, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 335, cos1215o2c k) + cos1215o2c 336 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 335) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_335
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 336 - ((-4611683/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_336).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_337 : ((122974477/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 337, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 337, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 336, cos1215o2c k) + cos1215o2c 337 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 336) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_336
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 337 - ((-16143/100000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_337).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_338 : ((132951023/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 338, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 338, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 337, cos1215o2c k) + cos1215o2c 338 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 337) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_337
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 338 - ((4988773/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_338).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_339 : ((130081237/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 339, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 339, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 338, cos1215o2c k) + cos1215o2c 339 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 338) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_338
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 339 - ((-1434393/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_339).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_340 : ((121350653/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 340, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 340, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 339, cos1215o2c k) + cos1215o2c 340 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 339) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_339
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 340 - ((-545599/625000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_340).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_341 : ((6398253/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 341, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 341, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 340, cos1215o2c k) + cos1215o2c 341 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 340) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_340
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 341 - ((6615407/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_341).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_342 : ((133934241/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 342, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 342, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 341, cos1215o2c k) + cos1215o2c 342 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 341) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_341
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 342 - ((5970181/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_342).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_343 : ((1951131/156250 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 343, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 343, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 342, cos1215o2c k) + cos1215o2c 343 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 342) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_342
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 343 - ((-9060857/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_343).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_344 : ((61251551/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 344, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 344, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 343, cos1215o2c k) + cos1215o2c 344 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 343) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_343
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 344 - ((-1184141/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_344).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_345 : ((66245659/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 345, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 345, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 344, cos1215o2c k) + cos1215o2c 345 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 344) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_344
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 345 - ((312163/312500 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_345).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_346 : ((32771133/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 346, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 346, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 345, cos1215o2c k) + cos1215o2c 346 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 345) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_345
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 346 - ((-702893/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_346).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_347 : ((30400557/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 347, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 347, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 346, cos1215o2c k) + cos1215o2c 347 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 346) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_346
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 347 - ((-1185163/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_347).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_348 : ((126403387/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 348, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 348, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 347, cos1215o2c k) + cos1215o2c 348 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 347) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_347
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 348 - ((4802159/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_348).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_349 : ((33554977/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 349, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 349, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 348, cos1215o2c k) + cos1215o2c 349 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 348) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_348
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 349 - ((7817521/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_349).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_350 : ((507071/40000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 350, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 350, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 349, cos1215o2c k) + cos1215o2c 350 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 349) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_349
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 350 - ((-3725579/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_350).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_351 : ((3793451/312500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 351, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 351, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 350, cos1215o2c k) + cos1215o2c 351 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 350) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_350
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 351 - ((-2688159/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_351).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_352 : ((6528003/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 352, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 352, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 351, cos1215o2c k) + cos1215o2c 352 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 351) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_351
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 352 - ((2292657/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_352).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_353 : ((133105941/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 353, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 353, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 352, cos1215o2c k) + cos1215o2c 353 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 352) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_352
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 353 - ((2546881/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_353).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_354 : ((61582561/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 354, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 354, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 353, cos1215o2c k) + cos1215o2c 354 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 353) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_353
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 354 - ((-9939819/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_354).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_355 : ((123494811/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 355, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 355, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 354, cos1215o2c k) + cos1215o2c 355 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 354) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_354
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 355 - ((330689/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_355).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_356 : ((66673831/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 356, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 356, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 355, cos1215o2c k) + cos1215o2c 356 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 355) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_355
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 356 - ((9853851/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_356).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_357 : ((130349289/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 357, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 357, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 356, cos1215o2c k) + cos1215o2c 357 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 356) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_356
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 357 - ((-2997373/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_357).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_358 : ((121270843/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 358, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 358, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 357, cos1215o2c k) + cos1215o2c 358 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 357) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_357
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 358 - ((-4538723/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_358).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_359 : ((63276791/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 359, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 359, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 358, cos1215o2c k) + cos1215o2c 359 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 358) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_358
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 359 - ((5283739/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_359).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_360 : ((67177417/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 360, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 360, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 359, cos1215o2c k) + cos1215o2c 360 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 359) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_359
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 360 - ((1950563/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_360).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_361 : ((127249467/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 361, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 361, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 360, cos1215o2c k) + cos1215o2c 361 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 360) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_360
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 361 - ((-7104367/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_361).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_362 : ((30257797/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 362, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 362, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 361, cos1215o2c k) + cos1215o2c 362 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 361) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_361
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 362 - ((-6217279/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_362).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_363 : ((64735643/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 363, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 363, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 362, cos1215o2c k) + cos1215o2c 363 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 362) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_362
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 363 - ((4220549/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_363).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_364 : ((133958603/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 364, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 364, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 363, cos1215o2c k) + cos1215o2c 364 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 363) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_363
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 364 - ((4488317/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_364).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_365 : ((124632803/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 365, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 365, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 364, cos1215o2c k) + cos1215o2c 365 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 364) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_364
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 365 - ((-2914/3125 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_365).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_366 : ((121885031/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 366, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 366, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 365, cos1215o2c k) + cos1215o2c 366 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 365) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_365
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 366 - ((-686693/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_366).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_367 : ((26340251/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 367, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 367, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 366, cos1215o2c k) + cos1215o2c 367 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 366) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_366
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 367 - ((1227153/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_367).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_368 : ((132790231/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 368, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 368, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 367, cos1215o2c k) + cos1215o2c 368 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 367) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_367
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 368 - ((136247/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_368).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_369 : ((30698543/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 369, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 369, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 368, cos1215o2c k) + cos1215o2c 369 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 368) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_368
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 369 - ((-9995059/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_369).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_370 : ((30803021/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 370, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 370, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 369, cos1215o2c k) + cos1215o2c 370 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 369) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_369
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 370 - ((13091/312500 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_370).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_371 : ((133149819/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 371, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 371, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 370, cos1215o2c k) + cos1215o2c 371 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 370) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_370
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 371 - ((1987747/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_371).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_372 : ((131405553/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 372, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 372, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 371, cos1215o2c k) + cos1215o2c 372 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 371) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_371
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 372 - ((-871633/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_372).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_373 : ((24336031/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 373, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 373, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 372, cos1215o2c k) + cos1215o2c 373 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 372) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_372
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 373 - ((-4862199/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_373).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_374 : ((1245481/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 374, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 374, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 373, cos1215o2c k) + cos1215o2c 374 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 373) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_373
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 374 - ((573789/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_374).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_375 : ((26793327/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 375, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 375, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 374, cos1215o2c k) + cos1215o2c 375 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 374) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_374
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 375 - ((1883907/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_375).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_376 : ((32542253/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 376, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 376, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 375, cos1215o2c k) + cos1215o2c 376 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 375) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_375
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 376 - ((-3796623/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_376).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_377 : ((121087359/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 377, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 377, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 376, cos1215o2c k) + cos1215o2c 377 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 376) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_376
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 377 - ((-9080653/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_377).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_378 : ((125620803/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 378, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 378, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 377, cos1215o2c k) + cos1215o2c 378 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 377) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_377
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 378 - ((1133611/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_378).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_379 : ((26874401/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 379, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 379, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 378, cos1215o2c k) + cos1215o2c 379 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 378) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_378
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 379 - ((4376101/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_379).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_380 : ((64636849/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 380, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 380, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 379, cos1215o2c k) + cos1215o2c 380 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 379) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_379
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 380 - ((-5097307/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_380).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_381 : ((120803581/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 381, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 381, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 380, cos1215o2c k) + cos1215o2c 381 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 380) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_380
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 381 - ((-8469117/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_381).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_382 : ((126301957/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 382, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 382, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 381, cos1215o2c k) + cos1215o2c 382 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 381) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_381
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 382 - ((343711/625000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_382).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_383 : ((134556117/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 383, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 383, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 382, cos1215o2c k) + cos1215o2c 383 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 382) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_382
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 383 - ((206379/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_383).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_384 : ((128801869/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 384, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 384, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 383, cos1215o2c k) + cos1215o2c 384 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 383) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_383
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 384 - ((-179789/312500 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_384).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_385 : ((60337417/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 385, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 385, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 384, cos1215o2c k) + cos1215o2c 385 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 384) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_384
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 385 - ((-1625207/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_385).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_386 : ((25308607/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 386, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 386, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 385, cos1215o2c k) + cos1215o2c 386 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 385) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_385
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 386 - ((5869201/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_386).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_387 : ((134632679/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 387, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 387, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 386, cos1215o2c k) + cos1215o2c 387 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 386) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_386
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 387 - ((2022661/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_387).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_388 : ((32194737/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 388, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 388, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 387, cos1215o2c k) + cos1215o2c 388 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 387) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_387
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 388 - ((-5852731/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_388).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_389 : ((60314143/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 389, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 389, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 388, cos1215o2c k) + cos1215o2c 389 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 388) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_388
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 389 - ((-4074831/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_389).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_390 : ((126331549/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 390, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 390, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 389, cos1215o2c k) + cos1215o2c 390 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 389) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_389
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 390 - ((5704263/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_390).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_391 : ((13462929/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 391, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 391, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 390, cos1215o2c k) + cos1215o2c 391 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 390) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_390
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 391 - ((8298741/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_391).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_392 : ((129207953/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 392, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 392, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 391, cos1215o2c k) + cos1215o2c 392 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 391) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_391
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 392 - ((-5420337/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_392).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_393 : ((120680911/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 393, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 393, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 392, cos1215o2c k) + cos1215o2c 393 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 392) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_392
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 393 - ((-4263021/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_393).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_394 : ((125673779/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 394, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 394, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 393, cos1215o2c k) + cos1215o2c 394 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 393) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_393
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 394 - ((1248467/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_394).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_395 : ((67243373/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 395, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 395, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 394, cos1215o2c k) + cos1215o2c 395 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 394) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_394
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 395 - ((8813967/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_395).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_396 : ((8129431/625000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 396, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 396, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 395, cos1215o2c k) + cos1215o2c 396 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 395) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_395
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 396 - ((-88297/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_396).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_397 : ((15116649/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 397, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 397, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 396, cos1215o2c k) + cos1215o2c 397 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 396) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_396
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 397 - ((-142761/156250 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_397).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_398 : ((31151343/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 398, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 398, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 397, cos1215o2c k) + cos1215o2c 398 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 397) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_397
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 398 - ((183659/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_398).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_399 : ((67032741/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 399, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 399, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 398, cos1215o2c k) + cos1215o2c 399 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 398) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_398
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 399 - ((946111/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_399).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_400 : ((13130453/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 400, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 400, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 399, cos1215o2c k) + cos1215o2c 400 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 399) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_399
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 400 - ((-172497/625000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_400).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_401 : ((121557143/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 401, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 401, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 400, cos1215o2c k) + cos1215o2c 401 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 400) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_400
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 401 - ((-9746387/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_401).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_402 : ((24645529/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 402, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 402, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 401, cos1215o2c k) + cos1215o2c 402 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 401) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_401
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 402 - ((835751/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_402).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_403 : ((133170013/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 403, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 403, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 402, cos1215o2c k) + cos1215o2c 403 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 402) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_402
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 403 - ((1242921/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_403).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_404 : ((132756661/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 404, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 404, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 403, cos1215o2c k) + cos1215o2c 404 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 403) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_403
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 404 - ((-6443/156250 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_404).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_405 : ((61379747/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 405, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 405, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 404, cos1215o2c k) + cos1215o2c 405 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 404) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_404
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 405 - ((-9996167/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_405).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_406 : ((121756891/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 406, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 406, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 405, cos1215o2c k) + cos1215o2c 406 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 405) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_405
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 406 - ((-1001603/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_406).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_407 : ((131600227/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 407, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 407, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 406, cos1215o2c k) + cos1215o2c 407 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 406) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_406
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 407 - ((615271/625000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_407).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_408 : ((670689/50000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 408, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 408, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 407, cos1215o2c k) + cos1215o2c 408 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 407) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_407
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 408 - ((2538573/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_408).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_409 : ((124710263/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 409, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 409, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 408, cos1215o2c k) + cos1215o2c 409 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 408) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_408
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 409 - ((-9426537/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_409).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_410 : ((120562529/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 410, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 410, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 409, cos1215o2c k) + cos1215o2c 410 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 409) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_409
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 410 - ((-2073367/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_410).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_411 : ((25849483/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 411, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 411, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 410, cos1215o2c k) + cos1215o2c 411 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 410) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_410
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 411 - ((4342943/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_411).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_412 : ((67499663/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 412, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 412, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 411, cos1215o2c k) + cos1215o2c 412 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 411) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_411
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 412 - ((5752911/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_412).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_413 : ((127421587/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 413, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 413, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 412, cos1215o2c k) + cos1215o2c 413 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 412) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_412
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 413 - ((-7576739/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_413).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_414 : ((12015931/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 414, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 414, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 413, cos1215o2c k) + cos1215o2c 414 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 413) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_413
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 414 - ((-7261277/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_414).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_415 : ((126233881/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 415, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 415, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 414, cos1215o2c k) + cos1215o2c 415 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 414) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_414
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 415 - ((6075571/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_415).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_416 : ((33697003/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 416, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 416, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 415, cos1215o2c k) + cos1215o2c 416 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 415) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_415
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 416 - ((8555131/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_416).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_417 : ((130599529/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 417, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 417, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 416, cos1215o2c k) + cos1215o2c 417 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 416) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_416
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 417 - ((-4187483/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_417).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_418 : ((121094769/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 418, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 418, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 417, cos1215o2c k) + cos1215o2c 418 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 417) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_417
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 418 - ((-118797/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_418).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_419 : ((123052807/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 419, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 419, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 418, cos1215o2c k) + cos1215o2c 419 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 418) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_418
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 419 - ((979519/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_419).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_420 : ((66512019/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 420, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 420, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 419, cos1215o2c k) + cos1215o2c 420 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 419) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_419
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 420 - ((9972231/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_420).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_421 : ((133538403/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 421, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 421, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 420, cos1215o2c k) + cos1215o2c 421 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 420) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_420
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 421 - ((103073/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_421).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_422 : ((123700873/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 422, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 422, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 421, cos1215o2c k) + cos1215o2c 422 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 421) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_421
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 422 - ((-983653/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_422).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_423 : ((120610959/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 423, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 423, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 422, cos1215o2c k) + cos1215o2c 423 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 422) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_422
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 423 - ((-1544457/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_423).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_424 : ((129612977/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 424, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 424, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 423, cos1215o2c k) + cos1215o2c 424 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 423) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_423
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 424 - ((4501509/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_424).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_425 : ((6758797/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 425, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 425, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 424, cos1215o2c k) + cos1215o2c 425 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 424) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_424
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 425 - ((5563963/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_425).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_426 : ((127743853/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 426, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 426, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 425, cos1215o2c k) + cos1215o2c 426 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 425) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_425
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 426 - ((-7431087/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_426).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_427 : ((120038757/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 427, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 427, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 426, cos1215o2c k) + cos1215o2c 427 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 426) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_426
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 427 - ((-240753/312500 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_427).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_428 : ((31298037/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 428, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 428, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 427, cos1215o2c k) + cos1215o2c 428 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 427) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_427
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 428 - ((5154391/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_428).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_429 : ((8402869/625000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 429, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 429, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 428, cos1215o2c k) + cos1215o2c 429 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 428) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_428
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 429 - ((2313689/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_429).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_430 : ((132144171/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 430, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 430, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 429, cos1215o2c k) + cos1215o2c 430 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 429) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_429
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 430 - ((-2300733/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_430).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_431 : ((12216941/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 431, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 431, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 430, cos1215o2c k) + cos1215o2c 431 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 430) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_430
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 431 - ((-9973761/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_431).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_432 : ((12126507/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 432, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 432, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 431, cos1215o2c k) + cos1215o2c 432 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 431) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_431
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 432 - ((-45167/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_432).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_433 : ((65468337/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 433, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 433, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 432, cos1215o2c k) + cos1215o2c 433 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 432) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_432
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 433 - ((2418151/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_433).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_434 : ((135068059/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 434, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 434, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 433, cos1215o2c k) + cos1215o2c 434 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 433) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_433
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 434 - ((826477/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_434).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_435 : ((63403023/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 435, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 435, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 434, cos1215o2c k) + cos1215o2c 435 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 434) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_434
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 435 - ((-8261013/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_435).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_436 : ((119811477/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 436, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 436, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 435, cos1215o2c k) + cos1215o2c 436 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 435) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_435
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 436 - ((-6993569/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_436).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_437 : ((15699777/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 437, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 437, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 436, cos1215o2c k) + cos1215o2c 437 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 436) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_436
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 437 - ((5787739/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_437).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_438 : ((134665699/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 438, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 438, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 437, cos1215o2c k) + cos1215o2c 438 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 437) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_437
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 438 - ((9068483/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_438).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_439 : ((33048491/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 439, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 439, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 438, cos1215o2c k) + cos1215o2c 439 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 438) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_438
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 439 - ((-494147/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_439).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_440 : ((122211629/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 440, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 440, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 439, cos1215o2c k) + cos1215o2c 440 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 439) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_439
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 440 - ((-1996267/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_440).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_441 : ((60454153/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 441, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 441, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 440, cos1215o2c k) + cos1215o2c 441 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 440) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_440
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 441 - ((-1302323/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_441).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_442 : ((130382497/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 442, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 442, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 441, cos1215o2c k) + cos1215o2c 442 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 441) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_441
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 442 - ((9475191/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_442).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_443 : ((5415163/400000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 443, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 443, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 442, cos1215o2c k) + cos1215o2c 443 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 442) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_442
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 443 - ((2498789/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_443).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_444 : ((127888603/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 444, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 444, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 443, cos1215o2c k) + cos1215o2c 444 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 443) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_443
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 444 - ((-117023/156250 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_444).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_445 : ((119880811/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 445, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 445, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 444, cos1215o2c k) + cos1215o2c 445 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 444) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_444
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 445 - ((-1000849/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_445).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_446 : ((4963839/400000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 446, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 446, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 445, cos1215o2c k) + cos1215o2c 446 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 445) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_445
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 446 - ((1054041/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_446).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_447 : ((133842943/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 447, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 447, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 446, cos1215o2c k) + cos1215o2c 447 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 446) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_446
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 447 - ((76156/78125 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_447).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_448 : ((33431057/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 448, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 448, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 447, cos1215o2c k) + cos1215o2c 448 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 447) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_447
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 448 - ((-23543/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_448).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_449 : ((15491461/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 449, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 449, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 448, cos1215o2c k) + cos1215o2c 449 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 448) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_448
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 449 - ((-489577/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_449).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_450 : ((119818109/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 450, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 450, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 449, cos1215o2c k) + cos1215o2c 450 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 449) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_449
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 450 - ((-4112579/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_450).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_451 : ((3195037/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 451, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 451, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 450, cos1215o2c k) + cos1215o2c 451 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 450) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_450
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 451 - ((7984371/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_451).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_452 : ((135452833/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 452, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 452, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 451, cos1215o2c k) + cos1215o2c 452 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 451) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_451
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 452 - ((7652353/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_452).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_453 : ((130912557/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 453, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 453, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 452, cos1215o2c k) + cos1215o2c 453 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 452) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_452
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 453 - ((-1134819/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_453).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_454 : ((60598981/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 454, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 454, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 453, cos1215o2c k) + cos1215o2c 454 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 453) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_453
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 454 - ((-1942719/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_454).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_455 : ((24250983/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 455, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 455, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 454, cos1215o2c k) + cos1215o2c 455 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 454) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_454
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 455 - ((57953/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_455).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_456 : ((130987617/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 456, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 456, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 455, cos1215o2c k) + cos1215o2c 456 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 455) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_455
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 456 - ((4866851/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_456).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_457 : ((33881907/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 457, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 457, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 456, cos1215o2c k) + cos1215o2c 457 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 456) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_456
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 457 - ((4541011/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_457).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_458 : ((15996377/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 458, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 458, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 457, cos1215o2c k) + cos1215o2c 458 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 457) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_457
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 458 - ((-1888903/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_458).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_459 : ((59888867/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 459, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 459, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 458, cos1215o2c k) + cos1215o2c 459 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 458) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_458
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 459 - ((-4096141/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_459).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_460 : ((123317977/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 460, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 460, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 459, cos1215o2c k) + cos1215o2c 460 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 459) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_459
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 460 - ((3541243/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_460).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_461 : ((133256067/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 461, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 461, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 460, cos1215o2c k) + cos1215o2c 461 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 460) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_460
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 461 - ((993909/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_461).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_462 : ((134690463/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 462, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 462, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 461, cos1215o2c k) + cos1215o2c 462 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 461) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_461
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 462 - ((358849/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_462).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_463 : ((125483911/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 463, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 463, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 462, cos1215o2c k) + cos1215o2c 463 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 462) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_462
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 463 - ((-575347/625000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_463).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_464 : ((59670297/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 464, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 464, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 463, cos1215o2c k) + cos1215o2c 464 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 463) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_463
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 464 - ((-6142317/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_464).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_465 : ((31340839/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 465, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 465, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 464, cos1215o2c k) + cos1215o2c 465 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 464) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_464
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 465 - ((3011881/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_465).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_466 : ((134646367/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 466, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 466, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 465, cos1215o2c k) + cos1215o2c 466 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 465) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_465
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 466 - ((9284011/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_466).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_467 : ((133526211/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 467, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 467, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 466, cos1215o2c k) + cos1215o2c 467 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 466) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_466
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 467 - ((-279789/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_467).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_468 : ((15456459/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 468, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 468, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 467, cos1215o2c k) + cos1215o2c 468 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 467) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_467
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 468 - ((-9873539/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_468).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_469 : ((59726037/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 469, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 469, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 468, cos1215o2c k) + cos1215o2c 469 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 468) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_468
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 469 - ((-2099299/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_469).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_470 : ((63516783/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 470, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 470, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 469, cos1215o2c k) + cos1215o2c 470 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 469) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_469
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 470 - ((1895623/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_470).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_471 : ((67695833/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 471, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 471, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 470, cos1215o2c k) + cos1215o2c 471 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 470) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_470
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 471 - ((83591/100000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_471).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_472 : ((132448287/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 472, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 472, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 471, cos1215o2c k) + cos1215o2c 472 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 471) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_471
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 472 - ((-2942379/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_472).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_473 : ((7653013/625000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 473, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 473, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 472, cos1215o2c k) + cos1215o2c 473 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 472) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_472
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 473 - ((-9999079/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_473).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_474 : ((3741863/312500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 474, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 474, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 473, cos1215o2c k) + cos1215o2c 474 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 473) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_473
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 474 - ((-338449/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_474).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_475 : ((128186259/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 475, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 475, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 474, cos1215o2c k) + cos1215o2c 475 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 474) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_474
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 475 - ((8447643/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_475).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_476 : ((135749937/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 476, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 476, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 475, cos1215o2c k) + cos1215o2c 476 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 475) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_475
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 476 - ((3782339/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_476).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_477 : ((131698707/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 477, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 477, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 476, cos1215o2c k) + cos1215o2c 477 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 476) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_476
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 477 - ((-405023/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_477).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_478 : ((12176783/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 478, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 478, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 477, cos1215o2c k) + cos1215o2c 478 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 477) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_477
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 478 - ((-9929877/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_478).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_479 : ((23989901/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 479, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 479, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 478, cos1215o2c k) + cos1215o2c 479 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 478) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_478
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 479 - ((-72693/400000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_479).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_480 : ((64394027/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 480, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 480, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 479, cos1215o2c k) + cos1215o2c 480 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 479) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_479
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 480 - ((8839549/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_480).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_481 : ((33978041/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 481, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 481, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 480, cos1215o2c k) + cos1215o2c 481 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 480) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_480
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 481 - ((712511/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_481).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_482 : ((65697187/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 482, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 482, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 481, cos1215o2c k) + cos1215o2c 482 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 481) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_481
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 482 - ((-451679/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_482).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_483 : ((607581/50000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 483, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 483, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 482, cos1215o2c k) + cos1215o2c 483 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 482) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_482
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 483 - ((-4938587/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_483).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_484 : ((11994759/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 484, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 484, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 483, cos1215o2c k) + cos1215o2c 484 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 483) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_483
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 484 - ((-156761/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_484).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_485 : ((64421159/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 485, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 485, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 484, cos1215o2c k) + cos1215o2c 485 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 484) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_484
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 485 - ((555983/625000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_485).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_486 : ((33992983/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 486, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 486, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 485, cos1215o2c k) + cos1215o2c 486 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 485) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_485
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 486 - ((3565307/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_486).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_487 : ((32894389/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 487, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 487, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 486, cos1215o2c k) + cos1215o2c 487 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 486) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_486
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 487 - ((-137293/312500 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_487).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_488 : ((24332247/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 488, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 488, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 487, cos1215o2c k) + cos1215o2c 488 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 487) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_487
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 488 - ((-9915321/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_488).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_489 : ((29925703/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 489, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 489, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 488, cos1215o2c k) + cos1215o2c 489 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 488) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_488
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 489 - ((-1957423/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_489).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_490 : ((128346273/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 490, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 490, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 489, cos1215o2c k) + cos1215o2c 490 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 489) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_489
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 490 - ((8644461/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_490).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_491 : ((67958501/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 491, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 491, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 490, cos1215o2c k) + cos1215o2c 491 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 490) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_490
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 491 - ((7571729/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_491).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_492 : ((132234253/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 492, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 492, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 491, cos1215o2c k) + cos1215o2c 492 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 491) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_491
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 492 - ((-3681749/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_492).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_493 : ((122241139/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 493, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 493, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 492, cos1215o2c k) + cos1215o2c 493 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 492) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_492
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 493 - ((-4996057/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_493).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_494 : ((59642271/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 494, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 494, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 493, cos1215o2c k) + cos1215o2c 494 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 493) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_493
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 494 - ((-2955597/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_494).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_495 : ((31822609/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 495, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 495, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 494, cos1215o2c k) + cos1215o2c 495 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 494) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_494
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 495 - ((4003447/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_495).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_496 : ((135633699/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 496, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 496, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 495, cos1215o2c k) + cos1215o2c 496 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 495) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_495
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 496 - ((8344263/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_496).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_497 : ((133289929/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 497, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 497, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 496, cos1215o2c k) + cos1215o2c 497 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 496) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_496
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 497 - ((-234277/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_497).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_498 : ((15419123/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 498, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 498, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 497, cos1215o2c k) + cos1215o2c 498 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 497) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_497
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 498 - ((-1987189/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_498).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_499 : ((594321/50000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 499, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 499, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 498, cos1215o2c k) + cos1215o2c 499 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 498) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_498
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 499 - ((-560973/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_499).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_500 : ((31421391/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 500, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 500, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 499, cos1215o2c k) + cos1215o2c 500 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 499) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_499
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 500 - ((1705591/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_500).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_501 : ((26983777/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 501, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 501, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 500, cos1215o2c k) + cos1215o2c 501 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 500) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_500
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 501 - ((9234321/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_501).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_502 : ((134573701/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 502, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 502, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 501, cos1215o2c k) + cos1215o2c 502 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 501) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_501
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 502 - ((-43023/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_502).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_503 : ((125104033/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 503, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 503, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 502, cos1215o2c k) + cos1215o2c 503 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 502) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_502
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 503 - ((-2367167/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_503).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_504 : ((59362331/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 504, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 504, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 503, cos1215o2c k) + cos1215o2c 504 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 503) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_503
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 504 - ((-6378371/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_504).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_505 : ((30906809/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 505, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 505, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 504, cos1215o2c k) + cos1215o2c 505 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 504) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_504
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 505 - ((2451787/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_505).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_506 : ((133523509/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 506, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 506, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 505, cos1215o2c k) + cos1215o2c 506 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 505) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_505
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 506 - ((9897273/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_506).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_507 : ((135781719/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 507, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 507, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 506, cos1215o2c k) + cos1215o2c 507 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 506) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_506
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 507 - ((225921/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_507).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_508 : ((25507357/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 508, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 508, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 507, cos1215o2c k) + cos1215o2c 508 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 507) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_507
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 508 - ((-4121967/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_508).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_509 : ((59621673/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 509, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 509, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 508, cos1215o2c k) + cos1215o2c 509 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 508) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_508
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 509 - ((-8292439/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_509).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_510 : ((121371783/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 510, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 510, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 509, cos1215o2c k) + cos1215o2c 510 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 509) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_509
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 510 - ((2129437/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_510).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_511 : ((5249317/400000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 511, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 511, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 510, cos1215o2c k) + cos1215o2c 511 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 510) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_510
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 511 - ((4931071/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_511).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_512 : ((2132077/156250 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 512, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 512, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 511, cos1215o2c k) + cos1215o2c 512 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 511) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_511
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 512 - ((5221003/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_512).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_513 : ((26102353/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 513, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 513, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 512, cos1215o2c k) + cos1215o2c 513 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 512) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_512
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 513 - ((-5940163/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_513).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_514 : ((30204357/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 514, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 514, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 513, cos1215o2c k) + cos1215o2c 514 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 513) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_513
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 514 - ((-9693337/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_514).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_515 : ((23880819/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 515, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 515, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 514, cos1215o2c k) + cos1215o2c 515 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 514) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_514
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 515 - ((-1412333/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_515).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_516 : ((64005247/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 516, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 516, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 515, cos1215o2c k) + cos1215o2c 516 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 515) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_515
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 516 - ((8607399/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_516).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_517 : ((68008929/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 517, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 517, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 516, cos1215o2c k) + cos1215o2c 517 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 516) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_516
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 517 - ((2002091/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_517).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_518 : ((66794471/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 518, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 518, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 517, cos1215o2c k) + cos1215o2c 518 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 517) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_517
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 518 - ((-606979/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_518).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_519 : ((123706179/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 519, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 519, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 518, cos1215o2c k) + cos1215o2c 519 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 518) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_518
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 519 - ((-9881763/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_519).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_520 : ((118433297/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 520, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 520, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 519, cos1215o2c k) + cos1215o2c 520 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 519) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_519
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 520 - ((-2635941/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_520).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_521 : ((2483521/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 521, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 521, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 520, cos1215o2c k) + cos1215o2c 521 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 520) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_520
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 521 - ((5743753/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_521).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_522 : ((133963771/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 522, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 522, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 521, cos1215o2c k) + cos1215o2c 522 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 521) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_521
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 522 - ((9788721/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_522).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_523 : ((135970789/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 523, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 523, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 522, cos1215o2c k) + cos1215o2c 523 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 522) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_522
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 523 - ((1004009/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_523).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_524 : ((63893903/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 524, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 524, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 523, cos1215o2c k) + cos1215o2c 524 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 523) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_523
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 524 - ((-8181983/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_524).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_525 : ((119239337/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 525, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 525, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 524, cos1215o2c k) + cos1215o2c 525 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 524) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_524
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 525 - ((-8547469/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_525).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_526 : ((7534043/625000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 526, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 526, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 525, cos1215o2c k) + cos1215o2c 526 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 525) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_525
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 526 - ((1306351/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_526).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_527 : ((26027519/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 527, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 527, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 526, cos1215o2c k) + cos1215o2c 527 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 526) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_526
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 527 - ((9593907/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_527).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_528 : ((34154463/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 528, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 528, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 527, cos1215o2c k) + cos1215o2c 528 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 527) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_527
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 528 - ((6481257/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_528).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_529 : ((33079443/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 529, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 529, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 528, cos1215o2c k) + cos1215o2c 529 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 528) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_528
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 529 - ((-107477/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_529).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_530 : ((1528987/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 530, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 530, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 529, cos1215o2c k) + cos1215o2c 530 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 529) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_529
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 530 - ((-2499453/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_530).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_531 : ((29595041/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 531, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 531, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 530, cos1215o2c k) + cos1215o2c 531 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 530) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_530
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 531 - ((-984449/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_531).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_532 : ((125108819/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 532, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 532, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 531, cos1215o2c k) + cos1215o2c 532 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 531) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_531
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 532 - ((1345931/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_532).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_533 : ((134636329/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 533, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 533, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 532, cos1215o2c k) + cos1215o2c 533 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 532) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_532
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 533 - ((952851/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_533).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_534 : ((67935079/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 534, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 534, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 533, cos1215o2c k) + cos1215o2c 534 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 533) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_533
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 534 - ((1234829/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_534).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_535 : ((1019089/80000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 535, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 535, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 534, cos1215o2c k) + cos1215o2c 535 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 534) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_534
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 535 - ((-8483033/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_535).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_536 : ((7437559/625000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 536, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 536, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 535, cos1215o2c k) + cos1215o2c 536 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 535) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_535
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 536 - ((-8384181/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_536).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_537 : ((120375023/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 537, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 537, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 536, cos1215o2c k) + cos1215o2c 537 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 536) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_536
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 537 - ((1375079/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_537).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_538 : ((129919679/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 538, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 538, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 537, cos1215o2c k) + cos1215o2c 538 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 537) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_537
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 538 - ((1193207/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_538).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_539 : ((34175089/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 539, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 539, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 538, cos1215o2c k) + cos1215o2c 539 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 538) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_538
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 539 - ((6781677/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_539).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_540 : ((26596553/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 540, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 540, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 539, cos1215o2c k) + cos1215o2c 540 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 539) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_539
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 540 - ((-3716591/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_540).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_541 : ((6150179/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 541, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 541, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 540, cos1215o2c k) + cos1215o2c 541 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 540) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_540
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 541 - ((-1995637/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_541).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_542 : ((59038919/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 542, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 542, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 541, cos1215o2c k) + cos1215o2c 542 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 541) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_541
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 542 - ((-2462371/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_542).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_543 : ((4950537/400000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 543, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 543, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 542, cos1215o2c k) + cos1215o2c 543 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 542) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_542
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 543 - ((5686587/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_543).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_544 : ((33411851/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 544, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 544, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 543, cos1215o2c k) + cos1215o2c 544 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 543) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_543
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 544 - ((9884979/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_544).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_545 : ((68316583/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 545, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 545, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 544, cos1215o2c k) + cos1215o2c 545 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 544) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_544
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 545 - ((1493381/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_545).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_546 : ((129386787/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 546, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 546, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 545, cos1215o2c k) + cos1215o2c 546 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 545) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_545
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 546 - ((-7245379/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_546).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_547 : ((11999629/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 547, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 547, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 546, cos1215o2c k) + cos1215o2c 547 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 546) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_546
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 547 - ((-9389497/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_547).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_548 : ((59448621/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 548, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 548, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 547, cos1215o2c k) + cos1215o2c 548 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 547) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_547
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 548 - ((-17157/156250 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_548).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_549 : ((127297783/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 549, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 549, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 548, cos1215o2c k) + cos1215o2c 549 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 548) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_548
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 549 - ((8401541/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_549).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_550 : ((67956603/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 550, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 550, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 549, cos1215o2c k) + cos1215o2c 550 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 549) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_549
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 550 - ((8616423/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_550).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_551 : ((135261789/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 551, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 551, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 550, cos1215o2c k) + cos1215o2c 551 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 550) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_550
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 551 - ((-650417/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_551).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_552 : ((5042663/400000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 552, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 552, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 551, cos1215o2c k) + cos1215o2c 552 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 551) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_551
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 552 - ((-4597107/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_552).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_553 : ((59193753/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 553, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 553, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 552, cos1215o2c k) + cos1215o2c 553 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 552) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_552
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 553 - ((-7678069/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_553).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_554 : ((120589277/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 554, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 554, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 553, cos1215o2c k) + cos1215o2c 554 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 553) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_553
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 554 - ((2202771/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_554).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_555 : ((32567439/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 555, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 555, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 554, cos1215o2c k) + cos1215o2c 555 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 554) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_554
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 555 - ((9681479/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_555).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_556 : ((136939741/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 556, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 556, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 555, cos1215o2c k) + cos1215o2c 556 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 555) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_555
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 556 - ((1334197/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_556).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_557 : ((133403177/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 557, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 557, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 556, cos1215o2c k) + cos1215o2c 557 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 556) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_556
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 557 - ((-883891/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_557).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_558 : ((30868449/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 558, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 558, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 557, cos1215o2c k) + cos1215o2c 558 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 557) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_557
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 558 - ((-9928381/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_558).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_559 : ((117803113/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 559, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 559, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 558, cos1215o2c k) + cos1215o2c 559 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 558) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_558
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 559 - ((-5669683/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_559).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_560 : ((4897847/400000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 560, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 560, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 559, cos1215o2c k) + cos1215o2c 560 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 559) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_559
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 560 - ((2322031/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_560).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_561 : ((66222549/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 561, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 561, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 560, cos1215o2c k) + cos1215o2c 561 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 560) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_560
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 561 - ((9999923/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_561).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_562 : ((8573457/625000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 562, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 562, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 561, cos1215o2c k) + cos1215o2c 562 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 561) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_561
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 562 - ((2365607/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_562).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_563 : ((131634131/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 563, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 563, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 562, cos1215o2c k) + cos1215o2c 563 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 562) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_562
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 563 - ((-5540181/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_563).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_564 : ((30419427/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 564, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 564, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 563, cos1215o2c k) + cos1215o2c 564 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 563) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_563
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 564 - ((-9955423/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_564).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_565 : ((29445277/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 565, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 565, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 564, cos1215o2c k) + cos1215o2c 565 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 564) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_564
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 565 - ((-9739/25000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_565).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_566 : ((62010981/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 566, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 566, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 565, cos1215o2c k) + cos1215o2c 566 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 565) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_565
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 566 - ((3120927/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_566).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_567 : ((66933493/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 567, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 567, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 566, cos1215o2c k) + cos1215o2c 567 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 566) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_566
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 567 - ((1230753/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_567).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_568 : ((68527683/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 568, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 568, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 567, cos1215o2c k) + cos1215o2c 568 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 567) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_567
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 568 - ((159469/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_568).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_569 : ((65141061/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 569, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 569, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 568, cos1215o2c k) + cos1215o2c 569 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 568) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_568
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 569 - ((-1693061/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_569).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_570 : ((120567497/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 570, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 570, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 569, cos1215o2c k) + cos1215o2c 570 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 569) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_569
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 570 - ((-77709/80000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_570).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_571 : ((11793763/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 571, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 571, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 570, cos1215o2c k) + cos1215o2c 571 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 570) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_570
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 571 - ((-2628867/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_571).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_572 : ((125088767/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 572, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 572, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 571, cos1215o2c k) + cos1215o2c 572 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 571) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_571
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 572 - ((7152137/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_572).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_573 : ((2693557/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 573, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 573, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 572, cos1215o2c k) + cos1215o2c 573 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 572) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_572
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 573 - ((9590083/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_573).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_574 : ((136900551/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 574, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 574, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 573, cos1215o2c k) + cos1215o2c 574 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 573) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_573
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 574 - ((2223701/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_574).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_575 : ((64749237/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 575, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 575, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 574, cos1215o2c k) + cos1215o2c 575 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 574) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_574
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 575 - ((-7401077/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_575).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_576 : ((119998929/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 576, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 576, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 575, cos1215o2c k) + cos1215o2c 576 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 575) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_575
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 576 - ((-1899709/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_576).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_577 : ((11802103/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 577, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 577, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 576, cos1215o2c k) + cos1215o2c 577 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 576) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_576
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 577 - ((-1976899/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_577).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_578 : ((62776123/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 578, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 578, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 577, cos1215o2c k) + cos1215o2c 578 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 577) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_577
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 578 - ((941527/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_578).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_579 : ((5400171/400000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 579, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 579, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 578, cos1215o2c k) + cos1215o2c 579 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 578) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_578
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 579 - ((9453029/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_579).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_580 : ((136893427/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 580, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 580, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 579, cos1215o2c k) + cos1215o2c 580 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 579) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_579
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 580 - ((236269/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_580).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_581 : ((6466903/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 581, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 581, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 580, cos1215o2c k) + cos1215o2c 581 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 580) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_580
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 581 - ((-7554367/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_581).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_582 : ((5993871/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 582, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 582, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 581, cos1215o2c k) + cos1215o2c 582 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 581) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_581
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 582 - ((-236491/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_582).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_583 : ((117912673/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 583, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 583, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 582, cos1215o2c k) + cos1215o2c 583 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 582) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_582
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 583 - ((-1963747/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_583).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_584 : ((125381249/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 584, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 584, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 583, cos1215o2c k) + cos1215o2c 584 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 583) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_583
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 584 - ((933697/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_584).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_585 : ((4215541/312500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 585, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 585, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 584, cos1215o2c k) + cos1215o2c 585 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 584) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_584
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 585 - ((9517063/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_585).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_586 : ((34272573/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 586, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 586, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 585, cos1215o2c k) + cos1215o2c 586 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 585) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_585
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 586 - ((109699/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_586).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_587 : ((129814431/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 587, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 587, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 586, cos1215o2c k) + cos1215o2c 587 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 586) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_586
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 587 - ((-7274861/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_587).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_588 : ((1502463/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 588, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 588, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 587, cos1215o2c k) + cos1215o2c 588 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 587) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_587
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 588 - ((-9616391/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_588).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_589 : ((117618933/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 589, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 589, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 588, cos1215o2c k) + cos1215o2c 589 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 588) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_588
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 589 - ((-2577107/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_589).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_590 : ((62289323/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 590, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 590, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 589, cos1215o2c k) + cos1215o2c 590 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 589) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_589
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 590 - ((6960713/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_590).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_591 : ((419747/31250 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 591, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 591, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 590, cos1215o2c k) + cos1215o2c 591 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 590) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_590
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 591 - ((4870697/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_591).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_592 : ((137424199/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 592, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 592, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 591, cos1215o2c k) + cos1215o2c 592 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 591) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_591
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 592 - ((3106159/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_592).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_593 : ((65454567/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 593, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 593, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 592, cos1215o2c k) + cos1215o2c 593 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 592) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_592
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 593 - ((-1302813/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_593).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_594 : ((30259879/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 594, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 594, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 593, cos1215o2c k) + cos1215o2c 594 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 593) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_593
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 594 - ((-4934309/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_594).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_595 : ((58633853/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 595, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 595, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 594, cos1215o2c k) + cos1215o2c 595 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 594) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_594
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 595 - ((-377081/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_595).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_596 : ((15398271/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 596, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 596, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 595, cos1215o2c k) + cos1215o2c 596 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 595) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_595
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 596 - ((2959731/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_596).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_597 : ((6657613/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 597, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 597, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 596, cos1215o2c k) + cos1215o2c 597 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 596) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_596
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 597 - ((2491773/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_597).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_598 : ((34426569/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 598, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 598, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 597, cos1215o2c k) + cos1215o2c 598 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 597) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_597
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 598 - ((569377/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_598).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_599 : ((66273063/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 599, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 599, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 598, cos1215o2c k) + cos1215o2c 599 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 598) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_598
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 599 - ((-103183/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_599).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_600 : ((957393/78125 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 600, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 600, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 599, cos1215o2c k) + cos1215o2c 600 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 599) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_599
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 600 - ((-4999411/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_600).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_601 : ((117111349/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 601, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 601, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 600, cos1215o2c k) + cos1215o2c 601 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 600) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_600
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 601 - ((-1086791/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_601).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_602 : ((24265783/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 602, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 602, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 601, cos1215o2c k) + cos1215o2c 602 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 601) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_601
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 602 - ((2109283/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_602).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_603 : ((32811833/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 603, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 603, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 602, cos1215o2c k) + cos1215o2c 603 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 602) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_602
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 603 - ((9919417/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_603).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_604 : ((27524199/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 604, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 604, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 603, cos1215o2c k) + cos1215o2c 604 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 603) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_603
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 604 - ((6374663/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_604).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_605 : ((67266707/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 605, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 605, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 604, cos1215o2c k) + cos1215o2c 605 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 604) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_604
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 605 - ((-3086581/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_605).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_606 : ((124852581/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 606, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 606, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 605, cos1215o2c k) + cos1215o2c 606 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 605) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_605
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 606 - ((-9679833/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_606).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_607 : ((23504103/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 607, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 607, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 606, cos1215o2c k) + cos1215o2c 607 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 606) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_606
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 607 - ((-3665533/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_607).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_608 : ((5964077/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 608, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 608, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 607, cos1215o2c k) + cos1215o2c 608 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 607) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_607
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 608 - ((70481/400000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_608).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_609 : ((128509337/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 609, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 609, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 608, cos1215o2c k) + cos1215o2c 609 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 608) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_608
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 609 - ((9228797/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_609).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_610 : ((136753657/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 610, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 610, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 609, cos1215o2c k) + cos1215o2c 610 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 609) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_609
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 610 - ((206133/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_610).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_611 : ((68247791/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 611, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 611, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 610, cos1215o2c k) + cos1215o2c 611 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 610) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_610
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 611 - ((-10283/400000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_611).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_612 : ((127977927/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 612, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 612, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 611, cos1215o2c k) + cos1215o2c 612 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 611) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_611
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 612 - ((-1703331/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_612).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_613 : ((23786073/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 613, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 613, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 612, cos1215o2c k) + cos1215o2c 613 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 612) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_612
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 613 - ((-4523281/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_613).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_614 : ((23506099/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 614, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 614, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 613, cos1215o2c k) + cos1215o2c 614 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 613) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_613
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 614 - ((-139887/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_614).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_615 : ((25006131/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 615, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 615, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 614, cos1215o2c k) + cos1215o2c 615 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 614) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_614
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 615 - ((187529/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_615).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_616 : ((134682029/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 616, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 616, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 615, cos1215o2c k) + cos1215o2c 616 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 615) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_615
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 616 - ((4826187/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_616).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_617 : ((68917733/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 617, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 617, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 616, cos1215o2c k) + cos1215o2c 617 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 616) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_616
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 617 - ((3154437/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_617).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_618 : ((131680719/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 618, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 618, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 617, cos1215o2c k) + cos1215o2c 618 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 617) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_617
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 618 - ((-6153747/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_618).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_619 : ((121707287/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 619, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 619, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 618, cos1215o2c k) + cos1215o2c 619 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 618) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_618
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 619 - ((-623277/625000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_619).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_620 : ((58386559/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 620, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 620, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 619, cos1215o2c k) + cos1215o2c 620 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 619) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_619
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 620 - ((-4933169/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_620).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_621 : ((60619893/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 621, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 621, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 620, cos1215o2c k) + cos1215o2c 621 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 620) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_620
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 621 - ((1116917/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_621).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_622 : ((131154171/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 622, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 622, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 621, cos1215o2c k) + cos1215o2c 622 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 621) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_621
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 622 - ((1983077/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_622).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_623 : ((137784737/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 623, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 623, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 622, cos1215o2c k) + cos1215o2c 623 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 622) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_622
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 623 - ((3315783/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_623).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_624 : ((2114323/156250 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 624, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 624, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 623, cos1215o2c k) + cos1215o2c 624 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 623) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_623
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 624 - ((-493413/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_624).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_625 : ((25183517/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 625, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 625, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 624, cos1215o2c k) + cos1215o2c 625 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 624) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_624
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 625 - ((-9398087/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_625).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_626 : ((58896129/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 626, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 626, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 625, cos1215o2c k) + cos1215o2c 626 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 625) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_625
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 626 - ((-8124327/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_626).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_627 : ((118005033/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 627, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 627, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 626, cos1215o2c k) + cos1215o2c 627 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 626) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_626
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 627 - ((8551/400000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_627).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_628 : ((126361499/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 628, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 628, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 627, cos1215o2c k) + cos1215o2c 628 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 627) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_627
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 628 - ((4178733/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_628).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_629 : ((135627401/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 629, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 629, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 628, cos1215o2c k) + cos1215o2c 629 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 628) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_628
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 629 - ((4633451/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_629).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_630 : ((137812931/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 630, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 630, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 629, cos1215o2c k) + cos1215o2c 630 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 629) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_629
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 630 - ((218653/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_630).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_631 : ((65523239/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 631, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 631, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 630, cos1215o2c k) + cos1215o2c 631 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 630) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_630
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 631 - ((-6765453/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_631).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_632 : ((60567723/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 632, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 632, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 631, cos1215o2c k) + cos1215o2c 632 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 631) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_631
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 632 - ((-619377/625000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_632).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_633 : ((58275921/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 633, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 633, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 632, cos1215o2c k) + cos1215o2c 633 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 632) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_632
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 633 - ((-1145651/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_633).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_634 : ((121194353/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 634, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 634, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 633, cos1215o2c k) + cos1215o2c 634 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 633) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_633
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 634 - ((4643511/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_634).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_635 : ((32777089/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 635, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 635, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 634, cos1215o2c k) + cos1215o2c 635 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 634) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_634
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 635 - ((9915003/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_635).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_636 : ((2154521/156250 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 636, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 636, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 635, cos1215o2c k) + cos1215o2c 636 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 635) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_635
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 636 - ((1695497/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_636).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_637 : ((33953053/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 637, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 637, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 636, cos1215o2c k) + cos1215o2c 637 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 636) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_636
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 637 - ((-519033/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_637).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_638 : ((63317489/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 638, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 638, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 637, cos1215o2c k) + cos1215o2c 638 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 637) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_637
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 638 - ((-4588117/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_638).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_639 : ((59035477/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 639, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 639, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 638, cos1215o2c k) + cos1215o2c 639 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 638) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_638
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 639 - ((-535189/625000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_639).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_640 : ((117289553/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 640, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 640, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 639, cos1215o2c k) + cos1215o2c 640 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 639) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_639
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 640 - ((-780401/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_640).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_641 : ((124934229/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 641, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 641, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 640, cos1215o2c k) + cos1215o2c 641 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 640) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_640
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 641 - ((1911419/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_641).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_642 : ((26926139/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 642, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 642, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 641, cos1215o2c k) + cos1215o2c 642 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 641) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_641
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 642 - ((4848733/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_642).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_643 : ((138326617/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 643, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 643, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 642, cos1215o2c k) + cos1215o2c 643 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 642) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_642
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 643 - ((1848461/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_643).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_644 : ((8310517/625000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 644, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 644, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 643, cos1215o2c k) + cos1215o2c 644 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 643) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_643
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 644 - ((-1071469/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_644).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_645 : ((122986999/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 645, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 645, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 644, cos1215o2c k) + cos1215o2c 645 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 644) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_644
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 645 - ((-9980273/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_645).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_646 : ((4664061/400000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 646, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 646, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 645, cos1215o2c k) + cos1215o2c 646 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 645) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_645
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 646 - ((-3192237/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_646).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_647 : ((119046853/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 647, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 647, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 646, cos1215o2c k) + cos1215o2c 647 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 646) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_646
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 647 - ((305791/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_647).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_648 : ((128312213/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 648, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 648, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 647, cos1215o2c k) + cos1215o2c 648 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 647) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_647
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 648 - ((231659/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_648).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_649 : ((136829167/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 649, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 649, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 648, cos1215o2c k) + cos1215o2c 649 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 648) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_648
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 649 - ((4258977/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_649).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_650 : ((17208517/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 650, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 650, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 649, cos1215o2c k) + cos1215o2c 650 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 649) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_649
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 650 - ((839969/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_650).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_651 : ((130155561/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 651, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 651, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 650, cos1215o2c k) + cos1215o2c 651 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 650) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_650
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 651 - ((-300463/400000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_651).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_652 : ((4815093/400000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 652, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 652, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 651, cos1215o2c k) + cos1215o2c 652 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 651) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_651
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 652 - ((-2444309/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_652).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_653 : ((29055831/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 653, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 653, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 652, cos1215o2c k) + cos1215o2c 653 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 652) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_652
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 653 - ((-4153001/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_653).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_654 : ((121028193/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 654, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 654, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 653, cos1215o2c k) + cos1215o2c 654 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 653) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_653
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 654 - ((4805869/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_654).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_655 : ((8182973/625000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 655, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 655, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 654, cos1215o2c k) + cos1215o2c 655 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 654) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_654
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 655 - ((79203/80000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_655).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_656 : ((68998571/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 656, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 656, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 655, cos1215o2c k) + cos1215o2c 656 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 655) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_655
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 656 - ((3535287/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_656).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_657 : ((68299977/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 657, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 657, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 656, cos1215o2c k) + cos1215o2c 657 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 656) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_656
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 657 - ((-349047/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_657).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_658 : ((63927901/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 658, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 658, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 657, cos1215o2c k) + cos1215o2c 658 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 657) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_657
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 658 - ((-546447/625000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_658).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_659 : ((29676693/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 659, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 659, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 658, cos1215o2c k) + cos1215o2c 659 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 658) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_658
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 659 - ((-914803/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_659).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_660 : ((23277671/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 660, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 660, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 659, cos1215o2c k) + cos1215o2c 660 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 659) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_659
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 660 - ((-2317417/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_660).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_661 : ((61360477/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 661, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 661, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 660, cos1215o2c k) + cos1215o2c 661 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 660) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_660
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 661 - ((6333599/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_661).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_662 : ((3317859/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 662, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 662, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 661, cos1215o2c k) + cos1215o2c 662 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 661) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_661
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 662 - ((4997203/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_662).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_663 : ((69263431/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 663, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 663, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 662, cos1215o2c k) + cos1215o2c 663 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 662) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_662
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 663 - ((2906751/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_663).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_664 : ((135616197/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 664, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 664, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 663, cos1215o2c k) + cos1215o2c 664 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 663) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_663
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 664 - ((-581933/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_664).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_665 : ((31565233/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 665, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 665, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 664, cos1215o2c k) + cos1215o2c 665 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 664) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_664
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 665 - ((-1870853/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_665).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_666 : ((2943563/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 666, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 666, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 665, cos1215o2c k) + cos1215o2c 666 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 665) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_665
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 666 - ((-2129353/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_666).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_667 : ((58332771/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 667, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 667, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 666, cos1215o2c k) + cos1215o2c 667 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 666) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_666
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 667 - ((-537989/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_667).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_668 : ((123854033/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 668, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 668, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 667, cos1215o2c k) + cos1215o2c 668 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 667) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_667
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 668 - ((7189491/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_668).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_669 : ((133754841/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 669, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 669, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 668, cos1215o2c k) + cos1215o2c 669 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 668) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_668
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 669 - ((618863/625000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_669).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_670 : ((69374853/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 670, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 670, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 669, cos1215o2c k) + cos1215o2c 670 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 669) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_669
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 670 - ((999173/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_670).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_671 : ((33753137/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 671, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 671, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 670, cos1215o2c k) + cos1215o2c 671 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 670) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_670
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 671 - ((-1868079/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_671).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_672 : ((25081979/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 672, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 672, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 671, cos1215o2c k) + cos1215o2c 672 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 671) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_671
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 672 - ((-9601653/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_672).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_673 : ((58635489/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 673, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 673, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 672, cos1215o2c k) + cos1215o2c 673 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 672) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_672
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 673 - ((-8137917/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_673).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_674 : ((116783859/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 674, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 674, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 673, cos1215o2c k) + cos1215o2c 674 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 673) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_673
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 674 - ((-486119/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_674).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_675 : ((124308767/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 675, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 675, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 674, cos1215o2c k) + cos1215o2c 675 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 674) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_674
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 675 - ((1881477/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_675).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_676 : ((67072623/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 676, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 676, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 675, cos1215o2c k) + cos1215o2c 676 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 675) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_675
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 676 - ((9837479/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_676).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_677 : ((69435197/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 677, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 677, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 676, cos1215o2c k) + cos1215o2c 677 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 676) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_676
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 677 - ((1181537/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_677).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_678 : ((33733647/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 678, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 678, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 677, cos1215o2c k) + cos1215o2c 678 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 677) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_677
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 678 - ((-1967403/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_678).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_679 : ((62649259/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 679, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 679, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 678, cos1215o2c k) + cos1215o2c 679 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 678) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_678
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 679 - ((-963507/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_679).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_680 : ((1830879/156250 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 680, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 680, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 679, cos1215o2c k) + cos1215o2c 680 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 679) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_679
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 680 - ((-4060631/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_680).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_681 : ((23325097/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 681, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 681, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 680, cos1215o2c k) + cos1215o2c 681 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 680) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_680
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 681 - ((-549771/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_681).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_682 : ((24809341/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 682, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 682, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 681, cos1215o2c k) + cos1215o2c 682 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 681) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_681
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 682 - ((371111/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_682).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_683 : ((133924749/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 683, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 683, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 682, cos1215o2c k) + cos1215o2c 683 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 682) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_682
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 683 - ((2469761/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_683).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_684 : ((138946869/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 684, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 684, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 683, cos1215o2c k) + cos1215o2c 684 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 683) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_683
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 684 - ((62789/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_684).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_685 : ((135411653/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 685, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 685, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 684, cos1215o2c k) + cos1215o2c 685 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 684) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_684
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 685 - ((-441777/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_685).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_686 : ((125928887/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 686, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 686, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 685, cos1215o2c k) + cos1215o2c 686 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 685) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_685
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 686 - ((-4740883/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_686).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_687 : ((58731751/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 687, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 687, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 686, cos1215o2c k) + cos1215o2c 687 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 686) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_686
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 687 - ((-1692877/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_687).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_688 : ((116209887/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 688, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 688, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 687, cos1215o2c k) + cos1215o2c 688 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 687) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_687
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 688 - ((-250523/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_688).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_689 : ((123074447/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 689, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 689, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 688, cos1215o2c k) + cos1215o2c 689 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 688) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_688
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 689 - ((171639/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_689).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_690 : ((133051009/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 690, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 690, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 689, cos1215o2c k) + cos1215o2c 690 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 689) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_689
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 690 - ((4988781/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_690).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_691 : ((34723119/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 691, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 691, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 690, cos1215o2c k) + cos1215o2c 691 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 690) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_690
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 691 - ((5842467/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_691).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_692 : ((17046667/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 692, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 692, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 691, cos1215o2c k) + cos1215o2c 692 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 691) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_691
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 692 - ((-125907/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_692).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_693 : ((15915077/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 693, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 693, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 692, cos1215o2c k) + cos1215o2c 693 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 692) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_692
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 693 - ((-226293/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_693).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_694 : ((59129687/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 694, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 694, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 693, cos1215o2c k) + cos1215o2c 694 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 693) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_693
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 694 - ((-4530121/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_694).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_695 : ((115696709/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 695, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 695, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 694, cos1215o2c k) + cos1215o2c 695 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 694) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_694
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 695 - ((-512333/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_695).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_696 : ((30365117/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 696, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 696, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 695, cos1215o2c k) + cos1215o2c 696 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 695) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_695
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 696 - ((5764759/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_696).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_697 : ((32856023/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 697, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 697, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 696, cos1215o2c k) + cos1215o2c 697 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 696) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_696
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 697 - ((622789/625000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_697).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_698 : ((69241999/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 698, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 698, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 697, cos1215o2c k) + cos1215o2c 698 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 697) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_697
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 698 - ((3530453/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_698).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_699 : ((137626699/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 699, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 699, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 698, cos1215o2c k) + cos1215o2c 699 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 698) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_698
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 699 - ((-856299/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_699).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_700 : ((8091693/625000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 700, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 700, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 699, cos1215o2c k) + cos1215o2c 700 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 699) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_699
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 700 - ((-8158611/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_700).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_701 : ((29944629/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 701, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 701, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 700, cos1215o2c k) + cos1215o2c 701 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 700) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_700
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 701 - ((-2421893/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_701).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_702 : ((115390821/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 702, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 702, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 701, cos1215o2c k) + cos1215o2c 702 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 701) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_701
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 702 - ((-877339/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_702).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_703 : ((59690699/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 703, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 703, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 702, cos1215o2c k) + cos1215o2c 703 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 702) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_702
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 703 - ((3991577/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_703).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_704 : ((128943647/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 704, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 704, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 703, cos1215o2c k) + cos1215o2c 704 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 703) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_703
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 704 - ((9563249/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_704).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_705 : ((68692367/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 705, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 705, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 704, cos1215o2c k) + cos1215o2c 705 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 704) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_704
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 705 - ((8442087/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_705).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_706 : ((8676183/625000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 706, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 706, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 705, cos1215o2c k) + cos1215o2c 706 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 705) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_705
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 706 - ((717597/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_706).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_707 : ((66127711/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 707, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 707, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 706, cos1215o2c k) + cos1215o2c 707 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 706) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_706
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 707 - ((-3281253/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_707).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_708 : ((12225449/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 708, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 708, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 707, cos1215o2c k) + cos1215o2c 708 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 707) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_707
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 708 - ((-2499983/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_708).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_709 : ((115737981/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 709, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 709, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 708, cos1215o2c k) + cos1215o2c 709 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 708) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_708
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 709 - ((-6515509/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_709).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_710 : ((117197571/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 710, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 710, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 709, cos1215o2c k) + cos1215o2c 710 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 709) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_709
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 710 - ((146059/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_710).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_711 : ((125620129/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 711, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 711, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 710, cos1215o2c k) + cos1215o2c 711 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 710) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_710
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 711 - ((4211779/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_711).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_712 : ((16902079/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 712, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 712, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 711, cos1215o2c k) + cos1215o2c 712 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 711) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_711
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 712 - ((9597503/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_712).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_713 : ((139415997/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 713, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 713, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 712, cos1215o2c k) + cos1215o2c 713 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 712) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_712
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 713 - ((840073/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_713).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_714 : ((135356341/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 714, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 714, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 713, cos1215o2c k) + cos1215o2c 714 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 713) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_713
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 714 - ((-126833/312500 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_714).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_715 : ((31452433/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 715, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 715, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 714, cos1215o2c k) + cos1215o2c 715 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 714) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_714
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 715 - ((-9545609/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_715).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_716 : ((117264873/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 716, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 716, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 715, cos1215o2c k) + cos1215o2c 716 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 715) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_715
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 716 - ((-8543859/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_716).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_717 : ((57754109/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 717, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 717, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 716, cos1215o2c k) + cos1215o2c 717 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 716) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_716
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 717 - ((-351131/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_717).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_718 : ((121718587/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 718, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 718, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 717, cos1215o2c k) + cos1215o2c 718 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 717) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_717
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 718 - ((6211369/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_718).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_719 : ((131702419/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 719, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 719, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 718, cos1215o2c k) + cos1215o2c 719 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 718) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_718
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 719 - ((156013/156250 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_719).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_720 : ((4335781/312500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 720, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 720, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 719, cos1215o2c k) + cos1215o2c 720 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 719) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_719
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 720 - ((7043573/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_720).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_721 : ((138128063/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 721, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 721, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 720, cos1215o2c k) + cos1215o2c 721 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 720) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_720
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 721 - ((-615929/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_721).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_722 : ((1302713/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 722, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 722, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 721, cos1215o2c k) + cos1215o2c 722 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 721) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_721
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 722 - ((-7855763/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_722).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_723 : ((12042073/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 723, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 723, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 722, cos1215o2c k) + cos1215o2c 723 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 722) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_722
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 723 - ((-984957/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_723).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_724 : ((7195567/625000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 724, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 724, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 723, cos1215o2c k) + cos1215o2c 724 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 723) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_723
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 724 - ((-2645329/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_724).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_725 : ((23580311/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 725, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 725, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 724, cos1215o2c k) + cos1215o2c 725 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 724) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_724
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 725 - ((2773483/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_725).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_726 : ((1015157/80000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 726, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 726, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 725, cos1215o2c k) + cos1215o2c 726 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 725) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_725
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 726 - ((899407/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_726).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_727 : ((136166193/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 727, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 727, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 726, cos1215o2c k) + cos1215o2c 727 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 726) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_726
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 727 - ((1159071/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_727).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_728 : ((69806237/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 728, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 728, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 727, cos1215o2c k) + cos1215o2c 728 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 727) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_727
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 728 - ((3447281/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_728).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_729 : ((33744063/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 729, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 729, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 728, cos1215o2c k) + cos1215o2c 729 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 728) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_728
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 729 - ((-2317611/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_729).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_730 : ((62650661/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 730, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 730, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 729, cos1215o2c k) + cos1215o2c 730 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 729) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_729
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 730 - ((-967393/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_730).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_731 : ((116911323/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 731, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 731, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 730, cos1215o2c k) + cos1215o2c 731 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 730) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_730
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 731 - ((-8388999/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_731).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_732 : ((11527031/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 732, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 732, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 731, cos1215o2c k) + cos1215o2c 732 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 731) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_731
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 732 - ((-1640013/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_732).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_733 : ((121436859/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 733, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 733, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 732, cos1215o2c k) + cos1215o2c 733 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 732) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_732
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 733 - ((6167549/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_733).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_734 : ((131405471/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 734, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 734, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 733, cos1215o2c k) + cos1215o2c 734 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 733) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_733
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 734 - ((2492403/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_734).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_735 : ((138727679/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 735, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 735, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 734, cos1215o2c k) + cos1215o2c 735 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 734) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_734
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 735 - ((915401/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_735).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_736 : ((138683741/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 736, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 736, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 735, cos1215o2c k) + cos1215o2c 736 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 735) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_735
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 736 - ((-21469/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_736).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_737 : ((131309527/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 737, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 737, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 736, cos1215o2c k) + cos1215o2c 737 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 736) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_736
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 737 - ((-3686607/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_737).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_738 : ((60671093/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 738, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 738, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 737, cos1215o2c k) + cos1215o2c 738 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 737) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_737
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 738 - ((-9966341/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_738).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_739 : ((115161861/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 739, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 739, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 738, cos1215o2c k) + cos1215o2c 739 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 738) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_738
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 739 - ((-247173/400000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_739).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_740 : ((116708131/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 740, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 740, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 739, cos1215o2c k) + cos1215o2c 740 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 739) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_739
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 740 - ((154727/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_740).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_741 : ((31247131/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 741, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 741, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 740, cos1215o2c k) + cos1215o2c 741 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 740) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_740
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 741 - ((8281393/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_741).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_742 : ((67368559/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 742, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 742, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 741, cos1215o2c k) + cos1215o2c 742 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 741) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_741
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 742 - ((4874797/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_742).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_743 : ((139777271/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 743, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 743, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 742, cos1215o2c k) + cos1215o2c 743 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 742) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_742
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 743 - ((5041153/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_743).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_744 : ((68464459/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 744, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 744, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 743, cos1215o2c k) + cos1215o2c 744 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 743) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_743
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 744 - ((-2847353/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_744).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_745 : ((25598903/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 745, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 745, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 744, cos1215o2c k) + cos1215o2c 745 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 744) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_744
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 745 - ((-8933403/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_745).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_746 : ((118595777/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 746, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 746, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 745, cos1215o2c k) + cos1215o2c 746 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 745) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_745
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 746 - ((-4698869/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_746).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_747 : ((917/80 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 747, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 747, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 746, cos1215o2c k) + cos1215o2c 747 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 746) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_746
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 747 - ((-3969777/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_747).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_748 : ((118559517/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 748, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 748, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 747, cos1215o2c k) + cos1215o2c 748 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 747) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_747
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 748 - ((3935517/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_748).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_749 : ((63968039/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 749, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 749, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 748, cos1215o2c k) + cos1215o2c 749 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 748) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_748
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 749 - ((9377561/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_749).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_750 : ((136913717/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 750, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 750, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 749, cos1215o2c k) + cos1215o2c 750 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 749) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_749
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 750 - ((8978639/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_750).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_751 : ((139920041/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 751, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 751, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 750, cos1215o2c k) + cos1215o2c 751 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 750) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_750
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 751 - ((751831/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_751).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_752 : ((1055461/78125 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 752, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 752, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 751, cos1215o2c k) + cos1215o2c 752 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 751) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_751
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 752 - ((-4820033/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_752).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_753 : ((125435523/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 753, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 753, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 752, cos1215o2c k) + cos1215o2c 753 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 752) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_752
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 753 - ((-1932497/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_753).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_754 : ((116886691/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 754, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 754, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 753, cos1215o2c k) + cos1215o2c 754 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 753) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_753
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 754 - ((-1068479/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_754).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_755 : ((114703859/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 755, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 755, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 754, cos1215o2c k) + cos1215o2c 755 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 754) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_754
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 755 - ((-272729/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_755).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_756 : ((30054409/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 756, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 756, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 755, cos1215o2c k) + cos1215o2c 756 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 755) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_755
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 756 - ((5514777/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_756).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_757 : ((2600971/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 757, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 757, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 756, cos1215o2c k) + cos1215o2c 757 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 756) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_756
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 757 - ((4915957/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_757).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_758 : ((34548973/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 758, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 758, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 757, cos1215o2c k) + cos1215o2c 758 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 757) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_757
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 758 - ((4074171/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_758).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_759 : ((34926063/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 759, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 759, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 758, cos1215o2c k) + cos1215o2c 759 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 758) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_758
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 759 - ((18867/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_759).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_760 : ((133664291/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 760, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 760, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 759, cos1215o2c k) + cos1215o2c 760 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 759) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_759
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 760 - ((-6038961/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_760).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_761 : ((30934899/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 761, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 761, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 760, cos1215o2c k) + cos1215o2c 761 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 760) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_760
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 761 - ((-1984739/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_761).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_762 : ((57963123/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 762, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 762, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 761, cos1215o2c k) + cos1215o2c 762 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 761) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_761
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 762 - ((-156247/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_762).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_763 : ((28731963/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 763, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 763, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 762, cos1215o2c k) + cos1215o2c 763 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 762) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_762
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 763 - ((-498697/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_763).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_764 : ((121336367/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 764, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 764, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 763, cos1215o2c k) + cos1215o2c 764 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 763) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_763
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 764 - ((1281903/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_764).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_765 : ((131303073/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 765, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 765, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 764, cos1215o2c k) + cos1215o2c 765 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 764) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_764
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 765 - ((4983853/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_765).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_766 : ((138864867/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 766, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 766, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 765, cos1215o2c k) + cos1215o2c 766 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 765) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_765
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 766 - ((3781397/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_766).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_767 : ((139513431/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 767, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 767, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 766, cos1215o2c k) + cos1215o2c 767 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 766) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_766
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 767 - ((162391/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_767).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_768 : ((26573957/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 768, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 768, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 767, cos1215o2c k) + cos1215o2c 768 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 767) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_767
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 768 - ((-3321323/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_768).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_769 : ((61441629/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 769, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 769, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 768, cos1215o2c k) + cos1215o2c 769 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 768) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_768
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 769 - ((-9985527/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_769).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_770 : ((115468641/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 770, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 770, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 769, cos1215o2c k) + cos1215o2c 770 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 769) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_769
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 770 - ((-7413617/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_770).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_771 : ((4600039/400000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 771, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 771, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 770, cos1215o2c k) + cos1215o2c 771 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 770) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_770
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 771 - ((-233333/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_771).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_772 : ((121748449/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 772, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 772, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 771, cos1215o2c k) + cos1215o2c 772 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 771) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_771
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 772 - ((3374237/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_772).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_773 : ((131737933/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 773, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 773, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 772, cos1215o2c k) + cos1215o2c 773 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 772) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_772
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 773 - ((2497621/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_773).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_774 : ((17388729/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 774, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 774, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 773, cos1215o2c k) + cos1215o2c 774 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 773) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_773
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 774 - ((7372899/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_774).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_775 : ((139555143/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 775, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 775, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 774, cos1215o2c k) + cos1215o2c 775 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 774) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_774
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 775 - ((446311/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_775).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_776 : ((132820683/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 776, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 776, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 775, cos1215o2c k) + cos1215o2c 776 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 775) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_775
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 776 - ((-336673/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_776).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_777 : ((122832047/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 777, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 777, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 776, cos1215o2c k) + cos1215o2c 777 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 776) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_776
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 777 - ((-2496909/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_777).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_778 : ((115390209/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 778, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 778, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 777, cos1215o2c k) + cos1215o2c 778 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 777) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_777
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 778 - ((-3720419/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_778).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_779 : ((57400631/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 779, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 779, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 778, cos1215o2c k) + cos1215o2c 779 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 778) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_778
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 779 - ((-587947/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_779).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_780 : ((30349529/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 780, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 780, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 779, cos1215o2c k) + cos1215o2c 780 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 779) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_779
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 780 - ((3298927/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_780).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_781 : ((26274251/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 781, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 781, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 780, cos1215o2c k) + cos1215o2c 781 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 780) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_780
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 781 - ((9974139/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_781).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_782 : ((13898363/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 782, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 782, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 781, cos1215o2c k) + cos1215o2c 782 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 781) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_781
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 782 - ((60907/80000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_782).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_783 : ((69935973/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 783, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 783, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 782, cos1215o2c k) + cos1215o2c 783 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 782) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_782
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 783 - ((222329/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_783).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_784 : ((133533661/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 784, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 784, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 783, cos1215o2c k) + cos1215o2c 784 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 783) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_783
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 784 - ((-1267457/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_784).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_785 : ((123593157/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 785, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 785, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 784, cos1215o2c k) + cos1215o2c 785 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 784) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_784
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 785 - ((-621219/625000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_785).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_786 : ((115712481/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 786, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 786, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 785, cos1215o2c k) + cos1215o2c 786 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 785) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_785
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 786 - ((-1969919/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_786).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_787 : ((22872987/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 787, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 787, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 786, cos1215o2c k) + cos1215o2c 787 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 786) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_786
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 787 - ((-673273/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_787).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_788 : ((120306481/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 788, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 788, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 787, cos1215o2c k) + cos1215o2c 788 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 787) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_787
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 788 - ((2971273/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_788).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_789 : ((65085679/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 789, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 789, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 788, cos1215o2c k) + cos1215o2c 789 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 788) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_788
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 789 - ((9865877/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_789).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_790 : ((17299071/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 790, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 790, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 789, cos1215o2c k) + cos1215o2c 790 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 789) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_789
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 790 - ((822221/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_790).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_791 : ((28069407/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 791, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 791, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 790, cos1215o2c k) + cos1215o2c 791 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 790) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_790
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 791 - ((1955467/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_791).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_792 : ((134943817/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 792, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 792, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 791, cos1215o2c k) + cos1215o2c 792 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 791) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_791
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 792 - ((-2701109/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_792).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_793 : ((31303543/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 793, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 793, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 792, cos1215o2c k) + cos1215o2c 793 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 792) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_792
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 793 - ((-1945729/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_793).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_794 : ((29148909/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 794, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 794, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 793, cos1215o2c k) + cos1215o2c 794 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 793) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_793
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 794 - ((-134649/156250 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_794).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_795 : ((113888253/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 795, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 795, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 794, cos1215o2c k) + cos1215o2c 795 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 794) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_794
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 795 - ((-2706383/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_795).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_796 : ((118589731/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 796, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 796, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 795, cos1215o2c k) + cos1215o2c 796 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 795) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_795
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 796 - ((2351239/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_796).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_797 : ((64042883/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 797, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 797, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 796, cos1215o2c k) + cos1215o2c 797 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 796) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_796
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 797 - ((1899407/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_797).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_798 : ((137118453/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 798, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 798, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 797, cos1215o2c k) + cos1215o2c 798 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 797) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_797
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 798 - ((9033687/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_798).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_799 : ((140703079/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 799, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 799, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 798, cos1215o2c k) + cos1215o2c 799 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 798) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_798
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 799 - ((1792813/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_799).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_800 : ((136871233/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 800, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 800, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 799, cos1215o2c k) + cos1215o2c 800 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 799) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_799
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 800 - ((-1915423/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_800).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_801 : ((127734351/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 801, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 801, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 800, cos1215o2c k) + cos1215o2c 801 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 800) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_800
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 801 - ((-4567941/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_801).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_802 : ((7393947/625000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 802, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 802, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 801, cos1215o2c k) + cos1215o2c 802 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 801) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_801
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 802 - ((-9430199/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_802).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_803 : ((113732443/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 803, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 803, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 802, cos1215o2c k) + cos1215o2c 803 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 802) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_802
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 803 - ((-4569709/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_803).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_804 : ((116508903/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 804, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 804, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 803, cos1215o2c k) + cos1215o2c 804 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 803) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_803
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 804 - ((138873/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_804).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_805 : ((3909829/312500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 805, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 805, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 804, cos1215o2c k) + cos1215o2c 805 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 804) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_804
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 805 - ((68853/80000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_805).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_806 : ((134872537/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 806, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 806, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 805, cos1215o2c k) + cos1215o2c 806 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 805) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_805
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 806 - ((9759009/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_806).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_807 : ((17562239/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 807, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 807, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 806, cos1215o2c k) + cos1215o2c 807 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 806) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_806
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 807 - ((45011/80000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_807).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_808 : ((138955529/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 808, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 808, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 807, cos1215o2c k) + cos1215o2c 808 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 807) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_807
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 808 - ((-1541383/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_808).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_809 : ((131083043/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 809, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 809, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 808, cos1215o2c k) + cos1215o2c 809 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 808) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_808
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 809 - ((-3935743/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_809).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_810 : ((60559423/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 810, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 810, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 809, cos1215o2c k) + cos1215o2c 810 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 809) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_809
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 810 - ((-9963197/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_810).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_811 : ((57204347/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 811, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 811, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 810, cos1215o2c k) + cos1215o2c 811 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 810) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_810
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 811 - ((-209661/312500 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_811).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_812 : ((114539489/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 812, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 812, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 811, cos1215o2c k) + cos1215o2c 812 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 811) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_811
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 812 - ((26359/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_812).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_813 : ((60717079/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 813, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 813, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 812, cos1215o2c k) + cos1215o2c 813 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 812) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_812
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 813 - ((6895669/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_813).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_814 : ((26282643/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 814, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 814, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 813, cos1215o2c k) + cos1215o2c 814 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 813) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_813
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 814 - ((9980057/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_814).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_815 : ((139170797/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 815, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 815, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 814, cos1215o2c k) + cos1215o2c 815 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 814) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_814
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 815 - ((3879291/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_815).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_816 : ((14059649/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 816, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 816, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 815, cos1215o2c k) + cos1215o2c 816 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 815) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_815
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 816 - ((1426693/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_816).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_817 : ((16867759/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 817, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 817, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 816, cos1215o2c k) + cos1215o2c 817 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 816) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_816
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 817 - ((-2826709/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_817).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_818 : ((125197149/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 818, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 818, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 817, cos1215o2c k) + cos1215o2c 818 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 817) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_817
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 818 - ((-9743923/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_818).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_819 : ((116495137/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 819, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 819, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 818, cos1215o2c k) + cos1215o2c 819 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 818) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_818
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 819 - ((-2175253/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_819).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_820 : ((22680953/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 820, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 820, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 819, cos1215o2c k) + cos1215o2c 820 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 819) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_819
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 820 - ((-772343/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_820).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_821 : ((29384807/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 821, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 821, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 820, cos1215o2c k) + cos1215o2c 821 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 820) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_820
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 821 - ((4135463/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_821).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_822 : ((25345849/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 822, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 822, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 821, cos1215o2c k) + cos1215o2c 822 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 821) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_821
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 822 - ((9191017/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_822).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_823 : ((136176753/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 823, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 823, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 822, cos1215o2c k) + cos1215o2c 823 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 822) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_822
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 823 - ((2362127/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_823).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_824 : ((28193039/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 824, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 824, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 823, cos1215o2c k) + cos1215o2c 824 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 823) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_823
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 824 - ((2394721/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_824).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_825 : ((69306583/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 825, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 825, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 824, cos1215o2c k) + cos1215o2c 825 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 824) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_824
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 825 - ((-2351029/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_825).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_826 : ((6517249/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 826, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 826, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 825, cos1215o2c k) + cos1215o2c 826 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 825) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_825
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 826 - ((-4133593/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_826).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_827 : ((60219159/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 827, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 827, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 826, cos1215o2c k) + cos1215o2c 827 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 826) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_826
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 827 - ((-4952831/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_827).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_828 : ((28500383/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 828, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 828, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 827, cos1215o2c k) + cos1215o2c 828 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 827) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_827
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 828 - ((-3217893/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_828).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_829 : ((3573167/312500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 829, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 829, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 828, cos1215o2c k) + cos1215o2c 829 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 828) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_828
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 829 - ((85203/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_829).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_830 : ((121276453/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 830, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 830, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 829, cos1215o2c k) + cos1215o2c 830 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 829) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_829
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 830 - ((6936109/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_830).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_831 : ((13124891/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 831, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 831, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 830, cos1215o2c k) + cos1215o2c 831 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 830) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_830
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 831 - ((9973457/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_831).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_832 : ((34790381/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 832, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 832, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 831, cos1215o2c k) + cos1215o2c 832 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 831) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_831
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 832 - ((3956807/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_832).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_833 : ((8811457/625000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 833, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 833, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 832, cos1215o2c k) + cos1215o2c 833 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 832) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_832
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 833 - ((455697/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_833).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_834 : ((2121769/156250 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 834, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 834, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 833, cos1215o2c k) + cos1215o2c 834 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 833) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_833
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 834 - ((-648637/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_834).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_835 : ((126230773/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 835, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 835, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 834, cos1215o2c k) + cos1215o2c 835 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 834) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_834
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 835 - ((-9561443/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_835).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_836 : ((117139543/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 836, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 836, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 835, cos1215o2c k) + cos1215o2c 836 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 835) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_835
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 836 - ((-909023/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_836).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_837 : ((11310913/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 837, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 837, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 836, cos1215o2c k) + cos1215o2c 837 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 836) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_836
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 837 - ((-4029413/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_837).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_838 : ((116165263/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 838, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 838, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 837, cos1215o2c k) + cos1215o2c 838 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 837) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_837
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 838 - ((3057133/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_838).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_839 : ((62381933/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 839, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 839, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 838, cos1215o2c k) + cos1215o2c 839 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 838) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_838
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 839 - ((8599603/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_839).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_840 : ((134586687/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 840, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 840, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 839, cos1215o2c k) + cos1215o2c 840 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 839) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_839
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 840 - ((9823821/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_840).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_841 : ((140716887/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 841, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 841, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 840, cos1215o2c k) + cos1215o2c 841 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 840) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_840
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 841 - ((1916/3125 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_841).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_842 : ((17512099/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 842, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 842, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 841, cos1215o2c k) + cos1215o2c 842 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 841) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_841
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 842 - ((-123819/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_842).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_843 : ((133041767/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 843, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 843, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 842, cos1215o2c k) + cos1215o2c 843 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 842) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_842
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 843 - ((-282161/400000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_843).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_844 : ((123063617/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 844, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 844, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 843, cos1215o2c k) + cos1215o2c 844 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 843) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_843
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 844 - ((-199543/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_844).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_845 : ((3597269/312500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 845, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 845, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 844, cos1215o2c k) + cos1215o2c 845 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 844) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_844
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 845 - ((-7950009/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_845).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_846 : ((11311983/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 846, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 846, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 845, cos1215o2c k) + cos1215o2c 846 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 845) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_845
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 846 - ((-995889/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_846).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_847 : ((59031313/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 847, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 847, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 846, cos1215o2c k) + cos1215o2c 847 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 846) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_846
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 847 - ((1235949/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_847).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_848 : ((1992183/156250 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 848, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 848, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 847, cos1215o2c k) + cos1215o2c 848 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 847) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_847
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 848 - ((4719043/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_848).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_849 : ((136788643/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 849, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 849, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 848, cos1215o2c k) + cos1215o2c 849 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 848) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_848
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 849 - ((9289931/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_849).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_850 : ((17671833/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 850, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 850, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 849, cos1215o2c k) + cos1215o2c 850 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 849) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_849
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 850 - ((4587021/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_850).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_851 : ((69509179/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 851, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 851, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 850, cos1215o2c k) + cos1215o2c 851 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 850) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_850
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 851 - ((-1177653/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_851).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_852 : ((32719039/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 852, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 852, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 851, cos1215o2c k) + cos1215o2c 852 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 851) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_851
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 852 - ((-4070601/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_852).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_853 : ((120918383/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 853, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 853, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 852, cos1215o2c k) + cos1215o2c 853 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 852) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_852
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 853 - ((-9956773/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_853).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_854 : ((56992273/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 854, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 854, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 853, cos1215o2c k) + cos1215o2c 854 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 853) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_853
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 854 - ((-6932837/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_854).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_855 : ((113433041/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 855, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 855, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 854, cos1215o2c k) + cos1215o2c 855 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 854) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_854
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 855 - ((-110101/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_855).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_856 : ((59761929/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 856, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 856, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 855, cos1215o2c k) + cos1215o2c 856 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 855) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_855
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 856 - ((6091817/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_856).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_857 : ((16163813/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 857, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 857, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 856, cos1215o2c k) + cos1215o2c 857 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 856) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_856
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 857 - ((4893823/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_857).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_858 : ((138075941/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 858, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 858, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 857, cos1215o2c k) + cos1215o2c 858 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 857) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_857
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 858 - ((8766437/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_858).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_859 : ((70804291/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 859, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 859, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 858, cos1215o2c k) + cos1215o2c 859 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 858) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_858
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 859 - ((3533641/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_859).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_860 : ((138219963/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 860, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 860, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 859, cos1215o2c k) + cos1215o2c 860 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 859) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_859
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 860 - ((-3387619/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_860).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_861 : ((32384149/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 861, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 861, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 860, cos1215o2c k) + cos1215o2c 861 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 860) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_860
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 861 - ((-8682367/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_861).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_862 : ((23941603/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 862, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 862, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 861, cos1215o2c k) + cos1215o2c 862 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 861) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_861
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 862 - ((-9827581/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_862).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_863 : ((113415239/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 863, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 863, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 862, cos1215o2c k) + cos1215o2c 863 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 862) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_862
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 863 - ((-98309/156250 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_863).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_864 : ((113644729/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 864, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 864, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 863, cos1215o2c k) + cos1215o2c 864 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 863) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_863
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 864 - ((23049/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_864).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_865 : ((60140561/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 865, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 865, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 864, cos1215o2c k) + cos1215o2c 865 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 864) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_864
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 865 - ((6637393/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_865).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_866 : ((32544483/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 866, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 866, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 865, cos1215o2c k) + cos1215o2c 866 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 865) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_865
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 866 - ((989781/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_866).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_867 : ((69330121/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 867, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 867, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 866, cos1215o2c k) + cos1215o2c 867 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 866) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_866
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 867 - ((848331/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_867).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_868 : ((70866809/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 868, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 868, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 867, cos1215o2c k) + cos1215o2c 868 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 867) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_867
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 868 - ((384297/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_868).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_869 : ((137958717/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 869, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 869, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 868, cos1215o2c k) + cos1215o2c 869 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 868) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_868
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 869 - ((-3773901/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_869).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_870 : ((129111593/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 870, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 870, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 869, cos1215o2c k) + cos1215o2c 870 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 869) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_869
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 870 - ((-2211531/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_870).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_871 : ((2386719/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 871, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 871, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 870, cos1215o2c k) + cos1215o2c 871 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 870) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_870
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 871 - ((-9774643/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_871).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_872 : ((28298993/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 872, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 872, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 871, cos1215o2c k) + cos1215o2c 872 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 871) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_871
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 872 - ((-3069489/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_872).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_873 : ((113547567/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 873, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 873, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 872, cos1215o2c k) + cos1215o2c 873 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 872) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_872
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 873 - ((70519/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_873).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_874 : ((60110361/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 874, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 874, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 873, cos1215o2c k) + cos1215o2c 874 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 873) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_873
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 874 - ((1334831/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_874).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_875 : ((130114221/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 875, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 875, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 874, cos1215o2c k) + cos1215o2c 875 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 874) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_874
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 875 - ((9894499/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_875).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_876 : ((138646301/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 876, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 876, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 875, cos1215o2c k) + cos1215o2c 876 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 875) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_875
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 876 - ((213327/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_876).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_877 : ((70939083/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 877, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 877, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 876, cos1215o2c k) + cos1215o2c 877 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 876) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_876
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 877 - ((646573/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_877).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_878 : ((69162683/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 878, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 878, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 877, cos1215o2c k) + cos1215o2c 878 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 877) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_877
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 878 - ((-17759/50000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_878).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_879 : ((6481361/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 879, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 879, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 878, cos1215o2c k) + cos1215o2c 879 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 878) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_878
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 879 - ((-4348573/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_879).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_880 : ((59889143/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 880, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 880, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 879, cos1215o2c k) + cos1215o2c 880 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 879) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_879
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 880 - ((-4923967/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_880).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_881 : ((113287487/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 881, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 881, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 880, cos1215o2c k) + cos1215o2c 881 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 880) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_880
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 881 - ((-6489799/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_881).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_882 : ((113115547/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 882, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 882, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 881, cos1215o2c k) + cos1215o2c 882 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 881) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_881
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 882 - ((-8547/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_882).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_883 : ((119334781/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 883, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 883, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 882, cos1215o2c k) + cos1215o2c 883 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 882) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_882
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 883 - ((3110117/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_883).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_884 : ((16138763/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 884, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 884, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 883, cos1215o2c k) + cos1215o2c 884 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 883) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_883
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 884 - ((9776323/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_884).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_885 : ((34500581/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 885, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 885, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 884, cos1215o2c k) + cos1215o2c 885 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 884) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_884
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 885 - ((444661/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_885).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_886 : ((141985681/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 886, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 886, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 885, cos1215o2c k) + cos1215o2c 886 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 885) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_885
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 886 - ((3984357/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_886).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_887 : ((17408111/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 887, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 887, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 886, cos1215o2c k) + cos1215o2c 887 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 886) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_886
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 887 - ((-2719793/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_887).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_888 : ((26214417/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 888, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 888, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 887, cos1215o2c k) + cos1215o2c 888 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 887) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_887
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 888 - ((-8191803/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_888).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_889 : ((1892151/156250 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 889, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 889, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 888, cos1215o2c k) + cos1215o2c 889 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 888) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_888
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 889 - ((-9973421/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_889).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_890 : ((113819959/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 890, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 890, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 889, cos1215o2c k) + cos1215o2c 890 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 889) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_889
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 890 - ((-1455341/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_890).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_891 : ((112495879/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 891, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 891, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 890, cos1215o2c k) + cos1215o2c 891 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 890) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_890
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 891 - ((-33077/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_891).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_892 : ((14713871/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 892, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 892, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 891, cos1215o2c k) + cos1215o2c 892 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 891) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_891
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 892 - ((5216089/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_892).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_893 : ((127132777/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 893, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 893, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 892, cos1215o2c k) + cos1215o2c 893 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 892) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_892
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 893 - ((9422809/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_893).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_894 : ((17070541/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 894, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 894, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 893, cos1215o2c k) + cos1215o2c 894 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 893) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_893
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 894 - ((9432551/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_894).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_895 : ((141816731/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 895, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 895, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 894, cos1215o2c k) + cos1215o2c 895 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 894) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_894
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 895 - ((5253403/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_895).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_896 : ((140566203/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 896, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 896, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 895, cos1215o2c k) + cos1215o2c 896 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 895) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_895
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 896 - ((-156191/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_896).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_897 : ((133371567/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 897, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 897, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 896, cos1215o2c k) + cos1215o2c 897 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 896) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_896
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 897 - ((-1798409/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_897).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_898 : ((61705987/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 898, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 898, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 897, cos1215o2c k) + cos1215o2c 898 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 897) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_897
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 898 - ((-9958593/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_898).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_899 : ((115074479/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 899, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 899, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 898, cos1215o2c k) + cos1215o2c 899 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 898) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_898
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 899 - ((-1667299/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_899).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_900 : ((28004949/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 900, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 900, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 899, cos1215o2c k) + cos1215o2c 900 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 899) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_899
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 900 - ((-3053683/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_900).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_901 : ((115581783/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 901, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 901, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 900, cos1215o2c k) + cos1215o2c 901 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 900) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_900
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 901 - ((3562987/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_901).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_902 : ((31048929/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 902, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 902, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 901, cos1215o2c k) + cos1215o2c 902 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 901) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_901
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 902 - ((8614933/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_902).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_903 : ((134096153/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 903, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 903, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 902, cos1215o2c k) + cos1215o2c 903 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 902) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_902
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 903 - ((9901437/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_903).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_904 : ((140969119/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 904, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 904, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 903, cos1215o2c k) + cos1215o2c 904 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 903) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_903
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 904 - ((3436983/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_904).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_905 : ((141829513/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 905, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 905, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 904, cos1215o2c k) + cos1215o2c 905 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 904) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_904
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 905 - ((430697/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_905).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_906 : ((27261843/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 906, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 906, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 905, cos1215o2c k) + cos1215o2c 906 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 905) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_905
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 906 - ((-2759649/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_906).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_907 : ((7925207/625000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 907, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 907, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 906, cos1215o2c k) + cos1215o2c 907 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 906) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_906
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 907 - ((-9504903/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_907).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_908 : ((117420359/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 908, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 908, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 907, cos1215o2c k) + cos1215o2c 908 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 907) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_907
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 908 - ((-9381953/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_908).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_909 : ((56101773/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 909, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 909, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 908, cos1215o2c k) + cos1215o2c 909 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 908) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_908
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 909 - ((-5215813/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_909).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_910 : ((14174019/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 910, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 910, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 909, cos1215o2c k) + cos1215o2c 910 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 909) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_909
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 910 - ((594803/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_910).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_911 : ((60234863/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 911, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 911, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 910, cos1215o2c k) + cos1215o2c 911 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 910) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_910
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 911 - ((3539287/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_911).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_912 : ((65199683/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 912, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 912, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 911, cos1215o2c k) + cos1215o2c 912 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 911) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_911
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 912 - ((124133/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_912).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_913 : ((138934509/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 913, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 913, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 912, cos1215o2c k) + cos1215o2c 913 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 912) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_912
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 913 - ((8536143/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_913).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_914 : ((28487233/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 914, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 914, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 913, cos1215o2c k) + cos1215o2c 914 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 913) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_913
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 914 - ((54729/156250 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_914).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_915 : ((69709219/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 915, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 915, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 914, cos1215o2c k) + cos1215o2c 915 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 914) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_914
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 915 - ((-3016727/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_915).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_916 : ((65584237/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 916, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 916, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 915, cos1215o2c k) + cos1215o2c 916 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 915) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_915
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 916 - ((-2062241/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_916).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_917 : ((121186729/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 917, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 917, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 916, cos1215o2c k) + cos1215o2c 917 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 916) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_916
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 917 - ((-1996149/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_917).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_918 : ((1136953/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 918, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 918, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 917, cos1215o2c k) + cos1215o2c 918 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 917) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_917
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 918 - ((-7490429/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_918).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_919 : ((111853161/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 919, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 919, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 918, cos1215o2c k) + cos1215o2c 919 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 918) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_918
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 919 - ((-1841139/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_919).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_920 : ((116429867/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 920, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 920, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 919, cos1215o2c k) + cos1215o2c 920 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 919) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_919
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 920 - ((2288853/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_920).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_921 : ((7843513/625000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 921, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 921, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 920, cos1215o2c k) + cos1215o2c 921 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 920) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_920
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 921 - ((9067341/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_921).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_922 : ((33811379/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 922, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 922, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 921, cos1215o2c k) + cos1215o2c 922 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 921) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_921
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 922 - ((2437577/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_922).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_923 : ((141596997/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 923, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 923, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 922, cos1215o2c k) + cos1215o2c 923 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 922) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_922
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 923 - ((6352481/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_923).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_924 : ((35475309/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 924, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 924, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 923, cos1215o2c k) + cos1215o2c 924 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 923) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_923
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 924 - ((305239/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_924).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_925 : ((68018131/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 925, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 925, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 924, cos1215o2c k) + cos1215o2c 925 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 924) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_924
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 925 - ((-2931987/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_925).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_926 : ((126446523/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 926, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 926, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 925, cos1215o2c k) + cos1215o2c 926 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 925) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_925
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 926 - ((-9588739/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_926).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_927 : ((117114627/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 927, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 927, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 926, cos1215o2c k) + cos1215o2c 927 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 926) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_926
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 927 - ((-583181/625000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_927).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_928 : ((111904639/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 928, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 928, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 927, cos1215o2c k) + cos1215o2c 928 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 927) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_927
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 928 - ((-1302247/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_928).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_929 : ((112965373/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 929, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 929, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 928, cos1215o2c k) + cos1215o2c 929 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 928) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_928
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 929 - ((530867/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_929).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_930 : ((4794121/400000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 930, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 930, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 929, cos1215o2c k) + cos1215o2c 930 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 929) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_929
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 930 - ((1722163/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_930).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_931 : ((64863737/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 931, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 931, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 930, cos1215o2c k) + cos1215o2c 931 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 930) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_930
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 931 - ((9875449/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_931).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_932 : ((8658117/625000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 932, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 932, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 931, cos1215o2c k) + cos1215o2c 932 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 931) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_931
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 932 - ((4401699/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_932).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_933 : ((28530589/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 933, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 933, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 932, cos1215o2c k) + cos1215o2c 933 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 932) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_932
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 933 - ((4124073/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_933).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_934 : ((70207229/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 934, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 934, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 933, cos1215o2c k) + cos1215o2c 934 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 933) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_933
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 934 - ((-2237487/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_934).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_935 : ((132733251/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 935, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 935, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 934, cos1215o2c k) + cos1215o2c 935 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 934) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_934
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 935 - ((-7680207/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_935).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_936 : ((122742689/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 936, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 936, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 935, cos1215o2c k) + cos1215o2c 936 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 935) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_935
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 936 - ((-4994781/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_936).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_937 : ((114505273/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 937, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 937, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 936, cos1215o2c k) + cos1215o2c 937 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 936) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_936
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 937 - ((-64347/78125 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_937).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_938 : ((111360673/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 938, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 938, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 937, cos1215o2c k) + cos1215o2c 938 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 937) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_937
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 938 - ((-7859/25000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_938).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_939 : ((57288263/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 939, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 939, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 938, cos1215o2c k) + cos1215o2c 939 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 938) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_938
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 939 - ((3216853/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_939).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_940 : ((12284767/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 940, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 940, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 939, cos1215o2c k) + cos1215o2c 940 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 939) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_939
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 940 - ((517009/625000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_940).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_941 : ((5313381/400000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 941, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 941, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 940, cos1215o2c k) + cos1215o2c 941 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 940) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_940
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 941 - ((1997571/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_941).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_942 : ((3512929/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 942, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 942, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 941, cos1215o2c k) + cos1215o2c 942 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 941) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_941
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 942 - ((1536727/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_942).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_943 : ((71406353/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 943, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 943, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 942, cos1215o2c k) + cos1215o2c 943 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 942) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_942
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 943 - ((1148273/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_943).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_944 : ((138805753/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 944, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 944, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 943, cos1215o2c k) + cos1215o2c 944 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 943) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_943
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 944 - ((-4005953/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_944).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_945 : ((813149/62500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 945, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 945, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 944, cos1215o2c k) + cos1215o2c 945 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 944) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_944
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 945 - ((-8700913/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_945).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_946 : ((60091741/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 946, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 946, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 945, cos1215o2c k) + cos1215o2c 946 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 945) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_945
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 946 - ((-4959679/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_946).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_947 : ((11299577/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 947, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 947, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 946, cos1215o2c k) + cos1215o2c 947 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 946) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_946
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 947 - ((-898339/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_947).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_948 : ((55697471/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 948, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 948, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 947, cos1215o2c k) + cos1215o2c 948 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 947) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_947
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 948 - ((-399957/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_948).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_949 : ((23201909/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 949, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 949, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 948, cos1215o2c k) + cos1215o2c 949 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 948) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_948
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 949 - ((4615603/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_949).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_950 : ((25001537/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 950, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 950, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 949, cos1215o2c k) + cos1215o2c 950 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 949) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_949
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 950 - ((449957/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_950).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_951 : ((67415311/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 951, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 951, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 950, cos1215o2c k) + cos1215o2c 951 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 950) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_950
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 951 - ((9823937/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_951).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_952 : ((70802417/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 952, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 952, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 951, cos1215o2c k) + cos1215o2c 952 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 951) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_951
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 952 - ((1693803/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_952).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_953 : ((71333773/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 953, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 953, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 952, cos1215o2c k) + cos1215o2c 953 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 952) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_952
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 953 - ((33241/312500 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_953).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_954 : ((17200849/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 954, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 954, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 953, cos1215o2c k) + cos1215o2c 954 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 953) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_953
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 954 - ((-2529877/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_954).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_955 : ((128410071/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 955, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 955, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 954, cos1215o2c k) + cos1215o2c 955 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 954) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_954
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 955 - ((-9195721/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_955).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_956 : ((59338497/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 956, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 956, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 955, cos1215o2c k) + cos1215o2c 956 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 955) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_955
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 956 - ((-9732077/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_956).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_957 : ((112205467/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 957, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 957, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 956, cos1215o2c k) + cos1215o2c 957 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 956) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_956
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 957 - ((-6470527/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_957).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_958 : ((892101/80000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 958, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 958, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 957, cos1215o2c k) + cos1215o2c 958 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 957) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_957
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 958 - ((-345921/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_958).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_959 : ((116862111/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 959, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 959, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 958, cos1215o2c k) + cos1215o2c 959 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 958) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_958
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 959 - ((2675243/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_959).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_960 : ((126173149/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 960, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 960, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 959, cos1215o2c k) + cos1215o2c 960 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 959) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_959
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 960 - ((4656019/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_960).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_961 : ((135837501/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 961, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 961, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 960, cos1215o2c k) + cos1215o2c 961 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 960) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_960
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 961 - ((1208169/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_961).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_962 : ((2220641/156250 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 962, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 962, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 961, cos1215o2c k) + cos1215o2c 962 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 961) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_961
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 962 - ((6284523/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_962).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_963 : ((142603529/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 963, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 963, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 962, cos1215o2c k) + cos1215o2c 963 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 962) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_962
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 963 - ((96701/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_963).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_964 : ((68552393/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 964, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 964, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 963, cos1215o2c k) + cos1215o2c 964 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 963) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_963
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 964 - ((-5497743/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_964).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_965 : ((63870273/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 965, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 965, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 964, cos1215o2c k) + cos1215o2c 965 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 964) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_964
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 965 - ((-234081/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_965).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_966 : ((118102911/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 966, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 966, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 965, cos1215o2c k) + cos1215o2c 966 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 965) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_965
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 966 - ((-1927327/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_966).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_967 : ((111877369/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 967, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 967, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 966, cos1215o2c k) + cos1215o2c 967 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 966) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_966
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 967 - ((-3112271/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_967).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_968 : ((22287377/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 968, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 968, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 967, cos1215o2c k) + cos1215o2c 968 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 967) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_967
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 968 - ((-109871/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_968).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_969 : ((7309003/625000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 969, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 969, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 968, cos1215o2c k) + cos1215o2c 969 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 968) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_968
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 969 - ((5508163/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_969).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_970 : ((126298917/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 970, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 970, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 969, cos1215o2c k) + cos1215o2c 970 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 969) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_969
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 970 - ((9355869/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_970).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_971 : ((135948609/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 971, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 971, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 970, cos1215o2c k) + cos1215o2c 971 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 970) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_970
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 971 - ((2412673/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_971).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_972 : ((28447647/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 972, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 972, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 971, cos1215o2c k) + cos1215o2c 972 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 971) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_971
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 972 - ((3145313/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_972).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_973 : ((142794099/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 973, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 973, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 972, cos1215o2c k) + cos1215o2c 973 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 972) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_972
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 973 - ((8701/156250 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_973).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_974 : ((137410513/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 974, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 974, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 973, cos1215o2c k) + cos1215o2c 974 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 973) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_973
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 974 - ((-2691293/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_974).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_975 : ((5124777/400000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 975, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 975, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 974, cos1215o2c k) + cos1215o2c 975 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 974) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_974
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 975 - ((-1161261/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_975).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_976 : ((29603463/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 976, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 976, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 975, cos1215o2c k) + cos1215o2c 976 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 975) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_975
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 976 - ((-9704573/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_976).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_977 : ((55966339/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 977, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 977, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 976, cos1215o2c k) + cos1215o2c 977 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 976) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_976
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 977 - ((-3240087/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_977).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_978 : ((111097589/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 978, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 978, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 977, cos1215o2c k) + cos1215o2c 978 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 977) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_977
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 978 - ((-834089/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_978).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_979 : ((1452691/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 979, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 979, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 978, cos1215o2c k) + cos1215o2c 979 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 978) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_978
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 979 - ((5118691/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_979).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_980 : ((125372523/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 980, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 980, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 979, cos1215o2c k) + cos1215o2c 980 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 979) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_979
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 980 - ((9158243/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_980).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_981 : ((67579689/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 981, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 981, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 980, cos1215o2c k) + cos1215o2c 981 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 980) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_980
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 981 - ((1957571/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_981).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_982 : ((141941519/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 982, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 982, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 981, cos1215o2c k) + cos1215o2c 982 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 981) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_981
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 982 - ((6783141/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_982).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_983 : ((71604309/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 983, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 983, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 982, cos1215o2c k) + cos1215o2c 983 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 982) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_982
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 983 - ((1268099/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_983).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_984 : ((13849701/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 984, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 984, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 983, cos1215o2c k) + cos1215o2c 984 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 983) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_983
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 984 - ((-294413/625000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_984).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_985 : ((129549759/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 985, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 985, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 984, cos1215o2c k) + cos1215o2c 985 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 984) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_984
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 985 - ((-8946251/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_985).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_986 : ((186978/15625 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 986, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 986, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 985, cos1215o2c k) + cos1215o2c 986 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 985) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_985
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 986 - ((-9882839/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_986).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_987 : ((11247919/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 987, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 987, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 986, cos1215o2c k) + cos1215o2c 987 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 986) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_986
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 987 - ((-718573/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_987).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_988 : ((55311531/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 988, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 988, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 987, cos1215o2c k) + cos1215o2c 988 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 987) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_987
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 988 - ((-231891/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_988).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_989 : ((11477271/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 989, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 989, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 988, cos1215o2c k) + cos1215o2c 989 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 988) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_988
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 989 - ((518831/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_989).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_990 : ((197449/16000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 990, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 990, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 989, cos1215o2c k) + cos1215o2c 990 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 989) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_989
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 990 - ((1726783/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_990).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_991 : ((66684477/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 991, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 991, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 990, cos1215o2c k) + cos1215o2c 991 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 990) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_990
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 991 - ((9964329/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_991).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_992 : ((17629287/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 992, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 992, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 991, cos1215o2c k) + cos1215o2c 992 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 991) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_991
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 992 - ((3833171/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_992).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_993 : ((143618849/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 993, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 993, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 992, cos1215o2c k) + cos1215o2c 993 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 992) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_992
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 993 - ((2585553/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_993).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_994 : ((140189029/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 994, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 994, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 993, cos1215o2c k) + cos1215o2c 994 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 993) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_993
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 994 - ((-171441/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_994).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_995 : ((32997847/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 995, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 995, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 994, cos1215o2c k) + cos1215o2c 995 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 994) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_994
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 995 - ((-8196641/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_995).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_996 : ((30497597/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 996, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 996, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 995, cos1215o2c k) + cos1215o2c 996 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 995) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_995
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 996 - ((-1 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_996).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_997 : ((113792267/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 997, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 997, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 996, cos1215o2c k) + cos1215o2c 997 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 996) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_996
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 997 - ((-8197121/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_997).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_998 : ((22068909/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 998, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 998, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 997, cos1215o2c k) + cos1215o2c 998 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 997) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_997
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 998 - ((-1723361/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_998).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_999 : ((56440361/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 999, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 999, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 998, cos1215o2c k) + cos1215o2c 999 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 998) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_998
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 999 - ((2537177/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_999).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1215o2_1000 : ((60243149/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 1000, cos1215o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 1000, cos1215o2c k)
      = (∑ k ∈ Finset.Icc 11 999, cos1215o2c k) + cos1215o2c 1000 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 999) (by norm_num) cos1215o2c
    simpa using h
  have hprev := psum1215o2_999
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1215o2c 1000 - ((475411/625000 : ℚ) : ℝ) :=
    (abs_le.mp cos1215o2_br_1000).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

set_option maxHeartbeats 6400000 in
set_option maxRecDepth 32768 in
theorem psum1215o2_floor : ∀ j : ℕ, 11 ≤ j → j ≤ 1000 →
    ((0 : ℚ) : ℝ) ≤ ∑ k ∈ Finset.Icc 11 j, cos1215o2c k := by
  intro j hj1 hj2
  interval_cases j
  · exact le_trans (by norm_num) psum1215o2_11
  · exact le_trans (by norm_num) psum1215o2_12
  · exact le_trans (by norm_num) psum1215o2_13
  · exact le_trans (by norm_num) psum1215o2_14
  · exact le_trans (by norm_num) psum1215o2_15
  · exact le_trans (by norm_num) psum1215o2_16
  · exact le_trans (by norm_num) psum1215o2_17
  · exact le_trans (by norm_num) psum1215o2_18
  · exact le_trans (by norm_num) psum1215o2_19
  · exact le_trans (by norm_num) psum1215o2_20
  · exact le_trans (by norm_num) psum1215o2_21
  · exact le_trans (by norm_num) psum1215o2_22
  · exact le_trans (by norm_num) psum1215o2_23
  · exact le_trans (by norm_num) psum1215o2_24
  · exact le_trans (by norm_num) psum1215o2_25
  · exact le_trans (by norm_num) psum1215o2_26
  · exact le_trans (by norm_num) psum1215o2_27
  · exact le_trans (by norm_num) psum1215o2_28
  · exact le_trans (by norm_num) psum1215o2_29
  · exact le_trans (by norm_num) psum1215o2_30
  · exact le_trans (by norm_num) psum1215o2_31
  · exact le_trans (by norm_num) psum1215o2_32
  · exact le_trans (by norm_num) psum1215o2_33
  · exact le_trans (by norm_num) psum1215o2_34
  · exact le_trans (by norm_num) psum1215o2_35
  · exact le_trans (by norm_num) psum1215o2_36
  · exact le_trans (by norm_num) psum1215o2_37
  · exact le_trans (by norm_num) psum1215o2_38
  · exact le_trans (by norm_num) psum1215o2_39
  · exact le_trans (by norm_num) psum1215o2_40
  · exact le_trans (by norm_num) psum1215o2_41
  · exact le_trans (by norm_num) psum1215o2_42
  · exact le_trans (by norm_num) psum1215o2_43
  · exact le_trans (by norm_num) psum1215o2_44
  · exact le_trans (by norm_num) psum1215o2_45
  · exact le_trans (by norm_num) psum1215o2_46
  · exact le_trans (by norm_num) psum1215o2_47
  · exact le_trans (by norm_num) psum1215o2_48
  · exact le_trans (by norm_num) psum1215o2_49
  · exact le_trans (by norm_num) psum1215o2_50
  · exact le_trans (by norm_num) psum1215o2_51
  · exact le_trans (by norm_num) psum1215o2_52
  · exact le_trans (by norm_num) psum1215o2_53
  · exact le_trans (by norm_num) psum1215o2_54
  · exact le_trans (by norm_num) psum1215o2_55
  · exact le_trans (by norm_num) psum1215o2_56
  · exact le_trans (by norm_num) psum1215o2_57
  · exact le_trans (by norm_num) psum1215o2_58
  · exact le_trans (by norm_num) psum1215o2_59
  · exact le_trans (by norm_num) psum1215o2_60
  · exact le_trans (by norm_num) psum1215o2_61
  · exact le_trans (by norm_num) psum1215o2_62
  · exact le_trans (by norm_num) psum1215o2_63
  · exact le_trans (by norm_num) psum1215o2_64
  · exact le_trans (by norm_num) psum1215o2_65
  · exact le_trans (by norm_num) psum1215o2_66
  · exact le_trans (by norm_num) psum1215o2_67
  · exact le_trans (by norm_num) psum1215o2_68
  · exact le_trans (by norm_num) psum1215o2_69
  · exact le_trans (by norm_num) psum1215o2_70
  · exact le_trans (by norm_num) psum1215o2_71
  · exact le_trans (by norm_num) psum1215o2_72
  · exact le_trans (by norm_num) psum1215o2_73
  · exact le_trans (by norm_num) psum1215o2_74
  · exact le_trans (by norm_num) psum1215o2_75
  · exact le_trans (by norm_num) psum1215o2_76
  · exact le_trans (by norm_num) psum1215o2_77
  · exact le_trans (by norm_num) psum1215o2_78
  · exact le_trans (by norm_num) psum1215o2_79
  · exact le_trans (by norm_num) psum1215o2_80
  · exact le_trans (by norm_num) psum1215o2_81
  · exact le_trans (by norm_num) psum1215o2_82
  · exact le_trans (by norm_num) psum1215o2_83
  · exact le_trans (by norm_num) psum1215o2_84
  · exact le_trans (by norm_num) psum1215o2_85
  · exact le_trans (by norm_num) psum1215o2_86
  · exact le_trans (by norm_num) psum1215o2_87
  · exact le_trans (by norm_num) psum1215o2_88
  · exact le_trans (by norm_num) psum1215o2_89
  · exact le_trans (by norm_num) psum1215o2_90
  · exact le_trans (by norm_num) psum1215o2_91
  · exact le_trans (by norm_num) psum1215o2_92
  · exact le_trans (by norm_num) psum1215o2_93
  · exact le_trans (by norm_num) psum1215o2_94
  · exact le_trans (by norm_num) psum1215o2_95
  · exact le_trans (by norm_num) psum1215o2_96
  · exact le_trans (by norm_num) psum1215o2_97
  · exact le_trans (by norm_num) psum1215o2_98
  · exact le_trans (by norm_num) psum1215o2_99
  · exact le_trans (by norm_num) psum1215o2_100
  · exact le_trans (by norm_num) psum1215o2_101
  · exact le_trans (by norm_num) psum1215o2_102
  · exact le_trans (by norm_num) psum1215o2_103
  · exact le_trans (by norm_num) psum1215o2_104
  · exact le_trans (by norm_num) psum1215o2_105
  · exact le_trans (by norm_num) psum1215o2_106
  · exact le_trans (by norm_num) psum1215o2_107
  · exact le_trans (by norm_num) psum1215o2_108
  · exact le_trans (by norm_num) psum1215o2_109
  · exact le_trans (by norm_num) psum1215o2_110
  · exact le_trans (by norm_num) psum1215o2_111
  · exact le_trans (by norm_num) psum1215o2_112
  · exact le_trans (by norm_num) psum1215o2_113
  · exact le_trans (by norm_num) psum1215o2_114
  · exact le_trans (by norm_num) psum1215o2_115
  · exact le_trans (by norm_num) psum1215o2_116
  · exact le_trans (by norm_num) psum1215o2_117
  · exact le_trans (by norm_num) psum1215o2_118
  · exact le_trans (by norm_num) psum1215o2_119
  · exact le_trans (by norm_num) psum1215o2_120
  · exact le_trans (by norm_num) psum1215o2_121
  · exact le_trans (by norm_num) psum1215o2_122
  · exact le_trans (by norm_num) psum1215o2_123
  · exact le_trans (by norm_num) psum1215o2_124
  · exact le_trans (by norm_num) psum1215o2_125
  · exact le_trans (by norm_num) psum1215o2_126
  · exact le_trans (by norm_num) psum1215o2_127
  · exact le_trans (by norm_num) psum1215o2_128
  · exact le_trans (by norm_num) psum1215o2_129
  · exact le_trans (by norm_num) psum1215o2_130
  · exact le_trans (by norm_num) psum1215o2_131
  · exact le_trans (by norm_num) psum1215o2_132
  · exact le_trans (by norm_num) psum1215o2_133
  · exact le_trans (by norm_num) psum1215o2_134
  · exact le_trans (by norm_num) psum1215o2_135
  · exact le_trans (by norm_num) psum1215o2_136
  · exact le_trans (by norm_num) psum1215o2_137
  · exact le_trans (by norm_num) psum1215o2_138
  · exact le_trans (by norm_num) psum1215o2_139
  · exact le_trans (by norm_num) psum1215o2_140
  · exact le_trans (by norm_num) psum1215o2_141
  · exact le_trans (by norm_num) psum1215o2_142
  · exact le_trans (by norm_num) psum1215o2_143
  · exact le_trans (by norm_num) psum1215o2_144
  · exact le_trans (by norm_num) psum1215o2_145
  · exact le_trans (by norm_num) psum1215o2_146
  · exact le_trans (by norm_num) psum1215o2_147
  · exact le_trans (by norm_num) psum1215o2_148
  · exact le_trans (by norm_num) psum1215o2_149
  · exact le_trans (by norm_num) psum1215o2_150
  · exact le_trans (by norm_num) psum1215o2_151
  · exact le_trans (by norm_num) psum1215o2_152
  · exact le_trans (by norm_num) psum1215o2_153
  · exact le_trans (by norm_num) psum1215o2_154
  · exact le_trans (by norm_num) psum1215o2_155
  · exact le_trans (by norm_num) psum1215o2_156
  · exact le_trans (by norm_num) psum1215o2_157
  · exact le_trans (by norm_num) psum1215o2_158
  · exact le_trans (by norm_num) psum1215o2_159
  · exact le_trans (by norm_num) psum1215o2_160
  · exact le_trans (by norm_num) psum1215o2_161
  · exact le_trans (by norm_num) psum1215o2_162
  · exact le_trans (by norm_num) psum1215o2_163
  · exact le_trans (by norm_num) psum1215o2_164
  · exact le_trans (by norm_num) psum1215o2_165
  · exact le_trans (by norm_num) psum1215o2_166
  · exact le_trans (by norm_num) psum1215o2_167
  · exact le_trans (by norm_num) psum1215o2_168
  · exact le_trans (by norm_num) psum1215o2_169
  · exact le_trans (by norm_num) psum1215o2_170
  · exact le_trans (by norm_num) psum1215o2_171
  · exact le_trans (by norm_num) psum1215o2_172
  · exact le_trans (by norm_num) psum1215o2_173
  · exact le_trans (by norm_num) psum1215o2_174
  · exact le_trans (by norm_num) psum1215o2_175
  · exact le_trans (by norm_num) psum1215o2_176
  · exact le_trans (by norm_num) psum1215o2_177
  · exact le_trans (by norm_num) psum1215o2_178
  · exact le_trans (by norm_num) psum1215o2_179
  · exact le_trans (by norm_num) psum1215o2_180
  · exact le_trans (by norm_num) psum1215o2_181
  · exact le_trans (by norm_num) psum1215o2_182
  · exact le_trans (by norm_num) psum1215o2_183
  · exact le_trans (by norm_num) psum1215o2_184
  · exact le_trans (by norm_num) psum1215o2_185
  · exact le_trans (by norm_num) psum1215o2_186
  · exact le_trans (by norm_num) psum1215o2_187
  · exact le_trans (by norm_num) psum1215o2_188
  · exact le_trans (by norm_num) psum1215o2_189
  · exact le_trans (by norm_num) psum1215o2_190
  · exact le_trans (by norm_num) psum1215o2_191
  · exact le_trans (by norm_num) psum1215o2_192
  · exact le_trans (by norm_num) psum1215o2_193
  · exact le_trans (by norm_num) psum1215o2_194
  · exact le_trans (by norm_num) psum1215o2_195
  · exact le_trans (by norm_num) psum1215o2_196
  · exact le_trans (by norm_num) psum1215o2_197
  · exact le_trans (by norm_num) psum1215o2_198
  · exact le_trans (by norm_num) psum1215o2_199
  · exact le_trans (by norm_num) psum1215o2_200
  · exact le_trans (by norm_num) psum1215o2_201
  · exact le_trans (by norm_num) psum1215o2_202
  · exact le_trans (by norm_num) psum1215o2_203
  · exact le_trans (by norm_num) psum1215o2_204
  · exact le_trans (by norm_num) psum1215o2_205
  · exact le_trans (by norm_num) psum1215o2_206
  · exact le_trans (by norm_num) psum1215o2_207
  · exact le_trans (by norm_num) psum1215o2_208
  · exact le_trans (by norm_num) psum1215o2_209
  · exact le_trans (by norm_num) psum1215o2_210
  · exact le_trans (by norm_num) psum1215o2_211
  · exact le_trans (by norm_num) psum1215o2_212
  · exact le_trans (by norm_num) psum1215o2_213
  · exact le_trans (by norm_num) psum1215o2_214
  · exact le_trans (by norm_num) psum1215o2_215
  · exact le_trans (by norm_num) psum1215o2_216
  · exact le_trans (by norm_num) psum1215o2_217
  · exact le_trans (by norm_num) psum1215o2_218
  · exact le_trans (by norm_num) psum1215o2_219
  · exact le_trans (by norm_num) psum1215o2_220
  · exact le_trans (by norm_num) psum1215o2_221
  · exact le_trans (by norm_num) psum1215o2_222
  · exact le_trans (by norm_num) psum1215o2_223
  · exact le_trans (by norm_num) psum1215o2_224
  · exact le_trans (by norm_num) psum1215o2_225
  · exact le_trans (by norm_num) psum1215o2_226
  · exact le_trans (by norm_num) psum1215o2_227
  · exact le_trans (by norm_num) psum1215o2_228
  · exact le_trans (by norm_num) psum1215o2_229
  · exact le_trans (by norm_num) psum1215o2_230
  · exact le_trans (by norm_num) psum1215o2_231
  · exact le_trans (by norm_num) psum1215o2_232
  · exact le_trans (by norm_num) psum1215o2_233
  · exact le_trans (by norm_num) psum1215o2_234
  · exact le_trans (by norm_num) psum1215o2_235
  · exact le_trans (by norm_num) psum1215o2_236
  · exact le_trans (by norm_num) psum1215o2_237
  · exact le_trans (by norm_num) psum1215o2_238
  · exact le_trans (by norm_num) psum1215o2_239
  · exact le_trans (by norm_num) psum1215o2_240
  · exact le_trans (by norm_num) psum1215o2_241
  · exact le_trans (by norm_num) psum1215o2_242
  · exact le_trans (by norm_num) psum1215o2_243
  · exact le_trans (by norm_num) psum1215o2_244
  · exact le_trans (by norm_num) psum1215o2_245
  · exact le_trans (by norm_num) psum1215o2_246
  · exact le_trans (by norm_num) psum1215o2_247
  · exact le_trans (by norm_num) psum1215o2_248
  · exact le_trans (by norm_num) psum1215o2_249
  · exact le_trans (by norm_num) psum1215o2_250
  · exact le_trans (by norm_num) psum1215o2_251
  · exact le_trans (by norm_num) psum1215o2_252
  · exact le_trans (by norm_num) psum1215o2_253
  · exact le_trans (by norm_num) psum1215o2_254
  · exact le_trans (by norm_num) psum1215o2_255
  · exact le_trans (by norm_num) psum1215o2_256
  · exact le_trans (by norm_num) psum1215o2_257
  · exact le_trans (by norm_num) psum1215o2_258
  · exact le_trans (by norm_num) psum1215o2_259
  · exact le_trans (by norm_num) psum1215o2_260
  · exact le_trans (by norm_num) psum1215o2_261
  · exact le_trans (by norm_num) psum1215o2_262
  · exact le_trans (by norm_num) psum1215o2_263
  · exact le_trans (by norm_num) psum1215o2_264
  · exact le_trans (by norm_num) psum1215o2_265
  · exact le_trans (by norm_num) psum1215o2_266
  · exact le_trans (by norm_num) psum1215o2_267
  · exact le_trans (by norm_num) psum1215o2_268
  · exact le_trans (by norm_num) psum1215o2_269
  · exact le_trans (by norm_num) psum1215o2_270
  · exact le_trans (by norm_num) psum1215o2_271
  · exact le_trans (by norm_num) psum1215o2_272
  · exact le_trans (by norm_num) psum1215o2_273
  · exact le_trans (by norm_num) psum1215o2_274
  · exact le_trans (by norm_num) psum1215o2_275
  · exact le_trans (by norm_num) psum1215o2_276
  · exact le_trans (by norm_num) psum1215o2_277
  · exact le_trans (by norm_num) psum1215o2_278
  · exact le_trans (by norm_num) psum1215o2_279
  · exact le_trans (by norm_num) psum1215o2_280
  · exact le_trans (by norm_num) psum1215o2_281
  · exact le_trans (by norm_num) psum1215o2_282
  · exact le_trans (by norm_num) psum1215o2_283
  · exact le_trans (by norm_num) psum1215o2_284
  · exact le_trans (by norm_num) psum1215o2_285
  · exact le_trans (by norm_num) psum1215o2_286
  · exact le_trans (by norm_num) psum1215o2_287
  · exact le_trans (by norm_num) psum1215o2_288
  · exact le_trans (by norm_num) psum1215o2_289
  · exact le_trans (by norm_num) psum1215o2_290
  · exact le_trans (by norm_num) psum1215o2_291
  · exact le_trans (by norm_num) psum1215o2_292
  · exact le_trans (by norm_num) psum1215o2_293
  · exact le_trans (by norm_num) psum1215o2_294
  · exact le_trans (by norm_num) psum1215o2_295
  · exact le_trans (by norm_num) psum1215o2_296
  · exact le_trans (by norm_num) psum1215o2_297
  · exact le_trans (by norm_num) psum1215o2_298
  · exact le_trans (by norm_num) psum1215o2_299
  · exact le_trans (by norm_num) psum1215o2_300
  · exact le_trans (by norm_num) psum1215o2_301
  · exact le_trans (by norm_num) psum1215o2_302
  · exact le_trans (by norm_num) psum1215o2_303
  · exact le_trans (by norm_num) psum1215o2_304
  · exact le_trans (by norm_num) psum1215o2_305
  · exact le_trans (by norm_num) psum1215o2_306
  · exact le_trans (by norm_num) psum1215o2_307
  · exact le_trans (by norm_num) psum1215o2_308
  · exact le_trans (by norm_num) psum1215o2_309
  · exact le_trans (by norm_num) psum1215o2_310
  · exact le_trans (by norm_num) psum1215o2_311
  · exact le_trans (by norm_num) psum1215o2_312
  · exact le_trans (by norm_num) psum1215o2_313
  · exact le_trans (by norm_num) psum1215o2_314
  · exact le_trans (by norm_num) psum1215o2_315
  · exact le_trans (by norm_num) psum1215o2_316
  · exact le_trans (by norm_num) psum1215o2_317
  · exact le_trans (by norm_num) psum1215o2_318
  · exact le_trans (by norm_num) psum1215o2_319
  · exact le_trans (by norm_num) psum1215o2_320
  · exact le_trans (by norm_num) psum1215o2_321
  · exact le_trans (by norm_num) psum1215o2_322
  · exact le_trans (by norm_num) psum1215o2_323
  · exact le_trans (by norm_num) psum1215o2_324
  · exact le_trans (by norm_num) psum1215o2_325
  · exact le_trans (by norm_num) psum1215o2_326
  · exact le_trans (by norm_num) psum1215o2_327
  · exact le_trans (by norm_num) psum1215o2_328
  · exact le_trans (by norm_num) psum1215o2_329
  · exact le_trans (by norm_num) psum1215o2_330
  · exact le_trans (by norm_num) psum1215o2_331
  · exact le_trans (by norm_num) psum1215o2_332
  · exact le_trans (by norm_num) psum1215o2_333
  · exact le_trans (by norm_num) psum1215o2_334
  · exact le_trans (by norm_num) psum1215o2_335
  · exact le_trans (by norm_num) psum1215o2_336
  · exact le_trans (by norm_num) psum1215o2_337
  · exact le_trans (by norm_num) psum1215o2_338
  · exact le_trans (by norm_num) psum1215o2_339
  · exact le_trans (by norm_num) psum1215o2_340
  · exact le_trans (by norm_num) psum1215o2_341
  · exact le_trans (by norm_num) psum1215o2_342
  · exact le_trans (by norm_num) psum1215o2_343
  · exact le_trans (by norm_num) psum1215o2_344
  · exact le_trans (by norm_num) psum1215o2_345
  · exact le_trans (by norm_num) psum1215o2_346
  · exact le_trans (by norm_num) psum1215o2_347
  · exact le_trans (by norm_num) psum1215o2_348
  · exact le_trans (by norm_num) psum1215o2_349
  · exact le_trans (by norm_num) psum1215o2_350
  · exact le_trans (by norm_num) psum1215o2_351
  · exact le_trans (by norm_num) psum1215o2_352
  · exact le_trans (by norm_num) psum1215o2_353
  · exact le_trans (by norm_num) psum1215o2_354
  · exact le_trans (by norm_num) psum1215o2_355
  · exact le_trans (by norm_num) psum1215o2_356
  · exact le_trans (by norm_num) psum1215o2_357
  · exact le_trans (by norm_num) psum1215o2_358
  · exact le_trans (by norm_num) psum1215o2_359
  · exact le_trans (by norm_num) psum1215o2_360
  · exact le_trans (by norm_num) psum1215o2_361
  · exact le_trans (by norm_num) psum1215o2_362
  · exact le_trans (by norm_num) psum1215o2_363
  · exact le_trans (by norm_num) psum1215o2_364
  · exact le_trans (by norm_num) psum1215o2_365
  · exact le_trans (by norm_num) psum1215o2_366
  · exact le_trans (by norm_num) psum1215o2_367
  · exact le_trans (by norm_num) psum1215o2_368
  · exact le_trans (by norm_num) psum1215o2_369
  · exact le_trans (by norm_num) psum1215o2_370
  · exact le_trans (by norm_num) psum1215o2_371
  · exact le_trans (by norm_num) psum1215o2_372
  · exact le_trans (by norm_num) psum1215o2_373
  · exact le_trans (by norm_num) psum1215o2_374
  · exact le_trans (by norm_num) psum1215o2_375
  · exact le_trans (by norm_num) psum1215o2_376
  · exact le_trans (by norm_num) psum1215o2_377
  · exact le_trans (by norm_num) psum1215o2_378
  · exact le_trans (by norm_num) psum1215o2_379
  · exact le_trans (by norm_num) psum1215o2_380
  · exact le_trans (by norm_num) psum1215o2_381
  · exact le_trans (by norm_num) psum1215o2_382
  · exact le_trans (by norm_num) psum1215o2_383
  · exact le_trans (by norm_num) psum1215o2_384
  · exact le_trans (by norm_num) psum1215o2_385
  · exact le_trans (by norm_num) psum1215o2_386
  · exact le_trans (by norm_num) psum1215o2_387
  · exact le_trans (by norm_num) psum1215o2_388
  · exact le_trans (by norm_num) psum1215o2_389
  · exact le_trans (by norm_num) psum1215o2_390
  · exact le_trans (by norm_num) psum1215o2_391
  · exact le_trans (by norm_num) psum1215o2_392
  · exact le_trans (by norm_num) psum1215o2_393
  · exact le_trans (by norm_num) psum1215o2_394
  · exact le_trans (by norm_num) psum1215o2_395
  · exact le_trans (by norm_num) psum1215o2_396
  · exact le_trans (by norm_num) psum1215o2_397
  · exact le_trans (by norm_num) psum1215o2_398
  · exact le_trans (by norm_num) psum1215o2_399
  · exact le_trans (by norm_num) psum1215o2_400
  · exact le_trans (by norm_num) psum1215o2_401
  · exact le_trans (by norm_num) psum1215o2_402
  · exact le_trans (by norm_num) psum1215o2_403
  · exact le_trans (by norm_num) psum1215o2_404
  · exact le_trans (by norm_num) psum1215o2_405
  · exact le_trans (by norm_num) psum1215o2_406
  · exact le_trans (by norm_num) psum1215o2_407
  · exact le_trans (by norm_num) psum1215o2_408
  · exact le_trans (by norm_num) psum1215o2_409
  · exact le_trans (by norm_num) psum1215o2_410
  · exact le_trans (by norm_num) psum1215o2_411
  · exact le_trans (by norm_num) psum1215o2_412
  · exact le_trans (by norm_num) psum1215o2_413
  · exact le_trans (by norm_num) psum1215o2_414
  · exact le_trans (by norm_num) psum1215o2_415
  · exact le_trans (by norm_num) psum1215o2_416
  · exact le_trans (by norm_num) psum1215o2_417
  · exact le_trans (by norm_num) psum1215o2_418
  · exact le_trans (by norm_num) psum1215o2_419
  · exact le_trans (by norm_num) psum1215o2_420
  · exact le_trans (by norm_num) psum1215o2_421
  · exact le_trans (by norm_num) psum1215o2_422
  · exact le_trans (by norm_num) psum1215o2_423
  · exact le_trans (by norm_num) psum1215o2_424
  · exact le_trans (by norm_num) psum1215o2_425
  · exact le_trans (by norm_num) psum1215o2_426
  · exact le_trans (by norm_num) psum1215o2_427
  · exact le_trans (by norm_num) psum1215o2_428
  · exact le_trans (by norm_num) psum1215o2_429
  · exact le_trans (by norm_num) psum1215o2_430
  · exact le_trans (by norm_num) psum1215o2_431
  · exact le_trans (by norm_num) psum1215o2_432
  · exact le_trans (by norm_num) psum1215o2_433
  · exact le_trans (by norm_num) psum1215o2_434
  · exact le_trans (by norm_num) psum1215o2_435
  · exact le_trans (by norm_num) psum1215o2_436
  · exact le_trans (by norm_num) psum1215o2_437
  · exact le_trans (by norm_num) psum1215o2_438
  · exact le_trans (by norm_num) psum1215o2_439
  · exact le_trans (by norm_num) psum1215o2_440
  · exact le_trans (by norm_num) psum1215o2_441
  · exact le_trans (by norm_num) psum1215o2_442
  · exact le_trans (by norm_num) psum1215o2_443
  · exact le_trans (by norm_num) psum1215o2_444
  · exact le_trans (by norm_num) psum1215o2_445
  · exact le_trans (by norm_num) psum1215o2_446
  · exact le_trans (by norm_num) psum1215o2_447
  · exact le_trans (by norm_num) psum1215o2_448
  · exact le_trans (by norm_num) psum1215o2_449
  · exact le_trans (by norm_num) psum1215o2_450
  · exact le_trans (by norm_num) psum1215o2_451
  · exact le_trans (by norm_num) psum1215o2_452
  · exact le_trans (by norm_num) psum1215o2_453
  · exact le_trans (by norm_num) psum1215o2_454
  · exact le_trans (by norm_num) psum1215o2_455
  · exact le_trans (by norm_num) psum1215o2_456
  · exact le_trans (by norm_num) psum1215o2_457
  · exact le_trans (by norm_num) psum1215o2_458
  · exact le_trans (by norm_num) psum1215o2_459
  · exact le_trans (by norm_num) psum1215o2_460
  · exact le_trans (by norm_num) psum1215o2_461
  · exact le_trans (by norm_num) psum1215o2_462
  · exact le_trans (by norm_num) psum1215o2_463
  · exact le_trans (by norm_num) psum1215o2_464
  · exact le_trans (by norm_num) psum1215o2_465
  · exact le_trans (by norm_num) psum1215o2_466
  · exact le_trans (by norm_num) psum1215o2_467
  · exact le_trans (by norm_num) psum1215o2_468
  · exact le_trans (by norm_num) psum1215o2_469
  · exact le_trans (by norm_num) psum1215o2_470
  · exact le_trans (by norm_num) psum1215o2_471
  · exact le_trans (by norm_num) psum1215o2_472
  · exact le_trans (by norm_num) psum1215o2_473
  · exact le_trans (by norm_num) psum1215o2_474
  · exact le_trans (by norm_num) psum1215o2_475
  · exact le_trans (by norm_num) psum1215o2_476
  · exact le_trans (by norm_num) psum1215o2_477
  · exact le_trans (by norm_num) psum1215o2_478
  · exact le_trans (by norm_num) psum1215o2_479
  · exact le_trans (by norm_num) psum1215o2_480
  · exact le_trans (by norm_num) psum1215o2_481
  · exact le_trans (by norm_num) psum1215o2_482
  · exact le_trans (by norm_num) psum1215o2_483
  · exact le_trans (by norm_num) psum1215o2_484
  · exact le_trans (by norm_num) psum1215o2_485
  · exact le_trans (by norm_num) psum1215o2_486
  · exact le_trans (by norm_num) psum1215o2_487
  · exact le_trans (by norm_num) psum1215o2_488
  · exact le_trans (by norm_num) psum1215o2_489
  · exact le_trans (by norm_num) psum1215o2_490
  · exact le_trans (by norm_num) psum1215o2_491
  · exact le_trans (by norm_num) psum1215o2_492
  · exact le_trans (by norm_num) psum1215o2_493
  · exact le_trans (by norm_num) psum1215o2_494
  · exact le_trans (by norm_num) psum1215o2_495
  · exact le_trans (by norm_num) psum1215o2_496
  · exact le_trans (by norm_num) psum1215o2_497
  · exact le_trans (by norm_num) psum1215o2_498
  · exact le_trans (by norm_num) psum1215o2_499
  · exact le_trans (by norm_num) psum1215o2_500
  · exact le_trans (by norm_num) psum1215o2_501
  · exact le_trans (by norm_num) psum1215o2_502
  · exact le_trans (by norm_num) psum1215o2_503
  · exact le_trans (by norm_num) psum1215o2_504
  · exact le_trans (by norm_num) psum1215o2_505
  · exact le_trans (by norm_num) psum1215o2_506
  · exact le_trans (by norm_num) psum1215o2_507
  · exact le_trans (by norm_num) psum1215o2_508
  · exact le_trans (by norm_num) psum1215o2_509
  · exact le_trans (by norm_num) psum1215o2_510
  · exact le_trans (by norm_num) psum1215o2_511
  · exact le_trans (by norm_num) psum1215o2_512
  · exact le_trans (by norm_num) psum1215o2_513
  · exact le_trans (by norm_num) psum1215o2_514
  · exact le_trans (by norm_num) psum1215o2_515
  · exact le_trans (by norm_num) psum1215o2_516
  · exact le_trans (by norm_num) psum1215o2_517
  · exact le_trans (by norm_num) psum1215o2_518
  · exact le_trans (by norm_num) psum1215o2_519
  · exact le_trans (by norm_num) psum1215o2_520
  · exact le_trans (by norm_num) psum1215o2_521
  · exact le_trans (by norm_num) psum1215o2_522
  · exact le_trans (by norm_num) psum1215o2_523
  · exact le_trans (by norm_num) psum1215o2_524
  · exact le_trans (by norm_num) psum1215o2_525
  · exact le_trans (by norm_num) psum1215o2_526
  · exact le_trans (by norm_num) psum1215o2_527
  · exact le_trans (by norm_num) psum1215o2_528
  · exact le_trans (by norm_num) psum1215o2_529
  · exact le_trans (by norm_num) psum1215o2_530
  · exact le_trans (by norm_num) psum1215o2_531
  · exact le_trans (by norm_num) psum1215o2_532
  · exact le_trans (by norm_num) psum1215o2_533
  · exact le_trans (by norm_num) psum1215o2_534
  · exact le_trans (by norm_num) psum1215o2_535
  · exact le_trans (by norm_num) psum1215o2_536
  · exact le_trans (by norm_num) psum1215o2_537
  · exact le_trans (by norm_num) psum1215o2_538
  · exact le_trans (by norm_num) psum1215o2_539
  · exact le_trans (by norm_num) psum1215o2_540
  · exact le_trans (by norm_num) psum1215o2_541
  · exact le_trans (by norm_num) psum1215o2_542
  · exact le_trans (by norm_num) psum1215o2_543
  · exact le_trans (by norm_num) psum1215o2_544
  · exact le_trans (by norm_num) psum1215o2_545
  · exact le_trans (by norm_num) psum1215o2_546
  · exact le_trans (by norm_num) psum1215o2_547
  · exact le_trans (by norm_num) psum1215o2_548
  · exact le_trans (by norm_num) psum1215o2_549
  · exact le_trans (by norm_num) psum1215o2_550
  · exact le_trans (by norm_num) psum1215o2_551
  · exact le_trans (by norm_num) psum1215o2_552
  · exact le_trans (by norm_num) psum1215o2_553
  · exact le_trans (by norm_num) psum1215o2_554
  · exact le_trans (by norm_num) psum1215o2_555
  · exact le_trans (by norm_num) psum1215o2_556
  · exact le_trans (by norm_num) psum1215o2_557
  · exact le_trans (by norm_num) psum1215o2_558
  · exact le_trans (by norm_num) psum1215o2_559
  · exact le_trans (by norm_num) psum1215o2_560
  · exact le_trans (by norm_num) psum1215o2_561
  · exact le_trans (by norm_num) psum1215o2_562
  · exact le_trans (by norm_num) psum1215o2_563
  · exact le_trans (by norm_num) psum1215o2_564
  · exact le_trans (by norm_num) psum1215o2_565
  · exact le_trans (by norm_num) psum1215o2_566
  · exact le_trans (by norm_num) psum1215o2_567
  · exact le_trans (by norm_num) psum1215o2_568
  · exact le_trans (by norm_num) psum1215o2_569
  · exact le_trans (by norm_num) psum1215o2_570
  · exact le_trans (by norm_num) psum1215o2_571
  · exact le_trans (by norm_num) psum1215o2_572
  · exact le_trans (by norm_num) psum1215o2_573
  · exact le_trans (by norm_num) psum1215o2_574
  · exact le_trans (by norm_num) psum1215o2_575
  · exact le_trans (by norm_num) psum1215o2_576
  · exact le_trans (by norm_num) psum1215o2_577
  · exact le_trans (by norm_num) psum1215o2_578
  · exact le_trans (by norm_num) psum1215o2_579
  · exact le_trans (by norm_num) psum1215o2_580
  · exact le_trans (by norm_num) psum1215o2_581
  · exact le_trans (by norm_num) psum1215o2_582
  · exact le_trans (by norm_num) psum1215o2_583
  · exact le_trans (by norm_num) psum1215o2_584
  · exact le_trans (by norm_num) psum1215o2_585
  · exact le_trans (by norm_num) psum1215o2_586
  · exact le_trans (by norm_num) psum1215o2_587
  · exact le_trans (by norm_num) psum1215o2_588
  · exact le_trans (by norm_num) psum1215o2_589
  · exact le_trans (by norm_num) psum1215o2_590
  · exact le_trans (by norm_num) psum1215o2_591
  · exact le_trans (by norm_num) psum1215o2_592
  · exact le_trans (by norm_num) psum1215o2_593
  · exact le_trans (by norm_num) psum1215o2_594
  · exact le_trans (by norm_num) psum1215o2_595
  · exact le_trans (by norm_num) psum1215o2_596
  · exact le_trans (by norm_num) psum1215o2_597
  · exact le_trans (by norm_num) psum1215o2_598
  · exact le_trans (by norm_num) psum1215o2_599
  · exact le_trans (by norm_num) psum1215o2_600
  · exact le_trans (by norm_num) psum1215o2_601
  · exact le_trans (by norm_num) psum1215o2_602
  · exact le_trans (by norm_num) psum1215o2_603
  · exact le_trans (by norm_num) psum1215o2_604
  · exact le_trans (by norm_num) psum1215o2_605
  · exact le_trans (by norm_num) psum1215o2_606
  · exact le_trans (by norm_num) psum1215o2_607
  · exact le_trans (by norm_num) psum1215o2_608
  · exact le_trans (by norm_num) psum1215o2_609
  · exact le_trans (by norm_num) psum1215o2_610
  · exact le_trans (by norm_num) psum1215o2_611
  · exact le_trans (by norm_num) psum1215o2_612
  · exact le_trans (by norm_num) psum1215o2_613
  · exact le_trans (by norm_num) psum1215o2_614
  · exact le_trans (by norm_num) psum1215o2_615
  · exact le_trans (by norm_num) psum1215o2_616
  · exact le_trans (by norm_num) psum1215o2_617
  · exact le_trans (by norm_num) psum1215o2_618
  · exact le_trans (by norm_num) psum1215o2_619
  · exact le_trans (by norm_num) psum1215o2_620
  · exact le_trans (by norm_num) psum1215o2_621
  · exact le_trans (by norm_num) psum1215o2_622
  · exact le_trans (by norm_num) psum1215o2_623
  · exact le_trans (by norm_num) psum1215o2_624
  · exact le_trans (by norm_num) psum1215o2_625
  · exact le_trans (by norm_num) psum1215o2_626
  · exact le_trans (by norm_num) psum1215o2_627
  · exact le_trans (by norm_num) psum1215o2_628
  · exact le_trans (by norm_num) psum1215o2_629
  · exact le_trans (by norm_num) psum1215o2_630
  · exact le_trans (by norm_num) psum1215o2_631
  · exact le_trans (by norm_num) psum1215o2_632
  · exact le_trans (by norm_num) psum1215o2_633
  · exact le_trans (by norm_num) psum1215o2_634
  · exact le_trans (by norm_num) psum1215o2_635
  · exact le_trans (by norm_num) psum1215o2_636
  · exact le_trans (by norm_num) psum1215o2_637
  · exact le_trans (by norm_num) psum1215o2_638
  · exact le_trans (by norm_num) psum1215o2_639
  · exact le_trans (by norm_num) psum1215o2_640
  · exact le_trans (by norm_num) psum1215o2_641
  · exact le_trans (by norm_num) psum1215o2_642
  · exact le_trans (by norm_num) psum1215o2_643
  · exact le_trans (by norm_num) psum1215o2_644
  · exact le_trans (by norm_num) psum1215o2_645
  · exact le_trans (by norm_num) psum1215o2_646
  · exact le_trans (by norm_num) psum1215o2_647
  · exact le_trans (by norm_num) psum1215o2_648
  · exact le_trans (by norm_num) psum1215o2_649
  · exact le_trans (by norm_num) psum1215o2_650
  · exact le_trans (by norm_num) psum1215o2_651
  · exact le_trans (by norm_num) psum1215o2_652
  · exact le_trans (by norm_num) psum1215o2_653
  · exact le_trans (by norm_num) psum1215o2_654
  · exact le_trans (by norm_num) psum1215o2_655
  · exact le_trans (by norm_num) psum1215o2_656
  · exact le_trans (by norm_num) psum1215o2_657
  · exact le_trans (by norm_num) psum1215o2_658
  · exact le_trans (by norm_num) psum1215o2_659
  · exact le_trans (by norm_num) psum1215o2_660
  · exact le_trans (by norm_num) psum1215o2_661
  · exact le_trans (by norm_num) psum1215o2_662
  · exact le_trans (by norm_num) psum1215o2_663
  · exact le_trans (by norm_num) psum1215o2_664
  · exact le_trans (by norm_num) psum1215o2_665
  · exact le_trans (by norm_num) psum1215o2_666
  · exact le_trans (by norm_num) psum1215o2_667
  · exact le_trans (by norm_num) psum1215o2_668
  · exact le_trans (by norm_num) psum1215o2_669
  · exact le_trans (by norm_num) psum1215o2_670
  · exact le_trans (by norm_num) psum1215o2_671
  · exact le_trans (by norm_num) psum1215o2_672
  · exact le_trans (by norm_num) psum1215o2_673
  · exact le_trans (by norm_num) psum1215o2_674
  · exact le_trans (by norm_num) psum1215o2_675
  · exact le_trans (by norm_num) psum1215o2_676
  · exact le_trans (by norm_num) psum1215o2_677
  · exact le_trans (by norm_num) psum1215o2_678
  · exact le_trans (by norm_num) psum1215o2_679
  · exact le_trans (by norm_num) psum1215o2_680
  · exact le_trans (by norm_num) psum1215o2_681
  · exact le_trans (by norm_num) psum1215o2_682
  · exact le_trans (by norm_num) psum1215o2_683
  · exact le_trans (by norm_num) psum1215o2_684
  · exact le_trans (by norm_num) psum1215o2_685
  · exact le_trans (by norm_num) psum1215o2_686
  · exact le_trans (by norm_num) psum1215o2_687
  · exact le_trans (by norm_num) psum1215o2_688
  · exact le_trans (by norm_num) psum1215o2_689
  · exact le_trans (by norm_num) psum1215o2_690
  · exact le_trans (by norm_num) psum1215o2_691
  · exact le_trans (by norm_num) psum1215o2_692
  · exact le_trans (by norm_num) psum1215o2_693
  · exact le_trans (by norm_num) psum1215o2_694
  · exact le_trans (by norm_num) psum1215o2_695
  · exact le_trans (by norm_num) psum1215o2_696
  · exact le_trans (by norm_num) psum1215o2_697
  · exact le_trans (by norm_num) psum1215o2_698
  · exact le_trans (by norm_num) psum1215o2_699
  · exact le_trans (by norm_num) psum1215o2_700
  · exact le_trans (by norm_num) psum1215o2_701
  · exact le_trans (by norm_num) psum1215o2_702
  · exact le_trans (by norm_num) psum1215o2_703
  · exact le_trans (by norm_num) psum1215o2_704
  · exact le_trans (by norm_num) psum1215o2_705
  · exact le_trans (by norm_num) psum1215o2_706
  · exact le_trans (by norm_num) psum1215o2_707
  · exact le_trans (by norm_num) psum1215o2_708
  · exact le_trans (by norm_num) psum1215o2_709
  · exact le_trans (by norm_num) psum1215o2_710
  · exact le_trans (by norm_num) psum1215o2_711
  · exact le_trans (by norm_num) psum1215o2_712
  · exact le_trans (by norm_num) psum1215o2_713
  · exact le_trans (by norm_num) psum1215o2_714
  · exact le_trans (by norm_num) psum1215o2_715
  · exact le_trans (by norm_num) psum1215o2_716
  · exact le_trans (by norm_num) psum1215o2_717
  · exact le_trans (by norm_num) psum1215o2_718
  · exact le_trans (by norm_num) psum1215o2_719
  · exact le_trans (by norm_num) psum1215o2_720
  · exact le_trans (by norm_num) psum1215o2_721
  · exact le_trans (by norm_num) psum1215o2_722
  · exact le_trans (by norm_num) psum1215o2_723
  · exact le_trans (by norm_num) psum1215o2_724
  · exact le_trans (by norm_num) psum1215o2_725
  · exact le_trans (by norm_num) psum1215o2_726
  · exact le_trans (by norm_num) psum1215o2_727
  · exact le_trans (by norm_num) psum1215o2_728
  · exact le_trans (by norm_num) psum1215o2_729
  · exact le_trans (by norm_num) psum1215o2_730
  · exact le_trans (by norm_num) psum1215o2_731
  · exact le_trans (by norm_num) psum1215o2_732
  · exact le_trans (by norm_num) psum1215o2_733
  · exact le_trans (by norm_num) psum1215o2_734
  · exact le_trans (by norm_num) psum1215o2_735
  · exact le_trans (by norm_num) psum1215o2_736
  · exact le_trans (by norm_num) psum1215o2_737
  · exact le_trans (by norm_num) psum1215o2_738
  · exact le_trans (by norm_num) psum1215o2_739
  · exact le_trans (by norm_num) psum1215o2_740
  · exact le_trans (by norm_num) psum1215o2_741
  · exact le_trans (by norm_num) psum1215o2_742
  · exact le_trans (by norm_num) psum1215o2_743
  · exact le_trans (by norm_num) psum1215o2_744
  · exact le_trans (by norm_num) psum1215o2_745
  · exact le_trans (by norm_num) psum1215o2_746
  · exact le_trans (by norm_num) psum1215o2_747
  · exact le_trans (by norm_num) psum1215o2_748
  · exact le_trans (by norm_num) psum1215o2_749
  · exact le_trans (by norm_num) psum1215o2_750
  · exact le_trans (by norm_num) psum1215o2_751
  · exact le_trans (by norm_num) psum1215o2_752
  · exact le_trans (by norm_num) psum1215o2_753
  · exact le_trans (by norm_num) psum1215o2_754
  · exact le_trans (by norm_num) psum1215o2_755
  · exact le_trans (by norm_num) psum1215o2_756
  · exact le_trans (by norm_num) psum1215o2_757
  · exact le_trans (by norm_num) psum1215o2_758
  · exact le_trans (by norm_num) psum1215o2_759
  · exact le_trans (by norm_num) psum1215o2_760
  · exact le_trans (by norm_num) psum1215o2_761
  · exact le_trans (by norm_num) psum1215o2_762
  · exact le_trans (by norm_num) psum1215o2_763
  · exact le_trans (by norm_num) psum1215o2_764
  · exact le_trans (by norm_num) psum1215o2_765
  · exact le_trans (by norm_num) psum1215o2_766
  · exact le_trans (by norm_num) psum1215o2_767
  · exact le_trans (by norm_num) psum1215o2_768
  · exact le_trans (by norm_num) psum1215o2_769
  · exact le_trans (by norm_num) psum1215o2_770
  · exact le_trans (by norm_num) psum1215o2_771
  · exact le_trans (by norm_num) psum1215o2_772
  · exact le_trans (by norm_num) psum1215o2_773
  · exact le_trans (by norm_num) psum1215o2_774
  · exact le_trans (by norm_num) psum1215o2_775
  · exact le_trans (by norm_num) psum1215o2_776
  · exact le_trans (by norm_num) psum1215o2_777
  · exact le_trans (by norm_num) psum1215o2_778
  · exact le_trans (by norm_num) psum1215o2_779
  · exact le_trans (by norm_num) psum1215o2_780
  · exact le_trans (by norm_num) psum1215o2_781
  · exact le_trans (by norm_num) psum1215o2_782
  · exact le_trans (by norm_num) psum1215o2_783
  · exact le_trans (by norm_num) psum1215o2_784
  · exact le_trans (by norm_num) psum1215o2_785
  · exact le_trans (by norm_num) psum1215o2_786
  · exact le_trans (by norm_num) psum1215o2_787
  · exact le_trans (by norm_num) psum1215o2_788
  · exact le_trans (by norm_num) psum1215o2_789
  · exact le_trans (by norm_num) psum1215o2_790
  · exact le_trans (by norm_num) psum1215o2_791
  · exact le_trans (by norm_num) psum1215o2_792
  · exact le_trans (by norm_num) psum1215o2_793
  · exact le_trans (by norm_num) psum1215o2_794
  · exact le_trans (by norm_num) psum1215o2_795
  · exact le_trans (by norm_num) psum1215o2_796
  · exact le_trans (by norm_num) psum1215o2_797
  · exact le_trans (by norm_num) psum1215o2_798
  · exact le_trans (by norm_num) psum1215o2_799
  · exact le_trans (by norm_num) psum1215o2_800
  · exact le_trans (by norm_num) psum1215o2_801
  · exact le_trans (by norm_num) psum1215o2_802
  · exact le_trans (by norm_num) psum1215o2_803
  · exact le_trans (by norm_num) psum1215o2_804
  · exact le_trans (by norm_num) psum1215o2_805
  · exact le_trans (by norm_num) psum1215o2_806
  · exact le_trans (by norm_num) psum1215o2_807
  · exact le_trans (by norm_num) psum1215o2_808
  · exact le_trans (by norm_num) psum1215o2_809
  · exact le_trans (by norm_num) psum1215o2_810
  · exact le_trans (by norm_num) psum1215o2_811
  · exact le_trans (by norm_num) psum1215o2_812
  · exact le_trans (by norm_num) psum1215o2_813
  · exact le_trans (by norm_num) psum1215o2_814
  · exact le_trans (by norm_num) psum1215o2_815
  · exact le_trans (by norm_num) psum1215o2_816
  · exact le_trans (by norm_num) psum1215o2_817
  · exact le_trans (by norm_num) psum1215o2_818
  · exact le_trans (by norm_num) psum1215o2_819
  · exact le_trans (by norm_num) psum1215o2_820
  · exact le_trans (by norm_num) psum1215o2_821
  · exact le_trans (by norm_num) psum1215o2_822
  · exact le_trans (by norm_num) psum1215o2_823
  · exact le_trans (by norm_num) psum1215o2_824
  · exact le_trans (by norm_num) psum1215o2_825
  · exact le_trans (by norm_num) psum1215o2_826
  · exact le_trans (by norm_num) psum1215o2_827
  · exact le_trans (by norm_num) psum1215o2_828
  · exact le_trans (by norm_num) psum1215o2_829
  · exact le_trans (by norm_num) psum1215o2_830
  · exact le_trans (by norm_num) psum1215o2_831
  · exact le_trans (by norm_num) psum1215o2_832
  · exact le_trans (by norm_num) psum1215o2_833
  · exact le_trans (by norm_num) psum1215o2_834
  · exact le_trans (by norm_num) psum1215o2_835
  · exact le_trans (by norm_num) psum1215o2_836
  · exact le_trans (by norm_num) psum1215o2_837
  · exact le_trans (by norm_num) psum1215o2_838
  · exact le_trans (by norm_num) psum1215o2_839
  · exact le_trans (by norm_num) psum1215o2_840
  · exact le_trans (by norm_num) psum1215o2_841
  · exact le_trans (by norm_num) psum1215o2_842
  · exact le_trans (by norm_num) psum1215o2_843
  · exact le_trans (by norm_num) psum1215o2_844
  · exact le_trans (by norm_num) psum1215o2_845
  · exact le_trans (by norm_num) psum1215o2_846
  · exact le_trans (by norm_num) psum1215o2_847
  · exact le_trans (by norm_num) psum1215o2_848
  · exact le_trans (by norm_num) psum1215o2_849
  · exact le_trans (by norm_num) psum1215o2_850
  · exact le_trans (by norm_num) psum1215o2_851
  · exact le_trans (by norm_num) psum1215o2_852
  · exact le_trans (by norm_num) psum1215o2_853
  · exact le_trans (by norm_num) psum1215o2_854
  · exact le_trans (by norm_num) psum1215o2_855
  · exact le_trans (by norm_num) psum1215o2_856
  · exact le_trans (by norm_num) psum1215o2_857
  · exact le_trans (by norm_num) psum1215o2_858
  · exact le_trans (by norm_num) psum1215o2_859
  · exact le_trans (by norm_num) psum1215o2_860
  · exact le_trans (by norm_num) psum1215o2_861
  · exact le_trans (by norm_num) psum1215o2_862
  · exact le_trans (by norm_num) psum1215o2_863
  · exact le_trans (by norm_num) psum1215o2_864
  · exact le_trans (by norm_num) psum1215o2_865
  · exact le_trans (by norm_num) psum1215o2_866
  · exact le_trans (by norm_num) psum1215o2_867
  · exact le_trans (by norm_num) psum1215o2_868
  · exact le_trans (by norm_num) psum1215o2_869
  · exact le_trans (by norm_num) psum1215o2_870
  · exact le_trans (by norm_num) psum1215o2_871
  · exact le_trans (by norm_num) psum1215o2_872
  · exact le_trans (by norm_num) psum1215o2_873
  · exact le_trans (by norm_num) psum1215o2_874
  · exact le_trans (by norm_num) psum1215o2_875
  · exact le_trans (by norm_num) psum1215o2_876
  · exact le_trans (by norm_num) psum1215o2_877
  · exact le_trans (by norm_num) psum1215o2_878
  · exact le_trans (by norm_num) psum1215o2_879
  · exact le_trans (by norm_num) psum1215o2_880
  · exact le_trans (by norm_num) psum1215o2_881
  · exact le_trans (by norm_num) psum1215o2_882
  · exact le_trans (by norm_num) psum1215o2_883
  · exact le_trans (by norm_num) psum1215o2_884
  · exact le_trans (by norm_num) psum1215o2_885
  · exact le_trans (by norm_num) psum1215o2_886
  · exact le_trans (by norm_num) psum1215o2_887
  · exact le_trans (by norm_num) psum1215o2_888
  · exact le_trans (by norm_num) psum1215o2_889
  · exact le_trans (by norm_num) psum1215o2_890
  · exact le_trans (by norm_num) psum1215o2_891
  · exact le_trans (by norm_num) psum1215o2_892
  · exact le_trans (by norm_num) psum1215o2_893
  · exact le_trans (by norm_num) psum1215o2_894
  · exact le_trans (by norm_num) psum1215o2_895
  · exact le_trans (by norm_num) psum1215o2_896
  · exact le_trans (by norm_num) psum1215o2_897
  · exact le_trans (by norm_num) psum1215o2_898
  · exact le_trans (by norm_num) psum1215o2_899
  · exact le_trans (by norm_num) psum1215o2_900
  · exact le_trans (by norm_num) psum1215o2_901
  · exact le_trans (by norm_num) psum1215o2_902
  · exact le_trans (by norm_num) psum1215o2_903
  · exact le_trans (by norm_num) psum1215o2_904
  · exact le_trans (by norm_num) psum1215o2_905
  · exact le_trans (by norm_num) psum1215o2_906
  · exact le_trans (by norm_num) psum1215o2_907
  · exact le_trans (by norm_num) psum1215o2_908
  · exact le_trans (by norm_num) psum1215o2_909
  · exact le_trans (by norm_num) psum1215o2_910
  · exact le_trans (by norm_num) psum1215o2_911
  · exact le_trans (by norm_num) psum1215o2_912
  · exact le_trans (by norm_num) psum1215o2_913
  · exact le_trans (by norm_num) psum1215o2_914
  · exact le_trans (by norm_num) psum1215o2_915
  · exact le_trans (by norm_num) psum1215o2_916
  · exact le_trans (by norm_num) psum1215o2_917
  · exact le_trans (by norm_num) psum1215o2_918
  · exact le_trans (by norm_num) psum1215o2_919
  · exact le_trans (by norm_num) psum1215o2_920
  · exact le_trans (by norm_num) psum1215o2_921
  · exact le_trans (by norm_num) psum1215o2_922
  · exact le_trans (by norm_num) psum1215o2_923
  · exact le_trans (by norm_num) psum1215o2_924
  · exact le_trans (by norm_num) psum1215o2_925
  · exact le_trans (by norm_num) psum1215o2_926
  · exact le_trans (by norm_num) psum1215o2_927
  · exact le_trans (by norm_num) psum1215o2_928
  · exact le_trans (by norm_num) psum1215o2_929
  · exact le_trans (by norm_num) psum1215o2_930
  · exact le_trans (by norm_num) psum1215o2_931
  · exact le_trans (by norm_num) psum1215o2_932
  · exact le_trans (by norm_num) psum1215o2_933
  · exact le_trans (by norm_num) psum1215o2_934
  · exact le_trans (by norm_num) psum1215o2_935
  · exact le_trans (by norm_num) psum1215o2_936
  · exact le_trans (by norm_num) psum1215o2_937
  · exact le_trans (by norm_num) psum1215o2_938
  · exact le_trans (by norm_num) psum1215o2_939
  · exact le_trans (by norm_num) psum1215o2_940
  · exact le_trans (by norm_num) psum1215o2_941
  · exact le_trans (by norm_num) psum1215o2_942
  · exact le_trans (by norm_num) psum1215o2_943
  · exact le_trans (by norm_num) psum1215o2_944
  · exact le_trans (by norm_num) psum1215o2_945
  · exact le_trans (by norm_num) psum1215o2_946
  · exact le_trans (by norm_num) psum1215o2_947
  · exact le_trans (by norm_num) psum1215o2_948
  · exact le_trans (by norm_num) psum1215o2_949
  · exact le_trans (by norm_num) psum1215o2_950
  · exact le_trans (by norm_num) psum1215o2_951
  · exact le_trans (by norm_num) psum1215o2_952
  · exact le_trans (by norm_num) psum1215o2_953
  · exact le_trans (by norm_num) psum1215o2_954
  · exact le_trans (by norm_num) psum1215o2_955
  · exact le_trans (by norm_num) psum1215o2_956
  · exact le_trans (by norm_num) psum1215o2_957
  · exact le_trans (by norm_num) psum1215o2_958
  · exact le_trans (by norm_num) psum1215o2_959
  · exact le_trans (by norm_num) psum1215o2_960
  · exact le_trans (by norm_num) psum1215o2_961
  · exact le_trans (by norm_num) psum1215o2_962
  · exact le_trans (by norm_num) psum1215o2_963
  · exact le_trans (by norm_num) psum1215o2_964
  · exact le_trans (by norm_num) psum1215o2_965
  · exact le_trans (by norm_num) psum1215o2_966
  · exact le_trans (by norm_num) psum1215o2_967
  · exact le_trans (by norm_num) psum1215o2_968
  · exact le_trans (by norm_num) psum1215o2_969
  · exact le_trans (by norm_num) psum1215o2_970
  · exact le_trans (by norm_num) psum1215o2_971
  · exact le_trans (by norm_num) psum1215o2_972
  · exact le_trans (by norm_num) psum1215o2_973
  · exact le_trans (by norm_num) psum1215o2_974
  · exact le_trans (by norm_num) psum1215o2_975
  · exact le_trans (by norm_num) psum1215o2_976
  · exact le_trans (by norm_num) psum1215o2_977
  · exact le_trans (by norm_num) psum1215o2_978
  · exact le_trans (by norm_num) psum1215o2_979
  · exact le_trans (by norm_num) psum1215o2_980
  · exact le_trans (by norm_num) psum1215o2_981
  · exact le_trans (by norm_num) psum1215o2_982
  · exact le_trans (by norm_num) psum1215o2_983
  · exact le_trans (by norm_num) psum1215o2_984
  · exact le_trans (by norm_num) psum1215o2_985
  · exact le_trans (by norm_num) psum1215o2_986
  · exact le_trans (by norm_num) psum1215o2_987
  · exact le_trans (by norm_num) psum1215o2_988
  · exact le_trans (by norm_num) psum1215o2_989
  · exact le_trans (by norm_num) psum1215o2_990
  · exact le_trans (by norm_num) psum1215o2_991
  · exact le_trans (by norm_num) psum1215o2_992
  · exact le_trans (by norm_num) psum1215o2_993
  · exact le_trans (by norm_num) psum1215o2_994
  · exact le_trans (by norm_num) psum1215o2_995
  · exact le_trans (by norm_num) psum1215o2_996
  · exact le_trans (by norm_num) psum1215o2_997
  · exact le_trans (by norm_num) psum1215o2_998
  · exact le_trans (by norm_num) psum1215o2_999
  · exact le_trans (by norm_num) psum1215o2_1000

end CriticalLinePhasor.DVP

section AxiomAudit
#print axioms CriticalLinePhasor.DVP.psum1215o2_floor
#print axioms CriticalLinePhasor.DVP.psum1215o2_1000
end AxiomAudit
