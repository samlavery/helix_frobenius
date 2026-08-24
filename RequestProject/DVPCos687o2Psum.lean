import RequestProject.DVPCos687o2Table

/-!
# The cosine partial-sum floor, `t = 687/2` (N = 500)
-/

open Finset

noncomputable section

namespace CriticalLinePhasor.DVP

/-- The cosine sequence of the `t = 687/2` segment certificate. -/
def cos687o2c (n : ℕ) : ℝ := Real.cos (((687:ℕ):ℝ) * (Real.log n / 2))

theorem psum687o2_11 : ((836503/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 11, cos687o2c k := by
  rw [Finset.Icc_self, Finset.sum_singleton]
  have h : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 11 - ((836603/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_11).1
  push_cast at h ⊢
  linarith

theorem psum687o2_12 : ((1419901/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 12, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 12, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 11, cos687o2c k) + cos687o2c 12 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 11) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_11
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 12 - ((291749/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_12).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_13 : ((1575799/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 13, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 13, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 12, cos687o2c k) + cos687o2c 13 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 12) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_12
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 13 - ((77999/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_13).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_14 : ((1409751/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 14, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 14, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 13, cos687o2c k) + cos687o2c 14 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 13) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_13
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 14 - ((-41487/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_14).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_15 : ((2363847/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 15, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 15, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 14, cos687o2c k) + cos687o2c 15 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 14) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_14
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 15 - ((238549/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_15).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_16 : ((1477521/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 16, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 16, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 15, cos687o2c k) + cos687o2c 16 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 15) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_15
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 16 - ((-443113/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_16).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_17 : ((56297/25000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 17, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 17, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 16, cos687o2c k) + cos687o2c 17 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 16) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_16
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 17 - ((774459/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_17).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_18 : ((1623421/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 18, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 18, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 17, cos687o2c k) + cos687o2c 18 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 17) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_17
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 18 - ((497531/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_18).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_19 : ((1057733/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 19, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 19, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 18, cos687o2c k) + cos687o2c 19 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 18) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_18
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 19 - ((98419/100000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_19).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_20 : ((4392553/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 20, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 20, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 19, cos687o2c k) + cos687o2c 20 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 19) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_19
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 20 - ((161721/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_20).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_21 : ((1727733/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 21, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 21, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 20, cos687o2c k) + cos687o2c 21 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 20) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_20
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 21 - ((-936987/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_21).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_22 : ((556467/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 22, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 22, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 21, cos687o2c k) + cos687o2c 22 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 21) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_21
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 22 - ((99637/100000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_22).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_23 : ((1792907/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 23, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 23, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 22, cos687o2c k) + cos687o2c 23 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 22) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_22
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 23 - ((-432911/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_23).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_24 : ((3543777/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 24, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 24, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 23, cos687o2c k) + cos687o2c 24 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 23) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_23
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 24 - ((-41937/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_24).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_25 : ((906283/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 25, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 25, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 24, cos687o2c k) + cos687o2c 25 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 24) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_24
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 25 - ((493869/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_25).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_26 : ((2631781/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 26, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 26, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 25, cos687o2c k) + cos687o2c 26 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 25) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_25
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 26 - ((732247/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_26).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_27 : ((709381/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 27, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 27, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 26, cos687o2c k) + cos687o2c 27 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 26) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_26
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 27 - ((205793/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_27).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_28 : ((1230569/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 28, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 28, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 27, cos687o2c k) + cos687o2c 28 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 27) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_27
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 28 - ((477897/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_28).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_29 : ((1399997/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 29, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 29, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 28, cos687o2c k) + cos687o2c 29 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 28) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_28
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 29 - ((21181/25000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_29).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_30 : ((3967683/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 30, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 30, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 29, cos687o2c k) + cos687o2c 30 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 29) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_29
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 30 - ((935481/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_30).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_31 : ((7841981/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 31, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 31, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 30, cos687o2c k) + cos687o2c 31 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 30) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_30
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 31 - ((-18657/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_31).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_32 : ((6858637/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 32, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 32, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 31, cos687o2c k) + cos687o2c 32 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 31) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_31
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 32 - ((-245811/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_32).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_33 : ((7430459/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 33, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 33, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 32, cos687o2c k) + cos687o2c 33 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 32) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_32
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 33 - ((285961/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_33).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_34 : ((956181/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 34, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 34, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 33, cos687o2c k) + cos687o2c 34 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 33) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_33
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 34 - ((219089/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_34).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_35 : ((1741323/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 35, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 35, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 34, cos687o2c k) + cos687o2c 35 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 34) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_34
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 35 - ((-85507/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_35).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_36 : ((195237/25000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 36, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 36, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 35, cos687o2c k) + cos687o2c 36 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 35) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_35
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 36 - ((13192/15625 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_36).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_37 : ((6972251/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 37, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 37, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 36, cos687o2c k) + cos687o2c 37 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 36) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_36
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 37 - ((-837129/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_37).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_38 : ((954669/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 38, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 38, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 37, cos687o2c k) + cos687o2c 38 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 37) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_37
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 38 - ((665201/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_38).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_39 : ((7413591/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 39, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 39, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 38, cos687o2c k) + cos687o2c 39 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 38) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_38
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 39 - ((-223661/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_39).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_40 : ((3465917/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 40, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 40, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 39, cos687o2c k) + cos687o2c 40 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 39) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_39
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 40 - ((-481657/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_40).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_41 : ((1980971/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 41, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 41, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 40, cos687o2c k) + cos687o2c 41 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 40) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_40
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 41 - ((19843/20000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_41).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_42 : ((7402013/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 42, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 42, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 41, cos687o2c k) + cos687o2c 42 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 41) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_41
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 42 - ((-521771/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_42).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_43 : ((6689363/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 43, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 43, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 42, cos687o2c k) + cos687o2c 43 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 42) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_42
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 43 - ((-14251/20000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_43).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_44 : ((3710403/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 44, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 44, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 43, cos687o2c k) + cos687o2c 44 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 43) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_43
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 44 - ((731543/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_44).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_45 : ((8194487/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 45, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 45, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 44, cos687o2c k) + cos687o2c 45 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 44) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_44
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 45 - ((773781/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_45).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_46 : ((977727/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 46, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 46, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 45, cos687o2c k) + cos687o2c 46 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 45) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_45
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 46 - ((-372571/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_46).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_47 : ((1706327/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 47, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 47, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 46, cos687o2c k) + cos687o2c 47 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 46) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_46
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 47 - ((-124551/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_47).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_48 : ((6175707/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 48, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 48, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 47, cos687o2c k) + cos687o2c 48 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 47) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_47
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 48 - ((-649501/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_48).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_49 : ((6268057/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 49, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 49, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 48, cos687o2c k) + cos687o2c 49 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 48) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_48
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 49 - ((1849/20000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_49).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_50 : ((3474453/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 50, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 50, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 49, cos687o2c k) + cos687o2c 50 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 49) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_49
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 50 - ((680949/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_50).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_51 : ((1975833/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 51, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 51, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 50, cos687o2c k) + cos687o2c 51 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 50) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_50
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 51 - ((477263/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_51).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_52 : ((8899689/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 52, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 52, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 51, cos687o2c k) + cos687o2c 52 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 51) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_51
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 52 - ((996457/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_52).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_53 : ((9840977/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 53, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 53, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 52, cos687o2c k) + cos687o2c 53 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 52) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_52
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 53 - ((235347/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_53).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_54 : ((10727121/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 54, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 54, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 53, cos687o2c k) + cos687o2c 54 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 53) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_53
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 54 - ((221561/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_54).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_55 : ((11603953/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 55, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 55, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 54, cos687o2c k) + cos687o2c 55 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 54) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_54
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 55 - ((219233/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_55).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_56 : ((6260979/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 56, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 56, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 55, cos687o2c k) + cos687o2c 56 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 55) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_55
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 56 - ((183621/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_56).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_57 : ((13501091/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 57, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 57, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 56, cos687o2c k) + cos687o2c 57 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 56) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_56
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 57 - ((979233/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_57).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_58 : ((14495489/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 58, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 58, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 57, cos687o2c k) + cos687o2c 58 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 57) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_57
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 58 - ((497249/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_58).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_59 : ((3073017/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 59, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 59, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 58, cos687o2c k) + cos687o2c 59 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 58) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_58
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 59 - ((13589/15625 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_59).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_60 : ((3176619/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 60, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 60, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 59, cos687o2c k) + cos687o2c 60 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 59) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_59
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 60 - ((51811/100000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_60).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_61 : ((7911151/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 61, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 61, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 60, cos687o2c k) + cos687o2c 61 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 60) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_60
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 61 - ((-60693/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_61).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_62 : ((15134417/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 62, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 62, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 61, cos687o2c k) + cos687o2c 62 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 61) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_61
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 62 - ((-137557/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_62).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_63 : ((14134637/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 63, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 63, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 62, cos687o2c k) + cos687o2c 63 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 62) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_62
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 63 - ((-3124/3125 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_63).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_64 : ((134733/10000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 64, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 64, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 63, cos687o2c k) + cos687o2c 64 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 63) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_63
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 64 - ((-661237/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_64).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_65 : ((3426517/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 65, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 65, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 64, cos687o2c k) + cos687o2c 65 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 64) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_64
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 65 - ((58217/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_65).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_66 : ((2932439/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 66, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 66, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 65, cos687o2c k) + cos687o2c 66 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 65) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_65
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 66 - ((956227/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_66).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_67 : ((239747/15625 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 67, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 67, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 66, cos687o2c k) + cos687o2c 67 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 66) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_66
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 67 - ((681713/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_67).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_68 : ((2982813/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 68, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 68, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 67, cos687o2c k) + cos687o2c 68 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 67) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_67
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 68 - ((-429643/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_68).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_69 : ((6962001/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 69, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 69, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 68, cos687o2c k) + cos687o2c 69 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 68) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_68
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 69 - ((-989963/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_69).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_70 : ((6917843/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 70, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 70, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 69, cos687o2c k) + cos687o2c 70 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 69) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_69
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 70 - ((-11027/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_70).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_71 : ((2960981/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 71, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 71, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 70, cos687o2c k) + cos687o2c 71 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 70) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_70
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 71 - ((969319/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_71).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_72 : ((7569267/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 72, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 72, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 71, cos687o2c k) + cos687o2c 72 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 71) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_71
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 72 - ((333729/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_72).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_73 : ((710231/50000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 73, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 73, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 72, cos687o2c k) + cos687o2c 73 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 72) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_72
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 73 - ((-466907/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_73).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_74 : ((2776663/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 74, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 74, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 73, cos687o2c k) + cos687o2c 74 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 73) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_73
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 74 - ((-64241/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_74).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_75 : ((14857909/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 75, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 75, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 74, cos687o2c k) + cos687o2c 75 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 74) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_74
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 75 - ((487347/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_75).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_76 : ((1865069/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 76, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 76, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 75, cos687o2c k) + cos687o2c 76 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 75) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_75
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 76 - ((62743/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_76).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_77 : ((43541/3125 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 77, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 77, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 76, cos687o2c k) + cos687o2c 77 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 76) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_76
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 77 - ((-246833/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_77).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_78 : ((574337/40000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 78, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 78, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 77, cos687o2c k) + cos687o2c 78 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 77) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_77
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 78 - ((85081/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_78).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_79 : ((188401/12500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 79, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 79, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 78, cos687o2c k) + cos687o2c 79 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 78) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_78
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 79 - ((142751/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_79).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_80 : ((14152199/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 80, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 80, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 79, cos687o2c k) + cos687o2c 80 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 79) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_79
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 80 - ((-919781/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_80).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_81 : ((7097037/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 81, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 81, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 80, cos687o2c k) + cos687o2c 81 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 80) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_80
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 81 - ((1679/40000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_81).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_82 : ((1505189/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 82, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 82, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 81, cos687o2c k) + cos687o2c 82 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 81) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_81
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 82 - ((214479/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_82).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_83 : ((7082979/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 83, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 83, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 82, cos687o2c k) + cos687o2c 83 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 82) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_82
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 83 - ((-110729/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_83).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_84 : ((14281667/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 84, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 84, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 83, cos687o2c k) + cos687o2c 84 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 83) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_83
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 84 - ((115809/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_84).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_85 : ((3751027/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 85, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 85, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 84, cos687o2c k) + cos687o2c 85 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 84) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_84
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 85 - ((722541/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_85).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_86 : ((14010347/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 86, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 86, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 85, cos687o2c k) + cos687o2c 86 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 85) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_85
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 86 - ((-993661/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_86).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_87 : ((14598229/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 87, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 87, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 86, cos687o2c k) + cos687o2c 87 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 86) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_86
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 87 - ((293991/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_87).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_88 : ((7376553/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 88, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 88, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 87, cos687o2c k) + cos687o2c 88 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 87) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_87
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 88 - ((154977/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_88).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_89 : ((13972553/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 89, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 89, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 88, cos687o2c k) + cos687o2c 89 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 88) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_88
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 89 - ((-780453/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_89).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_90 : ((1871529/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 90, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 90, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 89, cos687o2c k) + cos687o2c 90 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 89) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_89
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 90 - ((999779/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_90).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_91 : ((7095731/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 91, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 91, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 90, cos687o2c k) + cos687o2c 91 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 90) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_90
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 91 - ((-78067/100000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_91).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_92 : ((1808849/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 92, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 92, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 91, cos687o2c k) + cos687o2c 92 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 91) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_91
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 92 - ((27943/100000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_92).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_93 : ((14755447/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 93, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 93, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 92, cos687o2c k) + cos687o2c 93 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 92) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_92
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 93 - ((56951/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_93).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_94 : ((14023523/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 94, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 94, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 93, cos687o2c k) + cos687o2c 94 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 93) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_93
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 94 - ((-45739/62500 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_94).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_95 : ((14990721/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 95, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 95, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 94, cos687o2c k) + cos687o2c 95 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 94) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_94
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 95 - ((483649/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_95).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_96 : ((1751291/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 96, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 96, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 95, cos687o2c k) + cos687o2c 96 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 95) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_95
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 96 - ((-980293/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_96).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_97 : ((14825913/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 97, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 97, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 96, cos687o2c k) + cos687o2c 97 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 96) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_96
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 97 - ((163137/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_97).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_98 : ((2856833/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 98, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 98, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 97, cos687o2c k) + cos687o2c 98 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 97) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_97
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 98 - ((-33853/62500 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_98).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_99 : ((1450877/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 99, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 99, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 98, cos687o2c k) + cos687o2c 99 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 98) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_98
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 99 - ((44941/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_99).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_100 : ((14592617/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 100, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 100, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 99, cos687o2c k) + cos687o2c 100 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 99) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_99
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 100 - ((83947/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_100).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_101 : ((7119927/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 101, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 101, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 100, cos687o2c k) + cos687o2c 101 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 100) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_100
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 101 - ((-352663/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_101).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_102 : ((7403471/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 102, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 102, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 101, cos687o2c k) + cos687o2c 102 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 101) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_101
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 102 - ((141797/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_102).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_103 : ((2816137/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 103, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 103, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 102, cos687o2c k) + cos687o2c 103 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 102) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_102
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 103 - ((-726157/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_103).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_104 : ((14916603/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 104, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 104, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 103, cos687o2c k) + cos687o2c 104 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 103) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_103
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 104 - ((418009/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_104).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_105 : ((14009751/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 105, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 105, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 104, cos687o2c k) + cos687o2c 105 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 104) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_104
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 105 - ((-14168/15625 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_105).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_106 : ((1495859/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 106, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 106, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 105, cos687o2c k) + cos687o2c 106 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 105) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_105
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 106 - ((948939/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_106).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_107 : ((559459/40000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 107, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 107, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 106, cos687o2c k) + cos687o2c 107 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 106) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_106
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 107 - ((-194403/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_107).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_108 : ((14969613/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 108, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 108, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 107, cos687o2c k) + cos687o2c 108 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 107) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_107
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 108 - ((491619/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_108).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_109 : ((6991067/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 109, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 109, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 108, cos687o2c k) + cos687o2c 109 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 108) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_108
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 109 - ((-987379/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_109).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_110 : ((14968677/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 110, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 110, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 109, cos687o2c k) + cos687o2c 110 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 109) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_109
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 110 - ((986643/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_110).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_111 : ((3496959/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 111, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 111, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 110, cos687o2c k) + cos687o2c 111 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 110) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_110
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 111 - ((-980741/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_111).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_112 : ((14954777/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 112, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 112, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 111, cos687o2c k) + cos687o2c 112 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 111) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_111
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 112 - ((967041/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_112).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_113 : ((1401383/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 113, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 113, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 112, cos687o2c k) + cos687o2c 113 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 112) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_112
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 113 - ((-940847/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_113).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_114 : ((2981883/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 114, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 114, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 113, cos687o2c k) + cos687o2c 114 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 113) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_113
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 114 - ((179137/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_114).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_115 : ((14085333/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 115, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 115, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 114, cos687o2c k) + cos687o2c 115 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 114) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_114
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 115 - ((-411991/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_115).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_116 : ((14803169/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 116, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 116, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 115, cos687o2c k) + cos687o2c 116 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 115) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_115
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 116 - ((44871/62500 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_116).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_117 : ((7116013/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 117, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 117, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 116, cos687o2c k) + cos687o2c 117 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 116) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_116
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 117 - ((-571043/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_117).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_118 : ((1826469/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 118, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 118, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 117, cos687o2c k) + cos687o2c 118 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 117) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_117
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 118 - ((189913/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_118).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_119 : ((7232717/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 119, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 119, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 118, cos687o2c k) + cos687o2c 119 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 118) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_118
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 119 - ((-73109/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_119).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_120 : ((7172643/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 120, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 120, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 119, cos687o2c k) + cos687o2c 120 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 119) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_119
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 120 - ((-7503/62500 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_120).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_121 : ((14744981/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 121, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 121, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 120, cos687o2c k) + cos687o2c 121 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 120) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_120
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 121 - ((79959/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_121).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_122 : ((2816243/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 122, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 122, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 121, cos687o2c k) + cos687o2c 122 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 121) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_121
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 122 - ((-331833/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_122).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_123 : ((7477517/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 123, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 123, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 122, cos687o2c k) + cos687o2c 123 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 122) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_122
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 123 - ((873919/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_123).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_124 : ((558631/40000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 124, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 124, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 123, cos687o2c k) + cos687o2c 124 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 123) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_123
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 124 - ((-989159/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_124).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_125 : ((2987631/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 125, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 125, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 124, cos687o2c k) + cos687o2c 125 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 124) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_124
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 125 - ((3039/3125 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_125).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_126 : ((14135759/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 126, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 126, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 125, cos687o2c k) + cos687o2c 126 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 125) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_125
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 126 - ((-100287/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_126).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_127 : ((2923883/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 127, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 127, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 126, cos687o2c k) + cos687o2c 127 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 126) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_126
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 127 - ((120939/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_127).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_128 : ((14561859/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 128, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 128, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 127, cos687o2c k) + cos687o2c 128 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 127) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_127
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 128 - ((-3591/62500 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_128).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_129 : ((14162307/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 129, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 129, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 128, cos687o2c k) + cos687o2c 129 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 128) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_128
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 129 - ((-99863/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_129).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_130 : ((14945537/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 130, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 130, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 129, cos687o2c k) + cos687o2c 130 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 129) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_129
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 130 - ((78333/100000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_130).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_131 : ((2791687/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 131, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 131, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 130, cos687o2c k) + cos687o2c 131 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 130) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_130
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 131 - ((-493501/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_131).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_132 : ((14891381/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 132, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 132, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 131, cos687o2c k) + cos687o2c 132 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 131) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_131
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 132 - ((466523/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_132).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_133 : ((2856637/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 133, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 133, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 132, cos687o2c k) + cos687o2c 133 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 132) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_132
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 133 - ((-19003/31250 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_133).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_134 : ((14368087/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 134, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 134, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 133, cos687o2c k) + cos687o2c 134 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 133) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_133
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 134 - ((42501/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_134).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_135 : ((14849677/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 135, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 135, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 134, cos687o2c k) + cos687o2c 135 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 134) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_134
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 135 - ((48169/100000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_135).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_136 : ((6977137/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 136, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 136, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 135, cos687o2c k) + cos687o2c 136 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 135) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_135
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 136 - ((-895303/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_136).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_137 : ((2988171/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 137, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 137, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 136, cos687o2c k) + cos687o2c 137 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 136) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_136
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 137 - ((986681/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_137).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_138 : ((14248951/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 138, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 138, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 137, cos687o2c k) + cos687o2c 138 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 137) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_137
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 138 - ((-172951/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_138).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_139 : ((3587809/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 139, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 139, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 138, cos687o2c k) + cos687o2c 139 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 138) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_138
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 139 - ((20477/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_139).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_140 : ((14896353/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 140, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 140, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 139, cos687o2c k) + cos687o2c 140 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 139) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_139
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 140 - ((545217/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_140).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_141 : ((6970073/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 141, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 141, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 140, cos687o2c k) + cos687o2c 141 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 140) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_140
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 141 - ((-956107/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_141).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_142 : ((2970901/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 142, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 142, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 141, cos687o2c k) + cos687o2c 142 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 141) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_141
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 142 - ((914459/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_142).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_143 : ((2888759/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 143, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 143, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 142, cos687o2c k) + cos687o2c 143 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 142) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_142
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 143 - ((-41061/100000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_143).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_144 : ((7062309/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 144, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 144, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 143, cos687o2c k) + cos687o2c 144 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 143) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_143
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 144 - ((-319077/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_144).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_145 : ((3002151/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 145, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 145, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 144, cos687o2c k) + cos687o2c 145 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 144) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_144
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 145 - ((886237/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_145).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_146 : ((878441/62500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 146, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 146, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 145, cos687o2c k) + cos687o2c 146 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 145) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_145
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 146 - ((-955599/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_146).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_147 : ((7256053/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 147, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 147, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 146, cos687o2c k) + cos687o2c 147 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 146) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_146
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 147 - ((9143/20000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_147).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_148 : ((2968717/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 148, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 148, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 147, cos687o2c k) + cos687o2c 148 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 147) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_147
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 148 - ((331579/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_148).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_149 : ((6962071/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 149, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 149, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 148, cos687o2c k) + cos687o2c 149 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 148) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_148
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 149 - ((-919343/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_149).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_150 : ((14828979/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 150, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 150, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 149, cos687o2c k) + cos687o2c 150 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 149) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_149
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 150 - ((904937/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_150).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_151 : ((2912033/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 151, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 151, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 150, cos687o2c k) + cos687o2c 151 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 150) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_150
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 151 - ((-134357/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_151).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_152 : ((13993613/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 152, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 152, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 151, cos687o2c k) + cos687o2c 152 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 151) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_151
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 152 - ((-141613/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_152).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_153 : ((3747589/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 153, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 153, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 152, cos687o2c k) + cos687o2c 153 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 152) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_152
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 153 - ((996843/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_153).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_154 : ((14311197/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 154, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 154, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 153, cos687o2c k) + cos687o2c 154 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 153) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_153
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 154 - ((-679059/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_154).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_155 : ((3535033/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 155, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 155, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 154, cos687o2c k) + cos687o2c 155 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 154) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_154
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 155 - ((-34193/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_155).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_156 : ((15033221/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 156, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 156, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 155, cos687o2c k) + cos687o2c 156 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 155) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_155
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 156 - ((893189/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_156).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_157 : ((14146259/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 157, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 157, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 156, cos687o2c k) + cos687o2c 157 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 156) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_156
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 157 - ((-443431/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_157).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_158 : ((713783/50000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 158, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 158, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 157, cos687o2c k) + cos687o2c 158 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 157) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_157
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 158 - ((129501/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_158).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_159 : ((1502321/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 159, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 159, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 158, cos687o2c k) + cos687o2c 159 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 158) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_158
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 159 - ((14953/20000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_159).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_160 : ((351429/25000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 160, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 160, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 159, cos687o2c k) + cos687o2c 160 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 159) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_159
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 160 - ((-19319/20000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_160).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_161 : ((448747/31250 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 161, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 161, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 160, cos687o2c k) + cos687o2c 161 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 160) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_160
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 161 - ((75711/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_161).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_162 : ((7504667/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 162, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 162, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 161, cos687o2c k) + cos687o2c 162 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 161) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_161
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 162 - ((64953/100000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_162).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_163 : ((2804527/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 163, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 163, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 162, cos687o2c k) + cos687o2c 163 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 162) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_162
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 163 - ((-986599/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_163).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_164 : ((23009/1600 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 164, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 164, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 163, cos687o2c k) + cos687o2c 164 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 163) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_163
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 164 - ((35809/100000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_164).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_165 : ((15014927/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 165, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 165, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 164, cos687o2c k) + cos687o2c 165 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 164) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_164
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 165 - ((317201/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_165).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_166 : ((7015717/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 166, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 166, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 165, cos687o2c k) + cos687o2c 166 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 165) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_165
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 166 - ((-983393/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_166).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_167 : ((71681/5000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 167, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 167, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 166, cos687o2c k) + cos687o2c 167 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 166) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_166
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 167 - ((152433/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_167).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_168 : ((15040137/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 168, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 168, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 167, cos687o2c k) + cos687o2c 168 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 167) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_167
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 168 - ((704037/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_168).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_169 : ((7044351/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 169, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 169, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 168, cos687o2c k) + cos687o2c 169 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 168) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_168
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 169 - ((-190267/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_169).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_170 : ((14230613/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 170, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 170, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 169, cos687o2c k) + cos687o2c 170 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 169) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_169
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 170 - ((142011/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_170).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_171 : ((7531737/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 171, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 171, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 170, cos687o2c k) + cos687o2c 171 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 170) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_170
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 171 - ((832961/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_171).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_172 : ((2842413/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 172, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 172, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 171, cos687o2c k) + cos687o2c 172 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 171) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_171
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 172 - ((-851309/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_172).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_173 : ((14080533/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 173, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 173, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 172, cos687o2c k) + cos687o2c 173 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 172) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_172
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 173 - ((-16429/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_173).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_174 : ((15042253/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 174, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 174, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 173, cos687o2c k) + cos687o2c 174 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 173) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_173
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 174 - ((48091/50000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_174).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_175 : ((14417317/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 175, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 175, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 174, cos687o2c k) + cos687o2c 175 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 174) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_174
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 175 - ((-156209/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_175).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_176 : ((3482389/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 176, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 176, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 175, cos687o2c k) + cos687o2c 176 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 175) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_175
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 176 - ((-487661/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_176).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_177 : ((14920491/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 177, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 177, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 176, cos687o2c k) + cos687o2c 177 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 176) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_176
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 177 - ((198207/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_177).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_178 : ((14692013/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 178, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 178, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 177, cos687o2c k) + cos687o2c 178 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 177) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_177
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 178 - ((-114189/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_178).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_179 : ((3464413/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 179, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 179, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 178, cos687o2c k) + cos687o2c 179 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 178) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_178
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 179 - ((-834261/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_179).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_180 : ((14657283/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 180, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 180, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 179, cos687o2c k) + cos687o2c 180 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 179) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_179
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 180 - ((799731/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_180).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_181 : ((1870481/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 181, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 181, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 180, cos687o2c k) + cos687o2c 181 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 180) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_180
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 181 - ((61333/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_181).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_182 : ((13963799/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 182, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 182, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 181, cos687o2c k) + cos687o2c 182 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 181) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_181
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 182 - ((-999949/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_182).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_183 : ((14279667/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 183, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 183, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 182, cos687o2c k) + cos687o2c 183 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 182) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_182
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 183 - ((4937/15625 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_183).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_184 : ((7545961/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 184, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 184, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 183, cos687o2c k) + cos687o2c 184 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 183) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_183
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 184 - ((162471/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_184).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_185 : ((7150049/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 185, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 185, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 184, cos687o2c k) + cos687o2c 185 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 184) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_184
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 185 - ((-197931/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_185).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_186 : ((1741573/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 186, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 186, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 185, cos687o2c k) + cos687o2c 186 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 185) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_185
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 186 - ((-183707/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_186).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_187 : ((7463479/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 187, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 187, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 186, cos687o2c k) + cos687o2c 187 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 186) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_186
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 187 - ((497237/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_187).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_188 : ((7385737/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 188, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 188, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 187, cos687o2c k) + cos687o2c 188 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 187) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_187
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 188 - ((-19423/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_188).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_189 : ((3463317/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 189, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 189, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 188, cos687o2c k) + cos687o2c 189 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 188) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_188
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 189 - ((-459053/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_189).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_190 : ((225904/15625 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 190, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 190, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 189, cos687o2c k) + cos687o2c 190 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 189) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_189
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 190 - ((37793/62500 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_190).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_191 : ((377339/25000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 191, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 191, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 190, cos687o2c k) + cos687o2c 191 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 190) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_190
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 191 - ((158951/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_191).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_192 : ((14200143/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 192, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 192, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 191, cos687o2c k) + cos687o2c 192 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 191) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_191
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 192 - ((-893317/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_192).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_193 : ((3487553/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 193, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 193, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 192, cos687o2c k) + cos687o2c 193 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 192) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_192
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 193 - ((-249831/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_193).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_194 : ((3737239/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 194, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 194, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 193, cos687o2c k) + cos687o2c 194 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 193) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_193
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 194 - ((249711/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_194).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_195 : ((7401103/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 195, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 195, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 194, cos687o2c k) + cos687o2c 195 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 194) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_194
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 195 - ((-2933/20000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_195).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_196 : ((6928589/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 196, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 196, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 195, cos687o2c k) + cos687o2c 196 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 195) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_195
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 196 - ((-29529/31250 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_196).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_197 : ((14345893/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 197, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 197, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 196, cos687o2c k) + cos687o2c 197 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 196) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_196
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 197 - ((97763/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_197).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_198 : ((7561941/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 198, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 198, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 197, cos687o2c k) + cos687o2c 198 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 197) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_197
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 198 - ((778089/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_198).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_199 : ((1797487/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 199, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 199, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 198, cos687o2c k) + cos687o2c 199 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 198) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_198
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 199 - ((-371943/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_199).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_200 : ((864437/62500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 200, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 200, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 199, cos687o2c k) + cos687o2c 200 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 199) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_199
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 200 - ((-137201/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_200).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_201 : ((7368143/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 201, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 201, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 200, cos687o2c k) + cos687o2c 201 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 200) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_200
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 201 - ((452697/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_201).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_202 : ((3007219/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 202, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 202, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 201, cos687o2c k) + cos687o2c 202 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 201) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_201
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 202 - ((299909/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_202).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_203 : ((3512997/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 203, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 203, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 202, cos687o2c k) + cos687o2c 203 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 202) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_202
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 203 - ((-984007/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_203).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_204 : ((6995001/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 204, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 204, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 203, cos687o2c k) + cos687o2c 204 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 203) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_203
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 204 - ((-30943/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_204).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_205 : ((7494399/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 205, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 205, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 204, cos687o2c k) + cos687o2c 205 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 204) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_204
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 205 - ((62431/62500 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_205).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_206 : ((7420749/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 206, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 206, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 205, cos687o2c k) + cos687o2c 206 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 205) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_205
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 206 - ((-92/625 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_206).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_207 : ((13870149/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 207, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 207, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 206, cos687o2c k) + cos687o2c 207 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 206) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_206
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 207 - ((-971249/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_207).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_208 : ((3547341/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 208, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 208, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 207, cos687o2c k) + cos687o2c 208 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 207) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_207
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 208 - ((63863/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_208).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_209 : ((755483/50000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 209, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 209, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 208, cos687o2c k) + cos687o2c 209 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 208) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_208
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 209 - ((230099/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_209).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_210 : ((2931239/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 210, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 210, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 209, cos687o2c k) + cos687o2c 210 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 209) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_209
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 210 - ((-90673/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_210).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_211 : ((3448521/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 211, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 211, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 210, cos687o2c k) + cos687o2c 211 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 210) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_210
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 211 - ((-862011/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_211).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_212 : ((7173041/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 212, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 212, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 211, cos687o2c k) + cos687o2c 212 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 211) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_211
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 212 - ((276049/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_212).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_213 : ((189421/12500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 213, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 213, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 212, cos687o2c k) + cos687o2c 213 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 212) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_212
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 213 - ((403849/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_213).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_214 : ((3633407/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 214, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 214, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 213, cos687o2c k) + cos687o2c 214 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 213) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_213
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 214 - ((-38747/62500 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_214).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_215 : ((430257/31250 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 215, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 215, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 214, cos687o2c k) + cos687o2c 215 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 214) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_214
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 215 - ((-95663/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_215).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_216 : ((14429359/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 216, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 216, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 215, cos687o2c k) + cos687o2c 216 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 215) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_215
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 216 - ((132247/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_216).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_217 : ((151689/10000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 217, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 217, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 216, cos687o2c k) + cos687o2c 217 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 216) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_216
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 217 - ((739641/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_217).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_218 : ((7244763/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 218, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 218, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 217, cos687o2c k) + cos687o2c 218 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 217) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_217
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 218 - ((-339637/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_218).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_219 : ((550257/40000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 219, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 219, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 218, cos687o2c k) + cos687o2c 219 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 218) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_218
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 219 - ((-733001/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_219).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_220 : ((1804029/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 220, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 220, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 219, cos687o2c k) + cos687o2c 220 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 219) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_219
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 220 - ((675907/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_220).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_221 : ((7588907/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 221, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 221, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 220, cos687o2c k) + cos687o2c 221 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 220) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_220
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 221 - ((372841/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_221).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_222 : ((14526481/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 222, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 222, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 221, cos687o2c k) + cos687o2c 222 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 221) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_221
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 222 - ((-651233/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_222).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_223 : ((13750217/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 223, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 223, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 222, cos687o2c k) + cos687o2c 223 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 222) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_222
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 223 - ((-194041/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_223).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_224 : ((7177/500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 224, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 224, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 223, cos687o2c k) + cos687o2c 224 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 223) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_223
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 224 - ((603883/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_224).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_225 : ((1517489/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 225, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 225, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 224, cos687o2c k) + cos687o2c 225 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 224) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_224
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 225 - ((82099/100000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_225).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_226 : ((7321749/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 226, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 226, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 225, cos687o2c k) + cos687o2c 226 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 225) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_225
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 226 - ((-132823/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_226).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_227 : ((13768659/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 227, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 227, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 226, cos687o2c k) + cos687o2c 227 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 226) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_226
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 227 - ((-874739/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_227).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_228 : ((14199009/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 228, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 228, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 227, cos687o2c k) + cos687o2c 228 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 227) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_227
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 228 - ((8609/20000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_228).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_229 : ((7564251/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 229, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 229, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 228, cos687o2c k) + cos687o2c 229 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 228) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_228
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 229 - ((929593/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_229).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_230 : ((3707403/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 230, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 230, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 229, cos687o2c k) + cos687o2c 230 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 229) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_229
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 230 - ((-29879/100000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_230).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_231 : ((2770849/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 231, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 231, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 230, cos687o2c k) + cos687o2c 231 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 230) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_230
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 231 - ((-975267/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_231).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_232 : ((6994791/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 232, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 232, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 231, cos687o2c k) + cos687o2c 232 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 231) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_231
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 232 - ((135437/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_232).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_233 : ((749429/50000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 233, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 233, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 232, cos687o2c k) + cos687o2c 233 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 232) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_232
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 233 - ((499549/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_233).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_234 : ((3761413/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 234, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 234, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 233, cos687o2c k) + cos687o2c 234 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 233) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_233
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 234 - ((14293/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_234).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_235 : ((3514709/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 235, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 235, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 234, cos687o2c k) + cos687o2c 235 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 234) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_234
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 235 - ((-246679/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_235).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_236 : ((13786833/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 236, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 236, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 235, cos687o2c k) + cos687o2c 236 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 235) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_235
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 236 - ((-271903/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_236).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_237 : ((3677553/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 237, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 237, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 236, cos687o2c k) + cos687o2c 237 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 236) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_236
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 237 - ((923479/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_237).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_238 : ((15205459/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 238, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 238, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 237, cos687o2c k) + cos687o2c 238 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 237) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_237
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 238 - ((495347/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_238).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_239 : ((3602133/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 239, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 239, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 238, cos687o2c k) + cos687o2c 239 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 238) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_238
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 239 - ((-796827/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_239).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_240 : ((13701383/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 240, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 240, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 239, cos687o2c k) + cos687o2c 240 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 239) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_239
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 240 - ((-707049/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_240).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_241 : ((14300847/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 241, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 241, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 240, cos687o2c k) + cos687o2c 241 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 240) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_240
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 241 - ((149891/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_241).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_242 : ((15180941/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 242, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 242, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 241, cos687o2c k) + cos687o2c 242 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 241) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_241
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 242 - ((440097/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_242).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_243 : ((14847147/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 243, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 243, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 242, cos687o2c k) + cos687o2c 243 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 242) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_242
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 243 - ((-166847/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_243).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_244 : ((13863223/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 244, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 244, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 243, cos687o2c k) + cos687o2c 244 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 243) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_243
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 244 - ((-61489/62500 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_244).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_245 : ((13877333/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 245, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 245, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 244, cos687o2c k) + cos687o2c 245 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 244) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_244
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 245 - ((1421/100000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_245).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_246 : ((14864873/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 246, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 246, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 245, cos687o2c k) + cos687o2c 246 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 245) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_245
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 246 - ((24691/25000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_246).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_247 : ((3798309/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 247, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 247, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 246, cos687o2c k) + cos687o2c 247 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 246) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_246
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 247 - ((328463/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_247).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_248 : ((3581031/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 248, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 248, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 247, cos687o2c k) + cos687o2c 248 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 247) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_247
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 248 - ((-217253/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_248).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_249 : ((13675143/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 249, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 249, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 248, cos687o2c k) + cos687o2c 249 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 248) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_248
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 249 - ((-648881/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_249).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_250 : ((7148277/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 250, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 250, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 249, cos687o2c k) + cos687o2c 250 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 249) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_249
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 250 - ((621511/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_250).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_251 : ((1898439/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 251, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 251, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 250, cos687o2c k) + cos687o2c 251 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 250) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_250
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 251 - ((445529/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_251).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_252 : ((7462211/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 252, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 252, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 251, cos687o2c k) + cos687o2c 252 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 251) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_251
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 252 - ((-26299/100000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_252).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_253 : ((6962937/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 253, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 253, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 252, cos687o2c k) + cos687o2c 253 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 252) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_252
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 253 - ((-62403/62500 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_253).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_254 : ((13766419/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 254, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 254, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 253, cos687o2c k) + cos687o2c 254 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 253) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_253
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 254 - ((-31871/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_254).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_255 : ((1836821/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 255, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 255, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 254, cos687o2c k) + cos687o2c 255 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 254) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_254
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 255 - ((928249/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_255).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_256 : ((15265277/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 256, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 256, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 255, cos687o2c k) + cos687o2c 256 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 255) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_255
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 256 - ((570809/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_256).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_257 : ((14597057/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 257, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 257, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 256, cos687o2c k) + cos687o2c 257 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 256) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_256
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 257 - ((-16703/25000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_257).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_258 : ((3429231/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 258, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 258, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 257, cos687o2c k) + cos687o2c 258 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 257) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_257
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 258 - ((-880033/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_258).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_259 : ((2793407/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 259, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 259, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 258, cos687o2c k) + cos687o2c 259 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 258) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_258
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 259 - ((250211/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_259).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_260 : ((7483459/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 260, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 260, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 259, cos687o2c k) + cos687o2c 260 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 259) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_259
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 260 - ((999983/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_260).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_261 : ((15210689/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 261, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 261, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 260, cos687o2c k) + cos687o2c 261 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 260) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_260
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 261 - ((243871/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_261).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_262 : ((573389/40000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 262, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 262, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 261, cos687o2c k) + cos687o2c 262 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 261) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_261
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 262 - ((-109483/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_262).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_263 : ((13641507/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 263, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 263, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 262, cos687o2c k) + cos687o2c 263 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 262) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_262
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 263 - ((-346559/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_263).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_264 : ((221151/15625 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 264, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 264, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 263, cos687o2c k) + cos687o2c 264 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 263) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_263
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 264 - ((512257/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_264).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_265 : ((15118477/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 265, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 265, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 264, cos687o2c k) + cos687o2c 265 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 264) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_264
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 265 - ((964913/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_265).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_266 : ((3025939/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 266, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 266, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 265, cos687o2c k) + cos687o2c 266 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 265) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_265
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 266 - ((5659/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_266).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_267 : ((14172271/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 267, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 267, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 266, cos687o2c k) + cos687o2c 267 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 266) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_266
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 267 - ((-239331/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_267).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_268 : ((13624239/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 268, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 268, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 267, cos687o2c k) + cos687o2c 268 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 267) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_267
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 268 - ((-136983/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_268).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_269 : ((14267929/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 269, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 269, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 268, cos687o2c k) + cos687o2c 269 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 268) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_268
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 269 - ((64379/100000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_269).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_270 : ((121501/8000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 270, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 270, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 269, cos687o2c k) + cos687o2c 270 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 269) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_269
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 270 - ((229949/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_270).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_271 : ((15085379/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 271, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 271, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 270, cos687o2c k) + cos687o2c 271 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 270) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_270
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 271 - ((-51073/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_271).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_272 : ((881617/62500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 272, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 272, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 271, cos687o2c k) + cos687o2c 272 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 271) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_271
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 272 - ((-979407/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_272).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_273 : ((6807251/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 273, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 273, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 272, cos687o2c k) + cos687o2c 273 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 272) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_272
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 273 - ((-49127/100000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_273).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_274 : ((178631/12500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 274, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 274, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 273, cos687o2c k) + cos687o2c 274 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 273) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_273
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 274 - ((338039/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_274).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_275 : ((3040451/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 275, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 275, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 274, cos687o2c k) + cos687o2c 275 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 274) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_274
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 275 - ((1459/1600 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_275).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_276 : ((1510331/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 276, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 276, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 275, cos687o2c k) + cos687o2c 276 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 275) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_275
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 276 - ((-19769/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_276).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_277 : ((14129419/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 277, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 277, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 276, cos687o2c k) + cos687o2c 277 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 276) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_276
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 277 - ((-973791/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_277).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_278 : ((1359609/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 278, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 278, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 277, cos687o2c k) + cos687o2c 278 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 277) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_277
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 278 - ((-533229/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_278).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_279 : ((14217727/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 279, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 279, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 278, cos687o2c k) + cos687o2c 279 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 278) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_278
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 279 - ((621737/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_279).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_280 : ((7581969/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 280, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 280, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 279, cos687o2c k) + cos687o2c 280 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 279) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_279
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 280 - ((946311/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_280).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_281 : ((7590443/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 281, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 281, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 280, cos687o2c k) + cos687o2c 281 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 280) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_280
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 281 - ((2131/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_281).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_282 : ((1780949/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 282, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 282, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 281, cos687o2c k) + cos687o2c 282 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 281) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_281
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 282 - ((-466597/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_282).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_283 : ((3396563/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 283, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 283, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 282, cos687o2c k) + cos687o2c 283 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 282) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_282
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 283 - ((-16531/25000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_283).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_284 : ((219626/15625 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 284, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 284, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 283, cos687o2c k) + cos687o2c 284 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 283) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_283
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 284 - ((58739/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_284).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_285 : ((7524033/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 285, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 285, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 284, cos687o2c k) + cos687o2c 285 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 284) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_284
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 285 - ((496051/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_285).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_286 : ((15287471/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 286, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 286, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 285, cos687o2c k) + cos687o2c 286 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 285) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_285
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 286 - ((47901/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_286).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_287 : ((1808731/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 287, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 287, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 286, cos687o2c k) + cos687o2c 287 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 286) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_286
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 287 - ((-817523/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_287).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_288 : ((3408467/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 288, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 288, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 287, cos687o2c k) + cos687o2c 288 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 287) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_287
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 288 - ((-20897/25000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_288).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_289 : ((553333/40000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 289, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 289, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 288, cos687o2c k) + cos687o2c 289 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 288) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_288
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 289 - ((199557/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_289).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_290 : ((2963293/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 290, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 290, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 289, cos687o2c k) + cos687o2c 290 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 289) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_289
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 290 - ((24581/25000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_290).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_291 : ((1919679/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 291, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 291, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 290, cos687o2c k) + cos687o2c 291 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 290) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_290
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 291 - ((541067/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_291).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_292 : ((462099/31250 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 292, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 292, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 291, cos687o2c k) + cos687o2c 292 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 291) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_291
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 292 - ((-142541/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_292).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_293 : ((13809093/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 293, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 293, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 292, cos687o2c k) + cos687o2c 293 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 292) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_292
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 293 - ((-39119/40000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_293).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_294 : ((13619947/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 294, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 294, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 293, cos687o2c k) + cos687o2c 294 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 293) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_293
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 294 - ((-94523/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_294).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_295 : ((14448221/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 295, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 295, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 294, cos687o2c k) + cos687o2c 295 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 294) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_294
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 295 - ((414187/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_295).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_296 : ((3058237/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 296, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 296, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 295, cos687o2c k) + cos687o2c 296 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 295) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_295
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 296 - ((105383/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_296).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_297 : ((3027229/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 297, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 297, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 296, cos687o2c k) + cos687o2c 297 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 296) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_296
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 297 - ((-7747/50000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_297).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_298 : ((2833963/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 298, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 298, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 297, cos687o2c k) + cos687o2c 298 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 297) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_297
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 298 - ((-96623/100000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_298).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_299 : ((13540409/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 299, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 299, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 298, cos687o2c k) + cos687o2c 299 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 298) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_298
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 299 - ((-314653/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_299).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_300 : ((279797/20000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 300, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 300, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 299, cos687o2c k) + cos687o2c 300 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 299) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_299
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 300 - ((449541/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_300).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_301 : ((14989007/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 301, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 301, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 300, cos687o2c k) + cos687o2c 301 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 300) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_300
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 301 - ((999257/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_301).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_302 : ((3074359/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 302, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 302, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 301, cos687o2c k) + cos687o2c 302 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 301) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_301
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 302 - ((47861/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_302).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_303 : ((14695473/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 303, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 303, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 302, cos687o2c k) + cos687o2c 303 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 302) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_302
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 303 - ((-338111/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_303).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_304 : ((6870557/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 304, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 304, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 303, cos687o2c k) + cos687o2c 304 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 303) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_303
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 304 - ((-954259/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_304).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_305 : ((13602343/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 305, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 305, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 304, cos687o2c k) + cos687o2c 305 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 304) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_304
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 305 - ((-138671/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_305).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_306 : ((7217839/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 306, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 306, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 305, cos687o2c k) + cos687o2c 306 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 305) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_305
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 306 - ((166687/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_306).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_307 : ((238996/15625 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 307, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 307, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 306, cos687o2c k) + cos687o2c 307 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 306) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_306
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 307 - ((430083/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_307).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_308 : ((3803567/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 308, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 308, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 307, cos687o2c k) + cos687o2c 308 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 307) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_307
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 308 - ((-2543/31250 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_308).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_309 : ((14283981/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 309, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 309, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 308, cos687o2c k) + cos687o2c 309 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 308) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_308
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 309 - ((-930187/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_309).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_310 : ((13541363/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 310, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 310, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 309, cos687o2c k) + cos687o2c 310 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 309) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_309
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 310 - ((-371259/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_310).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_311 : ((13807501/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 311, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 311, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 310, cos687o2c k) + cos687o2c 311 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 310) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_310
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 311 - ((133119/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_311).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_312 : ((462117/31250 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 312, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 312, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 311, cos687o2c k) + cos687o2c 312 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 311) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_311
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 312 - ((980343/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_312).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_313 : ((15408787/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 313, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 313, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 312, cos687o2c k) + cos687o2c 313 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 312) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_312
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 313 - ((621143/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_313).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_314 : ((2999183/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 314, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 314, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 313, cos687o2c k) + cos687o2c 314 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 313) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_313
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 314 - ((-103193/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_314).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_315 : ((13997223/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 315, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 315, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 314, cos687o2c k) + cos687o2c 315 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 314) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_314
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 315 - ((-15603/15625 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_315).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_316 : ((2697437/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 316, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 316, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 315, cos687o2c k) + cos687o2c 316 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 315) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_315
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 316 - ((-254969/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_316).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_317 : ((7004961/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 317, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 317, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 316, cos687o2c k) + cos687o2c 317 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 316) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_316
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 317 - ((522837/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_317).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_318 : ((7503973/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 318, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 318, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 317, cos687o2c k) + cos687o2c 318 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 317) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_317
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 318 - ((249531/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_318).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_319 : ((15425633/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 319, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 319, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 318, cos687o2c k) + cos687o2c 319 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 318) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_318
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 319 - ((417787/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_319).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_320 : ((926567/62500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 320, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 320, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 319, cos687o2c k) + cos687o2c 320 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 319) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_319
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 320 - ((-600461/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_320).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_321 : ((3458869/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 321, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 321, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 320, cos687o2c k) + cos687o2c 321 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 320) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_320
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 321 - ((-123687/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_321).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_322 : ((13485627/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 322, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 322, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 321, cos687o2c k) + cos687o2c 322 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 321) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_321
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 322 - ((-349749/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_322).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_323 : ((14135707/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 323, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 323, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 322, cos687o2c k) + cos687o2c 323 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 322) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_322
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 323 - ((32509/50000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_323).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_324 : ((15115901/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 324, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 324, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 323, cos687o2c k) + cos687o2c 324 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 323) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_323
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 324 - ((490147/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_324).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_325 : ((15424109/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 325, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 325, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 324, cos687o2c k) + cos687o2c 325 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 324) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_324
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 325 - ((77077/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_325).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_326 : ((14748329/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 326, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 326, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 325, cos687o2c k) + cos687o2c 326 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 325) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_325
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 326 - ((-4223/6250 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_326).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_327 : ((6886513/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 327, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 327, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 326, cos687o2c k) + cos687o2c 327 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 326) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_326
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 327 - ((-975203/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_327).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_328 : ((13478593/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 328, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 328, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 327, cos687o2c k) + cos687o2c 328 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 327) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_327
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 328 - ((-294333/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_328).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_329 : ((7078927/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 329, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 329, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 328, cos687o2c k) + cos687o2c 329 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 328) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_328
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 329 - ((679361/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_329).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_330 : ((378349/25000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 330, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 330, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 329, cos687o2c k) + cos687o2c 330 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 329) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_329
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 330 - ((488103/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_330).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_331 : ((3088333/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 331, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 331, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 330, cos687o2c k) + cos687o2c 331 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 330) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_330
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 331 - ((61561/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_331).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_332 : ((14779691/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 332, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 332, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 331, cos687o2c k) + cos687o2c 332 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 331) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_331
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 332 - ((-330937/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_332).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_333 : ((2759353/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 333, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 333, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 332, cos687o2c k) + cos687o2c 333 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 332) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_332
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 333 - ((-491413/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_333).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_334 : ((13448873/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 334, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 334, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 333, cos687o2c k) + cos687o2c 334 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 333) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_333
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 334 - ((-21737/62500 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_334).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_335 : ((14071101/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 335, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 335, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 334, cos687o2c k) + cos687o2c 335 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 334) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_334
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 335 - ((77791/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_335).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_336 : ((1506323/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 336, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 336, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 335, cos687o2c k) + cos687o2c 336 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 335) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_335
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 336 - ((992229/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_336).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_337 : ((15475661/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 337, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 337, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 336, cos687o2c k) + cos687o2c 337 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 336) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_336
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 337 - ((412531/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_337).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_338 : ((14917103/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 338, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 338, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 337, cos687o2c k) + cos687o2c 338 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 337) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_337
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 338 - ((-279229/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_338).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_339 : ((1391767/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 339, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 339, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 338, cos687o2c k) + cos687o2c 339 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 338) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_338
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 339 - ((-999333/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_339).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_340 : ((6709267/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 340, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 340, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 339, cos687o2c k) + cos687o2c 340 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 339) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_339
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 340 - ((-124759/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_340).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_341 : ((3471449/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 341, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 341, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 340, cos687o2c k) + cos687o2c 341 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 340) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_340
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 341 - ((233681/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_341).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_342 : ((14882607/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 342, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 342, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 341, cos687o2c k) + cos687o2c 342 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 341) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_341
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 342 - ((996911/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_342).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_343 : ((15484903/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 343, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 343, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 342, cos687o2c k) + cos687o2c 343 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 342) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_342
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 343 - ((150599/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_343).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_344 : ((7569311/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 344, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 344, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 343, cos687o2c k) + cos687o2c 344 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 343) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_343
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 344 - ((-346181/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_344).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_345 : ((2832533/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 345, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 345, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 344, cos687o2c k) + cos687o2c 345 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 344) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_344
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 345 - ((-975857/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_345).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_346 : ((1680931/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 346, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 346, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 345, cos687o2c k) + cos687o2c 346 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 345) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_345
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 346 - ((-715117/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_346).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_347 : ((13640673/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 347, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 347, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 346, cos687o2c k) + cos687o2c 347 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 346) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_346
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 347 - ((7733/40000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_347).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_348 : ((14566333/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 348, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 348, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 347, cos687o2c k) + cos687o2c 348 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 347) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_347
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 348 - ((2893/3125 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_348).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_349 : ((15392743/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 349, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 349, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 348, cos687o2c k) + cos687o2c 349 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 348) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_348
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 349 - ((82651/100000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_349).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_350 : ((15382701/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 350, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 350, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 349, cos687o2c k) + cos687o2c 350 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 349) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_349
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 350 - ((-4971/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_350).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_351 : ((2909317/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 351, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 351, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 350, cos687o2c k) + cos687o2c 351 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 350) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_350
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 351 - ((-52251/62500 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_351).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_352 : ((425751/31250 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 352, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 352, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 351, cos687o2c k) + cos687o2c 352 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 351) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_351
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 352 - ((-922453/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_352).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_353 : ((13425349/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 353, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 353, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 352, cos687o2c k) + cos687o2c 353 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 352) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_352
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 353 - ((-198583/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_353).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_354 : ((7061343/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 354, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 354, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 353, cos687o2c k) + cos687o2c 354 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 353) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_353
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 354 - ((697437/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_354).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_355 : ((15108177/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 355, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 355, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 354, cos687o2c k) + cos687o2c 355 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 354) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_354
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 355 - ((985591/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_355).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_356 : ((3105819/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 356, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 356, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 355, cos687o2c k) + cos687o2c 356 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 355) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_355
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 356 - ((210509/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_356).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_357 : ((939023/62500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 357, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 357, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 356, cos687o2c k) + cos687o2c 357 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 356) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_356
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 357 - ((-504627/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_357).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_358 : ((14027547/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 358, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 358, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 357, cos687o2c k) + cos687o2c 358 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 357) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_357
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 358 - ((-996721/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_358).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_359 : ((13388103/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 359, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 359, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 358, cos687o2c k) + cos687o2c 359 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 358) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_358
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 359 - ((-39959/62500 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_359).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_360 : ((13646889/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 360, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 360, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 359, cos687o2c k) + cos687o2c 360 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 359) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_359
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 360 - ((129443/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_360).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_361 : ((2916811/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 361, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 361, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 360, cos687o2c k) + cos687o2c 361 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 360) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_360
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 361 - ((468633/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_361).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_362 : ((1541259/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 362, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 362, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 361, cos687o2c k) + cos687o2c 362 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 361) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_361
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 362 - ((165727/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_362).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_363 : ((3860393/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 363, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 363, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 362, cos687o2c k) + cos687o2c 363 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 362) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_362
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 363 - ((14541/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_363).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_364 : ((3662093/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 364, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 364, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 363, cos687o2c k) + cos687o2c 364 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 363) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_363
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 364 - ((-7931/10000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_364).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_365 : ((1368931/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 365, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 365, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 364, cos687o2c k) + cos687o2c 365 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 364) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_364
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 365 - ((-479481/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_365).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_366 : ((13352423/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 366, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 366, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 365, cos687o2c k) + cos687o2c 366 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 365) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_365
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 366 - ((-336787/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_366).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_367 : ((6955893/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 367, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 367, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 366, cos687o2c k) + cos687o2c 367 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 366) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_366
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 367 - ((559463/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_367).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_368 : ((14910789/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 368, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 368, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 367, cos687o2c k) + cos687o2c 368 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 367) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_367
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 368 - ((999103/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_368).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_369 : ((777013/50000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 369, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 369, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 368, cos687o2c k) + cos687o2c 369 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 368) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_368
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 369 - ((629571/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_369).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_370 : ((15294067/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 370, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 370, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 369, cos687o2c k) + cos687o2c 370 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 369) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_369
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 370 - ((-246093/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_370).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_371 : ((14370987/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 371, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 371, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 370, cos687o2c k) + cos687o2c 371 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 370) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_370
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 371 - ((-46149/50000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_371).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_372 : ((13507873/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 372, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 372, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 371, cos687o2c k) + cos687o2c 372 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 371) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_371
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 372 - ((-431507/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_372).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_373 : ((836813/62500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 373, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 373, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 372, cos687o2c k) + cos687o2c 373 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 372) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_372
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 373 - ((-23753/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_373).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_374 : ((14106687/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 374, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 374, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 373, cos687o2c k) + cos687o2c 374 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 373) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_373
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 374 - ((717779/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_374).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_375 : ((15095793/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 375, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 375, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 374, cos687o2c k) + cos687o2c 375 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 374) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_374
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 375 - ((494603/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_375).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_376 : ((3116593/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 376, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 376, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 375, cos687o2c k) + cos687o2c 376 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 375) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_375
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 376 - ((60909/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_376).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_377 : ((7595171/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 377, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 377, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 376, cos687o2c k) + cos687o2c 377 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 376) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_376
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 377 - ((-392523/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_377).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_378 : ((1422321/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 378, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 378, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 377, cos687o2c k) + cos687o2c 378 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 377) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_377
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 378 - ((-120879/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_378).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_379 : ((3356767/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 379, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 379, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 378, cos687o2c k) + cos687o2c 379 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 378) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_378
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 379 - ((-398021/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_379).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_380 : ((2682273/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 380, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 380, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 379, cos687o2c k) + cos687o2c 380 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 379) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_379
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 380 - ((-15603/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_380).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_381 : ((14186539/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 381, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 381, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 380, cos687o2c k) + cos687o2c 381 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 380) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_380
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 381 - ((387637/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_381).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_382 : ((15163037/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 382, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 382, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 381, cos687o2c k) + cos687o2c 382 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 381) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_381
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 382 - ((488299/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_382).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_383 : ((975207/62500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 383, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 383, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 382, cos687o2c k) + cos687o2c 383 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 382) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_382
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 383 - ((3523/8000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_383).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_384 : ((15177549/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 384, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 384, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 383, cos687o2c k) + cos687o2c 384 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 383) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_383
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 384 - ((-425663/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_384).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_385 : ((14205573/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 385, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 385, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 384, cos687o2c k) + cos687o2c 385 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 384) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_384
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 385 - ((-242969/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_385).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_386 : ((6705699/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 386, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 386, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 385, cos687o2c k) + cos687o2c 386 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 385) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_385
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 386 - ((-31763/40000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_386).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_387 : ((2676511/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 387, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 387, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 386, cos687o2c k) + cos687o2c 387 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 386) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_386
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 387 - ((-28743/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_387).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_388 : ((14138811/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 388, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 388, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 387, cos687o2c k) + cos687o2c 388 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 387) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_387
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 388 - ((189089/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_388).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_389 : ((1512411/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 389, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 389, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 388, cos687o2c k) + cos687o2c 389 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 388) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_388
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 389 - ((985399/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_389).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_390 : ((7809489/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 390, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 390, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 389, cos687o2c k) + cos687o2c 390 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 389) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_389
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 390 - ((61871/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_390).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_391 : ((3052977/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 391, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 391, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 390, cos687o2c k) + cos687o2c 391 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 390) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_390
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 391 - ((-353993/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_391).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_392 : ((894953/62500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 392, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 392, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 391, cos687o2c k) + cos687o2c 392 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 391) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_391
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 392 - ((-945537/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_392).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_393 : ((6731651/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 393, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 393, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 392, cos687o2c k) + cos687o2c 393 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 392) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_392
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 393 - ((-427923/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_393).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_394 : ((2661913/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 394, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 394, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 393, cos687o2c k) + cos687o2c 394 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 393) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_393
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 394 - ((-153637/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_394).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_395 : ((13966181/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 395, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 395, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 394, cos687o2c k) + cos687o2c 395 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 394) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_394
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 395 - ((164179/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_395).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_396 : ((748299/50000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 396, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 396, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 395, cos687o2c k) + cos687o2c 396 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 395) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_395
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 396 - ((999899/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_396).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_397 : ((15602641/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 397, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 397, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 396, cos687o2c k) + cos687o2c 397 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 396) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_396
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 397 - ((636761/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_397).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_398 : ((15429529/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 398, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 398, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 397, cos687o2c k) + cos687o2c 398 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 397) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_397
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 398 - ((-43253/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_398).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_399 : ((116553/8000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 399, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 399, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 398, cos687o2c k) + cos687o2c 399 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 398) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_398
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 399 - ((-53769/62500 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_399).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_400 : ((13621337/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 400, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 400, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 399, cos687o2c k) + cos687o2c 400 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 399) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_399
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 400 - ((-118461/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_400).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_401 : ((1324269/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 401, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 401, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 400, cos687o2c k) + cos687o2c 401 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 400) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_400
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 401 - ((-378547/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_401).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_402 : ((13693063/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 402, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 402, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 401, cos687o2c k) + cos687o2c 402 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 401) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_401
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 402 - ((450473/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_402).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_403 : ((14661857/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 403, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 403, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 402, cos687o2c k) + cos687o2c 403 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 402) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_402
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 403 - ((484447/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_403).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_404 : ((15486403/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 404, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 404, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 403, cos687o2c k) + cos687o2c 404 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 403) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_403
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 404 - ((412323/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_404).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_405 : ((3901597/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 405, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 405, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 404, cos687o2c k) + cos687o2c 405 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 404) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_404
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 405 - ((24017/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_405).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_406 : ((14941859/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 406, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 406, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 405, cos687o2c k) + cos687o2c 406 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 405) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_405
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 406 - ((-664429/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_406).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_407 : ((13941759/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 407, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 407, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 406, cos687o2c k) + cos687o2c 407 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 406) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_406
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 407 - ((-1 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_407).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_408 : ((132771/10000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 408, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 408, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 407, cos687o2c k) + cos687o2c 408 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 407) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_407
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 408 - ((-664559/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_408).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_409 : ((6695369/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 409, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 409, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 408, cos687o2c k) + cos687o2c 409 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 408) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_408
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 409 - ((56869/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_409).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_410 : ((2841137/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 410, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 410, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 409, cos687o2c k) + cos687o2c 410 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 409) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_409
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 410 - ((815047/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_410).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_411 : ((759087/50000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 411, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 411, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 410, cos687o2c k) + cos687o2c 411 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 410) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_410
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 411 - ((195231/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_411).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_412 : ((3919031/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 412, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 412, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 411, cos687o2c k) + cos687o2c 412 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 411) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_411
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 412 - ((123621/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_412).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_413 : ((48018/3125 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 413, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 413, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 412, cos687o2c k) + cos687o2c 413 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 412) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_412
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 413 - ((-38783/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_413).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_414 : ((7227229/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 414, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 414, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 413, cos687o2c k) + cos687o2c 414 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 413) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_413
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 414 - ((-455601/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_414).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_415 : ((1353491/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 415, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 415, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 414, cos687o2c k) + cos687o2c 415 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 414) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_414
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 415 - ((-114931/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_415).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_416 : ((264027/20000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 416, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 416, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 415, cos687o2c k) + cos687o2c 416 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 415) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_415
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 416 - ((-16673/50000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_416).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_417 : ((13667257/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 417, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 417, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 416, cos687o2c k) + cos687o2c 417 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 416) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_416
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 417 - ((466007/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_417).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_418 : ((146327/10000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 418, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 418, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 417, cos687o2c k) + cos687o2c 418 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 417) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_417
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 418 - ((965543/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_418).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_419 : ((1548117/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 419, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 419, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 418, cos687o2c k) + cos687o2c 419 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 418) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_418
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 419 - ((84857/100000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_419).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_420 : ((979643/62500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 420, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 420, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 419, cos687o2c k) + cos687o2c 420 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 419) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_419
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 420 - ((96609/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_420).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_421 : ((3772793/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 421, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 421, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 420, cos687o2c k) + cos687o2c 421 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 420) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_420
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 421 - ((-72877/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_421).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_422 : ((14099957/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 422, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 422, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 421, cos687o2c k) + cos687o2c 422 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 421) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_421
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 422 - ((-198223/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_422).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_423 : ((6661013/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 423, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 423, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 422, cos687o2c k) + cos687o2c 423 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 422) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_422
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 423 - ((-777831/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_423).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_424 : ((13241911/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 424, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 424, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 423, cos687o2c k) + cos687o2c 424 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 423) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_423
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 424 - ((-16003/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_424).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_425 : ((13907997/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 425, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 425, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 424, cos687o2c k) + cos687o2c 425 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 424) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_424
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 425 - ((333093/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_425).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_426 : ((2981461/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 426, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 426, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 425, cos687o2c k) + cos687o2c 426 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 425) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_425
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 426 - ((62463/62500 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_426).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_427 : ((1562443/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 427, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 427, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 426, cos687o2c k) + cos687o2c 427 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 426) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_426
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 427 - ((28689/40000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_427).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_428 : ((15620661/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 428, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 428, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 427, cos687o2c k) + cos687o2c 428 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 427) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_427
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 428 - ((-3669/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_428).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_429 : ((7449751/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 429, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 429, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 428, cos687o2c k) + cos687o2c 429 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 428) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_428
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 429 - ((-721059/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_429).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_430 : ((1389999/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 430, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 430, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 429, cos687o2c k) + cos687o2c 430 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 429) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_429
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 430 - ((-249853/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_430).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_431 : ((13226629/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 431, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 431, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 430, cos687o2c k) + cos687o2c 431 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 430) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_430
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 431 - ((-673261/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_431).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_432 : ((3320987/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 432, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 432, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 431, cos687o2c k) + cos687o2c 432 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 431) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_431
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 432 - ((57419/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_432).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_433 : ((3509061/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 433, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 433, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 432, cos687o2c k) + cos687o2c 433 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 432) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_432
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 433 - ((188099/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_433).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_434 : ((751673/50000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 434, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 434, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 433, cos687o2c k) + cos687o2c 434 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 433) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_433
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 434 - ((249329/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_434).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_435 : ((7841439/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 435, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 435, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 434, cos687o2c k) + cos687o2c 435 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 434) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_434
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 435 - ((324759/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_435).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_436 : ((624043/40000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 436, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 436, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 435, cos687o2c k) + cos687o2c 436 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 435) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_435
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 436 - ((-81703/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_436).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_437 : ((14837473/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 437, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 437, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 436, cos687o2c k) + cos687o2c 437 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 436) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_436
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 437 - ((-381751/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_437).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_438 : ((13840823/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 438, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 438, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 437, cos687o2c k) + cos687o2c 438 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 437) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_437
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 438 - ((-19931/20000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_438).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_439 : ((412287/31250 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 439, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 439, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 438, cos687o2c k) + cos687o2c 439 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 438) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_438
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 439 - ((-647539/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_439).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_440 : ((13270223/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 440, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 440, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 439, cos687o2c k) + cos687o2c 440 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 439) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_439
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 440 - ((77139/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_440).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_441 : ((7013001/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 441, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 441, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 440, cos687o2c k) + cos687o2c 441 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 440) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_440
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 441 - ((755879/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_441).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_442 : ((93899/6250 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 442, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 442, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 441, cos687o2c k) + cos687o2c 442 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 441) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_441
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 442 - ((498969/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_442).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_443 : ((15690829/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 443, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 443, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 442, cos687o2c k) + cos687o2c 443 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 442) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_442
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 443 - ((667089/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_443).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_444 : ((7823257/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 444, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 444, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 443, cos687o2c k) + cos687o2c 444 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 443) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_443
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 444 - ((-8843/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_444).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_445 : ((14917317/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 445, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 445, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 444, cos687o2c k) + cos687o2c 445 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 444) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_444
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 445 - ((-729097/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_445).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_446 : ((6958683/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 446, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 446, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 445, cos687o2c k) + cos687o2c 446 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 445) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_445
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 446 - ((-999851/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_446).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_447 : ((13210983/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 447, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 447, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 446, cos687o2c k) + cos687o2c 447 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 446) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_446
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 447 - ((-706283/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_447).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_448 : ((13194269/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 448, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 448, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 447, cos687o2c k) + cos687o2c 448 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 447) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_447
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 448 - ((-8307/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_448).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_449 : ((13875261/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 449, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 449, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 448, cos687o2c k) + cos687o2c 449 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 448) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_448
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 449 - ((170273/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_449).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_450 : ((3718379/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 450, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 450, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 449, cos687o2c k) + cos687o2c 450 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 449) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_449
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 450 - ((199671/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_450).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_451 : ((1954367/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 451, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 451, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 450, cos687o2c k) + cos687o2c 451 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 450) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_450
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 451 - ((9519/12500 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_451).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_452 : ((7869757/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 452, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 452, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 451, cos687o2c k) + cos687o2c 452 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 451) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_451
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 452 - ((52339/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_452).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_453 : ((7565419/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 453, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 453, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 452, cos687o2c k) + cos687o2c 453 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 452) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_452
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 453 - ((-9509/15625 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_453).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_454 : ((1414337/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 454, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 454, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 453, cos687o2c k) + cos687o2c 454 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 453) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_453
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 454 - ((-123421/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_454).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_455 : ((13316069/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 455, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 455, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 454, cos687o2c k) + cos687o2c 455 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 454) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_454
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 455 - ((-827201/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_455).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_456 : ((13097751/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 456, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 456, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 455, cos687o2c k) + cos687o2c 456 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 455) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_455
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 456 - ((-109109/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_456).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_457 : ((850331/62500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 457, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 457, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 456, cos687o2c k) + cos687o2c 457 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 456) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_456
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 457 - ((101529/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_457).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_458 : ((2912829/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 458, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 458, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 457, cos687o2c k) + cos687o2c 458 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 457) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_457
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 458 - ((958949/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_458).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_459 : ((15459349/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 459, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 459, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 458, cos687o2c k) + cos687o2c 459 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 458) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_458
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 459 - ((111913/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_459).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_460 : ((1581301/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 460, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 460, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 459, cos687o2c k) + cos687o2c 460 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 459) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_459
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 460 - ((353761/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_460).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_461 : ((3859487/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 461, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 461, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 460, cos687o2c k) + cos687o2c 461 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 460) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_460
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 461 - ((-187481/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_461).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_462 : ((3633503/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 462, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 462, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 461, cos687o2c k) + cos687o2c 462 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 461) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_461
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 462 - ((-225959/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_462).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_463 : ((1697343/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 463, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 463, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 462, cos687o2c k) + cos687o2c 463 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 462) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_462
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 463 - ((-29849/31250 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_463).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_464 : ((13073867/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 464, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 464, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 463, cos687o2c k) + cos687o2c 464 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 463) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_463
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 464 - ((-504777/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_464).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_465 : ((2656523/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 465, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 465, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 464, cos687o2c k) + cos687o2c 465 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 464) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_464
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 465 - ((13053/62500 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_465).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_466 : ((14094943/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 466, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 466, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 465, cos687o2c k) + cos687o2c 466 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 465) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_465
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 466 - ((203107/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_466).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_467 : ((15088371/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 467, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 467, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 466, cos687o2c k) + cos687o2c 467 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 466) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_466
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 467 - ((124191/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_467).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_468 : ((393733/25000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 468, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 468, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 467, cos687o2c k) + cos687o2c 468 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 467) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_467
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 468 - ((661049/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_468).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_469 : ((3147647/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 469, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 469, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 468, cos687o2c k) + cos687o2c 469 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 468) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_468
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 469 - ((-2197/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_469).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_470 : ((602477/40000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 470, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 470, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 469, cos687o2c k) + cos687o2c 470 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 469) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_469
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 470 - ((-67621/100000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_470).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_471 : ((7033317/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 471, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 471, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 470, cos687o2c k) + cos687o2c 471 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 470) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_470
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 471 - ((-995191/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_471).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_472 : ((10607/800 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 472, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 472, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 471, cos687o2c k) + cos687o2c 472 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 471) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_471
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 472 - ((-100973/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_472).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_473 : ((13046867/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 473, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 473, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 472, cos687o2c k) + cos687o2c 473 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 472) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_472
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 473 - ((-211783/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_473).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_474 : ((846047/62500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 474, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 474, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 473, cos687o2c k) + cos687o2c 474 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 473) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_473
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 474 - ((97997/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_474).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_475 : ((14481129/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 475, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 475, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 474, cos687o2c k) + cos687o2c 475 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 474) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_474
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 475 - ((944477/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_475).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_476 : ((7703427/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 476, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 476, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 475, cos687o2c k) + cos687o2c 476 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 475) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_475
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 476 - ((37033/40000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_476).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_477 : ((7926401/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 477, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 477, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 476, cos687o2c k) + cos687o2c 477 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 476) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_476
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 477 - ((13939/31250 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_477).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_478 : ((3899619/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 478, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 478, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 477, cos687o2c k) + cos687o2c 478 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 477) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_477
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 478 - ((-127113/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_478).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_479 : ((7385367/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 479, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 479, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 478, cos687o2c k) + cos687o2c 479 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 478) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_478
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 479 - ((-413821/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_479).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_480 : ((6888943/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 480, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 480, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 479, cos687o2c k) + cos687o2c 480 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 479) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_479
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 480 - ((-248187/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_480).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_481 : ((20971/1600 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 481, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 481, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 480, cos687o2c k) + cos687o2c 481 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 480) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_480
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 481 - ((-670911/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_481).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_482 : ((2616951/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 482, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 482, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 481, cos687o2c k) + cos687o2c 482 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 481) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_481
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 482 - ((-1101/50000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_482).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_483 : ((13721101/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 483, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 483, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 482, cos687o2c k) + cos687o2c 483 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 482) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_482
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 483 - ((318223/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_483).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_484 : ((14706509/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 484, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 484, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 483, cos687o2c k) + cos687o2c 484 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 483) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_483
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 484 - ((246377/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_484).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_485 : ((1556489/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 485, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 485, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 484, cos687o2c k) + cos687o2c 485 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 484) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_484
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 485 - ((858481/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_485).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_486 : ((1588387/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 486, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 486, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 485, cos687o2c k) + cos687o2c 486 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 485) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_485
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 486 - ((7977/25000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_486).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_487 : ((7755819/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 487, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 487, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 486, cos687o2c k) + cos687o2c 487 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 486) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_486
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 487 - ((-93033/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_487).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_488 : ((7313401/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 488, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 488, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 487, cos687o2c k) + cos687o2c 488 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 487) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_487
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 488 - ((-13824/15625 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_488).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_489 : ((1365043/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 489, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 489, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 488, cos687o2c k) + cos687o2c 489 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 488) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_488
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 489 - ((-61017/62500 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_489).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_490 : ((13044519/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 490, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 490, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 489, cos687o2c k) + cos687o2c 490 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 489) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_489
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 490 - ((-605811/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_490).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_491 : ((13093941/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 491, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 491, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 490, cos687o2c k) + cos687o2c 491 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 490) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_490
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 491 - ((24761/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_491).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_492 : ((13774329/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 492, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 492, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 491, cos687o2c k) + cos687o2c 492 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 491) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_491
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 492 - ((85061/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_492).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_493 : ((3691609/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 493, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 493, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 492, cos687o2c k) + cos687o2c 493 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 492) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_492
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 493 - ((992207/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_493).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_494 : ((780381/50000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 494, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 494, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 493, cos687o2c k) + cos687o2c 494 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 493) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_493
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 494 - ((210321/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_494).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_495 : ((49712/3125 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 495, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 495, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 494, cos687o2c k) + cos687o2c 495 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 494) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_494
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 495 - ((1877/6250 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_495).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_496 : ((3105839/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 496, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 496, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 495, cos687o2c k) + cos687o2c 496 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 495) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_495
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 496 - ((-75709/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_496).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_497 : ((7323553/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 497, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 497, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 496, cos687o2c k) + cos687o2c 497 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 496) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_496
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 497 - ((-881989/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_497).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_498 : ((13666881/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 498, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 498, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 497, cos687o2c k) + cos687o2c 498 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 497) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_497
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 498 - ((-7841/8000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_498).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_499 : ((13036411/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 499, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 499, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 498, cos687o2c k) + cos687o2c 499 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 498) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_498
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 499 - ((-63037/100000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_499).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum687o2_500 : ((815123/62500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 500, cos687o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 500, cos687o2c k)
      = (∑ k ∈ Finset.Icc 11 499, cos687o2c k) + cos687o2c 500 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 499) (by norm_num) cos687o2c
    simpa using h
  have hprev := psum687o2_499
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos687o2c 500 - ((5657/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos687o2_br_500).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

set_option maxHeartbeats 6400000 in
set_option maxRecDepth 16384 in
theorem psum687o2_floor : ∀ j : ℕ, 11 ≤ j → j ≤ 500 →
    ((0 : ℚ) : ℝ) ≤ ∑ k ∈ Finset.Icc 11 j, cos687o2c k := by
  intro j hj1 hj2
  interval_cases j
  · exact le_trans (by norm_num) psum687o2_11
  · exact le_trans (by norm_num) psum687o2_12
  · exact le_trans (by norm_num) psum687o2_13
  · exact le_trans (by norm_num) psum687o2_14
  · exact le_trans (by norm_num) psum687o2_15
  · exact le_trans (by norm_num) psum687o2_16
  · exact le_trans (by norm_num) psum687o2_17
  · exact le_trans (by norm_num) psum687o2_18
  · exact le_trans (by norm_num) psum687o2_19
  · exact le_trans (by norm_num) psum687o2_20
  · exact le_trans (by norm_num) psum687o2_21
  · exact le_trans (by norm_num) psum687o2_22
  · exact le_trans (by norm_num) psum687o2_23
  · exact le_trans (by norm_num) psum687o2_24
  · exact le_trans (by norm_num) psum687o2_25
  · exact le_trans (by norm_num) psum687o2_26
  · exact le_trans (by norm_num) psum687o2_27
  · exact le_trans (by norm_num) psum687o2_28
  · exact le_trans (by norm_num) psum687o2_29
  · exact le_trans (by norm_num) psum687o2_30
  · exact le_trans (by norm_num) psum687o2_31
  · exact le_trans (by norm_num) psum687o2_32
  · exact le_trans (by norm_num) psum687o2_33
  · exact le_trans (by norm_num) psum687o2_34
  · exact le_trans (by norm_num) psum687o2_35
  · exact le_trans (by norm_num) psum687o2_36
  · exact le_trans (by norm_num) psum687o2_37
  · exact le_trans (by norm_num) psum687o2_38
  · exact le_trans (by norm_num) psum687o2_39
  · exact le_trans (by norm_num) psum687o2_40
  · exact le_trans (by norm_num) psum687o2_41
  · exact le_trans (by norm_num) psum687o2_42
  · exact le_trans (by norm_num) psum687o2_43
  · exact le_trans (by norm_num) psum687o2_44
  · exact le_trans (by norm_num) psum687o2_45
  · exact le_trans (by norm_num) psum687o2_46
  · exact le_trans (by norm_num) psum687o2_47
  · exact le_trans (by norm_num) psum687o2_48
  · exact le_trans (by norm_num) psum687o2_49
  · exact le_trans (by norm_num) psum687o2_50
  · exact le_trans (by norm_num) psum687o2_51
  · exact le_trans (by norm_num) psum687o2_52
  · exact le_trans (by norm_num) psum687o2_53
  · exact le_trans (by norm_num) psum687o2_54
  · exact le_trans (by norm_num) psum687o2_55
  · exact le_trans (by norm_num) psum687o2_56
  · exact le_trans (by norm_num) psum687o2_57
  · exact le_trans (by norm_num) psum687o2_58
  · exact le_trans (by norm_num) psum687o2_59
  · exact le_trans (by norm_num) psum687o2_60
  · exact le_trans (by norm_num) psum687o2_61
  · exact le_trans (by norm_num) psum687o2_62
  · exact le_trans (by norm_num) psum687o2_63
  · exact le_trans (by norm_num) psum687o2_64
  · exact le_trans (by norm_num) psum687o2_65
  · exact le_trans (by norm_num) psum687o2_66
  · exact le_trans (by norm_num) psum687o2_67
  · exact le_trans (by norm_num) psum687o2_68
  · exact le_trans (by norm_num) psum687o2_69
  · exact le_trans (by norm_num) psum687o2_70
  · exact le_trans (by norm_num) psum687o2_71
  · exact le_trans (by norm_num) psum687o2_72
  · exact le_trans (by norm_num) psum687o2_73
  · exact le_trans (by norm_num) psum687o2_74
  · exact le_trans (by norm_num) psum687o2_75
  · exact le_trans (by norm_num) psum687o2_76
  · exact le_trans (by norm_num) psum687o2_77
  · exact le_trans (by norm_num) psum687o2_78
  · exact le_trans (by norm_num) psum687o2_79
  · exact le_trans (by norm_num) psum687o2_80
  · exact le_trans (by norm_num) psum687o2_81
  · exact le_trans (by norm_num) psum687o2_82
  · exact le_trans (by norm_num) psum687o2_83
  · exact le_trans (by norm_num) psum687o2_84
  · exact le_trans (by norm_num) psum687o2_85
  · exact le_trans (by norm_num) psum687o2_86
  · exact le_trans (by norm_num) psum687o2_87
  · exact le_trans (by norm_num) psum687o2_88
  · exact le_trans (by norm_num) psum687o2_89
  · exact le_trans (by norm_num) psum687o2_90
  · exact le_trans (by norm_num) psum687o2_91
  · exact le_trans (by norm_num) psum687o2_92
  · exact le_trans (by norm_num) psum687o2_93
  · exact le_trans (by norm_num) psum687o2_94
  · exact le_trans (by norm_num) psum687o2_95
  · exact le_trans (by norm_num) psum687o2_96
  · exact le_trans (by norm_num) psum687o2_97
  · exact le_trans (by norm_num) psum687o2_98
  · exact le_trans (by norm_num) psum687o2_99
  · exact le_trans (by norm_num) psum687o2_100
  · exact le_trans (by norm_num) psum687o2_101
  · exact le_trans (by norm_num) psum687o2_102
  · exact le_trans (by norm_num) psum687o2_103
  · exact le_trans (by norm_num) psum687o2_104
  · exact le_trans (by norm_num) psum687o2_105
  · exact le_trans (by norm_num) psum687o2_106
  · exact le_trans (by norm_num) psum687o2_107
  · exact le_trans (by norm_num) psum687o2_108
  · exact le_trans (by norm_num) psum687o2_109
  · exact le_trans (by norm_num) psum687o2_110
  · exact le_trans (by norm_num) psum687o2_111
  · exact le_trans (by norm_num) psum687o2_112
  · exact le_trans (by norm_num) psum687o2_113
  · exact le_trans (by norm_num) psum687o2_114
  · exact le_trans (by norm_num) psum687o2_115
  · exact le_trans (by norm_num) psum687o2_116
  · exact le_trans (by norm_num) psum687o2_117
  · exact le_trans (by norm_num) psum687o2_118
  · exact le_trans (by norm_num) psum687o2_119
  · exact le_trans (by norm_num) psum687o2_120
  · exact le_trans (by norm_num) psum687o2_121
  · exact le_trans (by norm_num) psum687o2_122
  · exact le_trans (by norm_num) psum687o2_123
  · exact le_trans (by norm_num) psum687o2_124
  · exact le_trans (by norm_num) psum687o2_125
  · exact le_trans (by norm_num) psum687o2_126
  · exact le_trans (by norm_num) psum687o2_127
  · exact le_trans (by norm_num) psum687o2_128
  · exact le_trans (by norm_num) psum687o2_129
  · exact le_trans (by norm_num) psum687o2_130
  · exact le_trans (by norm_num) psum687o2_131
  · exact le_trans (by norm_num) psum687o2_132
  · exact le_trans (by norm_num) psum687o2_133
  · exact le_trans (by norm_num) psum687o2_134
  · exact le_trans (by norm_num) psum687o2_135
  · exact le_trans (by norm_num) psum687o2_136
  · exact le_trans (by norm_num) psum687o2_137
  · exact le_trans (by norm_num) psum687o2_138
  · exact le_trans (by norm_num) psum687o2_139
  · exact le_trans (by norm_num) psum687o2_140
  · exact le_trans (by norm_num) psum687o2_141
  · exact le_trans (by norm_num) psum687o2_142
  · exact le_trans (by norm_num) psum687o2_143
  · exact le_trans (by norm_num) psum687o2_144
  · exact le_trans (by norm_num) psum687o2_145
  · exact le_trans (by norm_num) psum687o2_146
  · exact le_trans (by norm_num) psum687o2_147
  · exact le_trans (by norm_num) psum687o2_148
  · exact le_trans (by norm_num) psum687o2_149
  · exact le_trans (by norm_num) psum687o2_150
  · exact le_trans (by norm_num) psum687o2_151
  · exact le_trans (by norm_num) psum687o2_152
  · exact le_trans (by norm_num) psum687o2_153
  · exact le_trans (by norm_num) psum687o2_154
  · exact le_trans (by norm_num) psum687o2_155
  · exact le_trans (by norm_num) psum687o2_156
  · exact le_trans (by norm_num) psum687o2_157
  · exact le_trans (by norm_num) psum687o2_158
  · exact le_trans (by norm_num) psum687o2_159
  · exact le_trans (by norm_num) psum687o2_160
  · exact le_trans (by norm_num) psum687o2_161
  · exact le_trans (by norm_num) psum687o2_162
  · exact le_trans (by norm_num) psum687o2_163
  · exact le_trans (by norm_num) psum687o2_164
  · exact le_trans (by norm_num) psum687o2_165
  · exact le_trans (by norm_num) psum687o2_166
  · exact le_trans (by norm_num) psum687o2_167
  · exact le_trans (by norm_num) psum687o2_168
  · exact le_trans (by norm_num) psum687o2_169
  · exact le_trans (by norm_num) psum687o2_170
  · exact le_trans (by norm_num) psum687o2_171
  · exact le_trans (by norm_num) psum687o2_172
  · exact le_trans (by norm_num) psum687o2_173
  · exact le_trans (by norm_num) psum687o2_174
  · exact le_trans (by norm_num) psum687o2_175
  · exact le_trans (by norm_num) psum687o2_176
  · exact le_trans (by norm_num) psum687o2_177
  · exact le_trans (by norm_num) psum687o2_178
  · exact le_trans (by norm_num) psum687o2_179
  · exact le_trans (by norm_num) psum687o2_180
  · exact le_trans (by norm_num) psum687o2_181
  · exact le_trans (by norm_num) psum687o2_182
  · exact le_trans (by norm_num) psum687o2_183
  · exact le_trans (by norm_num) psum687o2_184
  · exact le_trans (by norm_num) psum687o2_185
  · exact le_trans (by norm_num) psum687o2_186
  · exact le_trans (by norm_num) psum687o2_187
  · exact le_trans (by norm_num) psum687o2_188
  · exact le_trans (by norm_num) psum687o2_189
  · exact le_trans (by norm_num) psum687o2_190
  · exact le_trans (by norm_num) psum687o2_191
  · exact le_trans (by norm_num) psum687o2_192
  · exact le_trans (by norm_num) psum687o2_193
  · exact le_trans (by norm_num) psum687o2_194
  · exact le_trans (by norm_num) psum687o2_195
  · exact le_trans (by norm_num) psum687o2_196
  · exact le_trans (by norm_num) psum687o2_197
  · exact le_trans (by norm_num) psum687o2_198
  · exact le_trans (by norm_num) psum687o2_199
  · exact le_trans (by norm_num) psum687o2_200
  · exact le_trans (by norm_num) psum687o2_201
  · exact le_trans (by norm_num) psum687o2_202
  · exact le_trans (by norm_num) psum687o2_203
  · exact le_trans (by norm_num) psum687o2_204
  · exact le_trans (by norm_num) psum687o2_205
  · exact le_trans (by norm_num) psum687o2_206
  · exact le_trans (by norm_num) psum687o2_207
  · exact le_trans (by norm_num) psum687o2_208
  · exact le_trans (by norm_num) psum687o2_209
  · exact le_trans (by norm_num) psum687o2_210
  · exact le_trans (by norm_num) psum687o2_211
  · exact le_trans (by norm_num) psum687o2_212
  · exact le_trans (by norm_num) psum687o2_213
  · exact le_trans (by norm_num) psum687o2_214
  · exact le_trans (by norm_num) psum687o2_215
  · exact le_trans (by norm_num) psum687o2_216
  · exact le_trans (by norm_num) psum687o2_217
  · exact le_trans (by norm_num) psum687o2_218
  · exact le_trans (by norm_num) psum687o2_219
  · exact le_trans (by norm_num) psum687o2_220
  · exact le_trans (by norm_num) psum687o2_221
  · exact le_trans (by norm_num) psum687o2_222
  · exact le_trans (by norm_num) psum687o2_223
  · exact le_trans (by norm_num) psum687o2_224
  · exact le_trans (by norm_num) psum687o2_225
  · exact le_trans (by norm_num) psum687o2_226
  · exact le_trans (by norm_num) psum687o2_227
  · exact le_trans (by norm_num) psum687o2_228
  · exact le_trans (by norm_num) psum687o2_229
  · exact le_trans (by norm_num) psum687o2_230
  · exact le_trans (by norm_num) psum687o2_231
  · exact le_trans (by norm_num) psum687o2_232
  · exact le_trans (by norm_num) psum687o2_233
  · exact le_trans (by norm_num) psum687o2_234
  · exact le_trans (by norm_num) psum687o2_235
  · exact le_trans (by norm_num) psum687o2_236
  · exact le_trans (by norm_num) psum687o2_237
  · exact le_trans (by norm_num) psum687o2_238
  · exact le_trans (by norm_num) psum687o2_239
  · exact le_trans (by norm_num) psum687o2_240
  · exact le_trans (by norm_num) psum687o2_241
  · exact le_trans (by norm_num) psum687o2_242
  · exact le_trans (by norm_num) psum687o2_243
  · exact le_trans (by norm_num) psum687o2_244
  · exact le_trans (by norm_num) psum687o2_245
  · exact le_trans (by norm_num) psum687o2_246
  · exact le_trans (by norm_num) psum687o2_247
  · exact le_trans (by norm_num) psum687o2_248
  · exact le_trans (by norm_num) psum687o2_249
  · exact le_trans (by norm_num) psum687o2_250
  · exact le_trans (by norm_num) psum687o2_251
  · exact le_trans (by norm_num) psum687o2_252
  · exact le_trans (by norm_num) psum687o2_253
  · exact le_trans (by norm_num) psum687o2_254
  · exact le_trans (by norm_num) psum687o2_255
  · exact le_trans (by norm_num) psum687o2_256
  · exact le_trans (by norm_num) psum687o2_257
  · exact le_trans (by norm_num) psum687o2_258
  · exact le_trans (by norm_num) psum687o2_259
  · exact le_trans (by norm_num) psum687o2_260
  · exact le_trans (by norm_num) psum687o2_261
  · exact le_trans (by norm_num) psum687o2_262
  · exact le_trans (by norm_num) psum687o2_263
  · exact le_trans (by norm_num) psum687o2_264
  · exact le_trans (by norm_num) psum687o2_265
  · exact le_trans (by norm_num) psum687o2_266
  · exact le_trans (by norm_num) psum687o2_267
  · exact le_trans (by norm_num) psum687o2_268
  · exact le_trans (by norm_num) psum687o2_269
  · exact le_trans (by norm_num) psum687o2_270
  · exact le_trans (by norm_num) psum687o2_271
  · exact le_trans (by norm_num) psum687o2_272
  · exact le_trans (by norm_num) psum687o2_273
  · exact le_trans (by norm_num) psum687o2_274
  · exact le_trans (by norm_num) psum687o2_275
  · exact le_trans (by norm_num) psum687o2_276
  · exact le_trans (by norm_num) psum687o2_277
  · exact le_trans (by norm_num) psum687o2_278
  · exact le_trans (by norm_num) psum687o2_279
  · exact le_trans (by norm_num) psum687o2_280
  · exact le_trans (by norm_num) psum687o2_281
  · exact le_trans (by norm_num) psum687o2_282
  · exact le_trans (by norm_num) psum687o2_283
  · exact le_trans (by norm_num) psum687o2_284
  · exact le_trans (by norm_num) psum687o2_285
  · exact le_trans (by norm_num) psum687o2_286
  · exact le_trans (by norm_num) psum687o2_287
  · exact le_trans (by norm_num) psum687o2_288
  · exact le_trans (by norm_num) psum687o2_289
  · exact le_trans (by norm_num) psum687o2_290
  · exact le_trans (by norm_num) psum687o2_291
  · exact le_trans (by norm_num) psum687o2_292
  · exact le_trans (by norm_num) psum687o2_293
  · exact le_trans (by norm_num) psum687o2_294
  · exact le_trans (by norm_num) psum687o2_295
  · exact le_trans (by norm_num) psum687o2_296
  · exact le_trans (by norm_num) psum687o2_297
  · exact le_trans (by norm_num) psum687o2_298
  · exact le_trans (by norm_num) psum687o2_299
  · exact le_trans (by norm_num) psum687o2_300
  · exact le_trans (by norm_num) psum687o2_301
  · exact le_trans (by norm_num) psum687o2_302
  · exact le_trans (by norm_num) psum687o2_303
  · exact le_trans (by norm_num) psum687o2_304
  · exact le_trans (by norm_num) psum687o2_305
  · exact le_trans (by norm_num) psum687o2_306
  · exact le_trans (by norm_num) psum687o2_307
  · exact le_trans (by norm_num) psum687o2_308
  · exact le_trans (by norm_num) psum687o2_309
  · exact le_trans (by norm_num) psum687o2_310
  · exact le_trans (by norm_num) psum687o2_311
  · exact le_trans (by norm_num) psum687o2_312
  · exact le_trans (by norm_num) psum687o2_313
  · exact le_trans (by norm_num) psum687o2_314
  · exact le_trans (by norm_num) psum687o2_315
  · exact le_trans (by norm_num) psum687o2_316
  · exact le_trans (by norm_num) psum687o2_317
  · exact le_trans (by norm_num) psum687o2_318
  · exact le_trans (by norm_num) psum687o2_319
  · exact le_trans (by norm_num) psum687o2_320
  · exact le_trans (by norm_num) psum687o2_321
  · exact le_trans (by norm_num) psum687o2_322
  · exact le_trans (by norm_num) psum687o2_323
  · exact le_trans (by norm_num) psum687o2_324
  · exact le_trans (by norm_num) psum687o2_325
  · exact le_trans (by norm_num) psum687o2_326
  · exact le_trans (by norm_num) psum687o2_327
  · exact le_trans (by norm_num) psum687o2_328
  · exact le_trans (by norm_num) psum687o2_329
  · exact le_trans (by norm_num) psum687o2_330
  · exact le_trans (by norm_num) psum687o2_331
  · exact le_trans (by norm_num) psum687o2_332
  · exact le_trans (by norm_num) psum687o2_333
  · exact le_trans (by norm_num) psum687o2_334
  · exact le_trans (by norm_num) psum687o2_335
  · exact le_trans (by norm_num) psum687o2_336
  · exact le_trans (by norm_num) psum687o2_337
  · exact le_trans (by norm_num) psum687o2_338
  · exact le_trans (by norm_num) psum687o2_339
  · exact le_trans (by norm_num) psum687o2_340
  · exact le_trans (by norm_num) psum687o2_341
  · exact le_trans (by norm_num) psum687o2_342
  · exact le_trans (by norm_num) psum687o2_343
  · exact le_trans (by norm_num) psum687o2_344
  · exact le_trans (by norm_num) psum687o2_345
  · exact le_trans (by norm_num) psum687o2_346
  · exact le_trans (by norm_num) psum687o2_347
  · exact le_trans (by norm_num) psum687o2_348
  · exact le_trans (by norm_num) psum687o2_349
  · exact le_trans (by norm_num) psum687o2_350
  · exact le_trans (by norm_num) psum687o2_351
  · exact le_trans (by norm_num) psum687o2_352
  · exact le_trans (by norm_num) psum687o2_353
  · exact le_trans (by norm_num) psum687o2_354
  · exact le_trans (by norm_num) psum687o2_355
  · exact le_trans (by norm_num) psum687o2_356
  · exact le_trans (by norm_num) psum687o2_357
  · exact le_trans (by norm_num) psum687o2_358
  · exact le_trans (by norm_num) psum687o2_359
  · exact le_trans (by norm_num) psum687o2_360
  · exact le_trans (by norm_num) psum687o2_361
  · exact le_trans (by norm_num) psum687o2_362
  · exact le_trans (by norm_num) psum687o2_363
  · exact le_trans (by norm_num) psum687o2_364
  · exact le_trans (by norm_num) psum687o2_365
  · exact le_trans (by norm_num) psum687o2_366
  · exact le_trans (by norm_num) psum687o2_367
  · exact le_trans (by norm_num) psum687o2_368
  · exact le_trans (by norm_num) psum687o2_369
  · exact le_trans (by norm_num) psum687o2_370
  · exact le_trans (by norm_num) psum687o2_371
  · exact le_trans (by norm_num) psum687o2_372
  · exact le_trans (by norm_num) psum687o2_373
  · exact le_trans (by norm_num) psum687o2_374
  · exact le_trans (by norm_num) psum687o2_375
  · exact le_trans (by norm_num) psum687o2_376
  · exact le_trans (by norm_num) psum687o2_377
  · exact le_trans (by norm_num) psum687o2_378
  · exact le_trans (by norm_num) psum687o2_379
  · exact le_trans (by norm_num) psum687o2_380
  · exact le_trans (by norm_num) psum687o2_381
  · exact le_trans (by norm_num) psum687o2_382
  · exact le_trans (by norm_num) psum687o2_383
  · exact le_trans (by norm_num) psum687o2_384
  · exact le_trans (by norm_num) psum687o2_385
  · exact le_trans (by norm_num) psum687o2_386
  · exact le_trans (by norm_num) psum687o2_387
  · exact le_trans (by norm_num) psum687o2_388
  · exact le_trans (by norm_num) psum687o2_389
  · exact le_trans (by norm_num) psum687o2_390
  · exact le_trans (by norm_num) psum687o2_391
  · exact le_trans (by norm_num) psum687o2_392
  · exact le_trans (by norm_num) psum687o2_393
  · exact le_trans (by norm_num) psum687o2_394
  · exact le_trans (by norm_num) psum687o2_395
  · exact le_trans (by norm_num) psum687o2_396
  · exact le_trans (by norm_num) psum687o2_397
  · exact le_trans (by norm_num) psum687o2_398
  · exact le_trans (by norm_num) psum687o2_399
  · exact le_trans (by norm_num) psum687o2_400
  · exact le_trans (by norm_num) psum687o2_401
  · exact le_trans (by norm_num) psum687o2_402
  · exact le_trans (by norm_num) psum687o2_403
  · exact le_trans (by norm_num) psum687o2_404
  · exact le_trans (by norm_num) psum687o2_405
  · exact le_trans (by norm_num) psum687o2_406
  · exact le_trans (by norm_num) psum687o2_407
  · exact le_trans (by norm_num) psum687o2_408
  · exact le_trans (by norm_num) psum687o2_409
  · exact le_trans (by norm_num) psum687o2_410
  · exact le_trans (by norm_num) psum687o2_411
  · exact le_trans (by norm_num) psum687o2_412
  · exact le_trans (by norm_num) psum687o2_413
  · exact le_trans (by norm_num) psum687o2_414
  · exact le_trans (by norm_num) psum687o2_415
  · exact le_trans (by norm_num) psum687o2_416
  · exact le_trans (by norm_num) psum687o2_417
  · exact le_trans (by norm_num) psum687o2_418
  · exact le_trans (by norm_num) psum687o2_419
  · exact le_trans (by norm_num) psum687o2_420
  · exact le_trans (by norm_num) psum687o2_421
  · exact le_trans (by norm_num) psum687o2_422
  · exact le_trans (by norm_num) psum687o2_423
  · exact le_trans (by norm_num) psum687o2_424
  · exact le_trans (by norm_num) psum687o2_425
  · exact le_trans (by norm_num) psum687o2_426
  · exact le_trans (by norm_num) psum687o2_427
  · exact le_trans (by norm_num) psum687o2_428
  · exact le_trans (by norm_num) psum687o2_429
  · exact le_trans (by norm_num) psum687o2_430
  · exact le_trans (by norm_num) psum687o2_431
  · exact le_trans (by norm_num) psum687o2_432
  · exact le_trans (by norm_num) psum687o2_433
  · exact le_trans (by norm_num) psum687o2_434
  · exact le_trans (by norm_num) psum687o2_435
  · exact le_trans (by norm_num) psum687o2_436
  · exact le_trans (by norm_num) psum687o2_437
  · exact le_trans (by norm_num) psum687o2_438
  · exact le_trans (by norm_num) psum687o2_439
  · exact le_trans (by norm_num) psum687o2_440
  · exact le_trans (by norm_num) psum687o2_441
  · exact le_trans (by norm_num) psum687o2_442
  · exact le_trans (by norm_num) psum687o2_443
  · exact le_trans (by norm_num) psum687o2_444
  · exact le_trans (by norm_num) psum687o2_445
  · exact le_trans (by norm_num) psum687o2_446
  · exact le_trans (by norm_num) psum687o2_447
  · exact le_trans (by norm_num) psum687o2_448
  · exact le_trans (by norm_num) psum687o2_449
  · exact le_trans (by norm_num) psum687o2_450
  · exact le_trans (by norm_num) psum687o2_451
  · exact le_trans (by norm_num) psum687o2_452
  · exact le_trans (by norm_num) psum687o2_453
  · exact le_trans (by norm_num) psum687o2_454
  · exact le_trans (by norm_num) psum687o2_455
  · exact le_trans (by norm_num) psum687o2_456
  · exact le_trans (by norm_num) psum687o2_457
  · exact le_trans (by norm_num) psum687o2_458
  · exact le_trans (by norm_num) psum687o2_459
  · exact le_trans (by norm_num) psum687o2_460
  · exact le_trans (by norm_num) psum687o2_461
  · exact le_trans (by norm_num) psum687o2_462
  · exact le_trans (by norm_num) psum687o2_463
  · exact le_trans (by norm_num) psum687o2_464
  · exact le_trans (by norm_num) psum687o2_465
  · exact le_trans (by norm_num) psum687o2_466
  · exact le_trans (by norm_num) psum687o2_467
  · exact le_trans (by norm_num) psum687o2_468
  · exact le_trans (by norm_num) psum687o2_469
  · exact le_trans (by norm_num) psum687o2_470
  · exact le_trans (by norm_num) psum687o2_471
  · exact le_trans (by norm_num) psum687o2_472
  · exact le_trans (by norm_num) psum687o2_473
  · exact le_trans (by norm_num) psum687o2_474
  · exact le_trans (by norm_num) psum687o2_475
  · exact le_trans (by norm_num) psum687o2_476
  · exact le_trans (by norm_num) psum687o2_477
  · exact le_trans (by norm_num) psum687o2_478
  · exact le_trans (by norm_num) psum687o2_479
  · exact le_trans (by norm_num) psum687o2_480
  · exact le_trans (by norm_num) psum687o2_481
  · exact le_trans (by norm_num) psum687o2_482
  · exact le_trans (by norm_num) psum687o2_483
  · exact le_trans (by norm_num) psum687o2_484
  · exact le_trans (by norm_num) psum687o2_485
  · exact le_trans (by norm_num) psum687o2_486
  · exact le_trans (by norm_num) psum687o2_487
  · exact le_trans (by norm_num) psum687o2_488
  · exact le_trans (by norm_num) psum687o2_489
  · exact le_trans (by norm_num) psum687o2_490
  · exact le_trans (by norm_num) psum687o2_491
  · exact le_trans (by norm_num) psum687o2_492
  · exact le_trans (by norm_num) psum687o2_493
  · exact le_trans (by norm_num) psum687o2_494
  · exact le_trans (by norm_num) psum687o2_495
  · exact le_trans (by norm_num) psum687o2_496
  · exact le_trans (by norm_num) psum687o2_497
  · exact le_trans (by norm_num) psum687o2_498
  · exact le_trans (by norm_num) psum687o2_499
  · exact le_trans (by norm_num) psum687o2_500

end CriticalLinePhasor.DVP

section AxiomAudit
#print axioms CriticalLinePhasor.DVP.psum687o2_floor
#print axioms CriticalLinePhasor.DVP.psum687o2_500
end AxiomAudit
