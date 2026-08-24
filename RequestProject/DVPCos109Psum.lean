import RequestProject.DVPCos109Table

/-!
# The cosine partial-sum floor, `t = 109`
-/

open Finset

noncomputable section

namespace CriticalLinePhasor.DVP

/-- The cosine sequence of the `t = 109` segment certificate. -/
def cos109c (n : ℕ) : ℝ := Real.cos (((109:ℕ):ℝ) * Real.log n)

theorem psum109_11 : ((-16297/20000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 11, cos109c k := by
  rw [Finset.Icc_self, Finset.sum_singleton]
  have h : -((1/25000 : ℚ) : ℝ) ≤ cos109c 11 - ((-81481/100000 : ℚ) : ℝ) :=
    (abs_le.mp cos109_br_11).1
  push_cast at h ⊢
  linarith

theorem psum109_12 : ((-35971/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 12, cos109c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 12, cos109c k)
      = (∑ k ∈ Finset.Icc 11 11, cos109c k) + cos109c 12 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 11) (by norm_num) cos109c
    simpa using h
  have hprev := psum109_11
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos109c 12 - ((778919/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos109_br_12).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum109_13 : ((-1035763/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 13, cos109c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 13, cos109c k)
      = (∑ k ∈ Finset.Icc 11 12, cos109c k) + cos109c 13 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 12) (by norm_num) cos109c
    simpa using h
  have hprev := psum109_12
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos109c 13 - ((-124969/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos109_br_13).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum109_14 : ((-835643/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 14, cos109c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 14, cos109c k)
      = (∑ k ∈ Finset.Icc 11 13, cos109c k) + cos109c 14 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 13) (by norm_num) cos109c
    simpa using h
  have hprev := psum109_13
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos109c 14 - ((1251/6250 : ℚ) : ℝ) :=
    (abs_le.mp cos109_br_14).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum109_15 : ((77793/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 15, cos109c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 15, cos109c k)
      = (∑ k ∈ Finset.Icc 11 14, cos109c k) + cos109c 15 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 14) (by norm_num) cos109c
    simpa using h
  have hprev := psum109_14
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos109c 15 - ((991269/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos109_br_15).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum109_16 : ((193969/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 16, cos109c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 16, cos109c k)
      = (∑ k ∈ Finset.Icc 11 15, cos109c k) + cos109c 16 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 15) (by norm_num) cos109c
    simpa using h
  have hprev := psum109_15
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos109c 16 - ((814299/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos109_br_16).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum109_17 : ((1556217/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 17, cos109c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 17, cos109c k)
      = (∑ k ∈ Finset.Icc 11 16, cos109c k) + cos109c 17 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 16) (by norm_num) cos109c
    simpa using h
  have hprev := psum109_16
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos109c 17 - ((146603/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos109_br_17).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum109_18 : ((2184613/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 18, cos109c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 18, cos109c k)
      = (∑ k ∈ Finset.Icc 11 17, cos109c k) + cos109c 18 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 17) (by norm_num) cos109c
    simpa using h
  have hprev := psum109_17
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos109c 18 - ((157109/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos109_br_18).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum109_19 : ((765371/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 19, cos109c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 19, cos109c k)
      = (∑ k ∈ Finset.Icc 11 18, cos109c k) + cos109c 19 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 18) (by norm_num) cos109c
    simpa using h
  have hprev := psum109_18
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos109c 19 - ((876911/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos109_br_19).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum109_20 : ((4043293/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 20, cos109c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 20, cos109c k)
      = (∑ k ∈ Finset.Icc 11 19, cos109c k) + cos109c 20 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 19) (by norm_num) cos109c
    simpa using h
  have hprev := psum109_19
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos109c 20 - ((981849/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos109_br_20).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum109_21 : ((444637/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 21, cos109c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 21, cos109c k)
      = (∑ k ∈ Finset.Icc 11 20, cos109c k) + cos109c 21 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 20) (by norm_num) cos109c
    simpa using h
  have hprev := psum109_20
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos109c 21 - ((403117/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos109_br_21).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum109_22 : ((186533/50000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 22, cos109c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 22, cos109c k)
      = (∑ k ∈ Finset.Icc 11 21, cos109c k) + cos109c 22 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 21) (by norm_num) cos109c
    simpa using h
  have hprev := psum109_21
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos109c 22 - ((-71567/100000 : ℚ) : ℝ) :=
    (abs_le.mp cos109_br_22).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum109_23 : ((2943537/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 23, cos109c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 23, cos109c k)
      = (∑ k ∈ Finset.Icc 11 22, cos109c k) + cos109c 23 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 22) (by norm_num) cos109c
    simpa using h
  have hprev := psum109_22
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos109c 23 - ((-787083/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos109_br_23).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum109_24 : ((904099/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 24, cos109c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 24, cos109c k)
      = (∑ k ∈ Finset.Icc 11 23, cos109c k) + cos109c 24 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 23) (by norm_num) cos109c
    simpa using h
  have hprev := psum109_23
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos109c 24 - ((672899/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos109_br_24).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum109_25 : ((415589/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 25, cos109c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 25, cos109c k)
      = (∑ k ∈ Finset.Icc 11 24, cos109c k) + cos109c 25 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 24) (by norm_num) cos109c
    simpa using h
  have hprev := psum109_24
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos109c 25 - ((269767/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos109_br_25).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum109_26 : ((1582311/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 26, cos109c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 26, cos109c k)
      = (∑ k ∈ Finset.Icc 11 25, cos109c k) + cos109c 26 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 25) (by norm_num) cos109c
    simpa using h
  have hprev := psum109_25
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos109c 26 - ((-247807/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos109_br_26).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum109_27 : ((451753/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 27, cos109c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 27, cos109c k)
      = (∑ k ∈ Finset.Icc 11 26, cos109c k) + cos109c 27 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 26) (by norm_num) cos109c
    simpa using h
  have hprev := psum109_26
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos109c 27 - ((224721/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos109_br_27).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum109_28 : ((396283/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 28, cos109c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 28, cos109c k)
      = (∑ k ∈ Finset.Icc 11 27, cos109c k) + cos109c 28 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 27) (by norm_num) cos109c
    simpa using h
  have hprev := psum109_27
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos109c 28 - ((174423/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos109_br_28).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum109_29 : ((3100537/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 29, cos109c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 29, cos109c k)
      = (∑ k ∈ Finset.Icc 11 28, cos109c k) + cos109c 29 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 28) (by norm_num) cos109c
    simpa using h
  have hprev := psum109_28
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos109c 29 - ((-862253/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos109_br_29).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum109_30 : ((2050121/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 30, cos109c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 30, cos109c k)
      = (∑ k ∈ Finset.Icc 11 29, cos109c k) + cos109c 30 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 29) (by norm_num) cos109c
    simpa using h
  have hprev := psum109_29
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos109c 30 - ((199949/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos109_br_30).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum109_31 : ((400247/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 31, cos109c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 31, cos109c k)
      = (∑ k ∈ Finset.Icc 11 30, cos109c k) + cos109c 31 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 30) (by norm_num) cos109c
    simpa using h
  have hprev := psum109_30
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos109c 31 - ((-449113/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos109_br_31).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum109_32 : ((391699/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 32, cos109c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 32, cos109c k)
      = (∑ k ∈ Finset.Icc 11 31, cos109c k) + cos109c 32 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 31) (by norm_num) cos109c
    simpa using h
  have hprev := psum109_31
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos109c 32 - ((357527/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos109_br_32).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum109_33 : ((420679/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 33, cos109c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 33, cos109c k)
      = (∑ k ∈ Finset.Icc 11 32, cos109c k) + cos109c 33 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 32) (by norm_num) cos109c
    simpa using h
  have hprev := psum109_32
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos109c 33 - ((-275759/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos109_br_33).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum109_34 : ((763977/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 34, cos109c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 34, cos109c k)
      = (∑ k ∈ Finset.Icc 11 33, cos109c k) + cos109c 34 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 33) (by norm_num) cos109c
    simpa using h
  have hprev := psum109_33
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos109c 34 - ((454493/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos109_br_34).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum109_35 : ((1690751/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 35, cos109c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 35, cos109c k)
      = (∑ k ∈ Finset.Icc 11 34, cos109c k) + cos109c 35 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 34) (by norm_num) cos109c
    simpa using h
  have hprev := psum109_34
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos109c 35 - ((-438343/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos109_br_35).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum109_36 : ((1941217/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 36, cos109c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 36, cos109c k)
      = (∑ k ∈ Finset.Icc 11 35, cos109c k) + cos109c 36 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 35) (by norm_num) cos109c
    simpa using h
  have hprev := psum109_35
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos109c 36 - ((125243/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos109_br_36).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum109_37 : ((3253737/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 37, cos109c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 37, cos109c k)
      = (∑ k ∈ Finset.Icc 11 36, cos109c k) + cos109c 37 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 36) (by norm_num) cos109c
    simpa using h
  have hprev := psum109_36
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos109c 37 - ((-628657/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos109_br_37).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum109_38 : ((4046003/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 38, cos109c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 38, cos109c k)
      = (∑ k ∈ Finset.Icc 11 37, cos109c k) + cos109c 38 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 37) (by norm_num) cos109c
    simpa using h
  have hprev := psum109_37
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos109c 38 - ((396153/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos109_br_38).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum109_39 : ((310521/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 39, cos109c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 39, cos109c k)
      = (∑ k ∈ Finset.Icc 11 38, cos109c k) + cos109c 39 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 38) (by norm_num) cos109c
    simpa using h
  have hprev := psum109_38
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos109c 39 - ((-940753/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos109_br_39).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum109_40 : ((2052261/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 40, cos109c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 40, cos109c k)
      = (∑ k ∈ Finset.Icc 11 39, cos109c k) + cos109c 40 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 39) (by norm_num) cos109c
    simpa using h
  have hprev := psum109_39
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos109c 40 - ((124919/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos109_br_40).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum109_41 : ((3220319/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 41, cos109c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 41, cos109c k)
      = (∑ k ∈ Finset.Icc 11 40, cos109c k) + cos109c 41 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 40) (by norm_num) cos109c
    simpa using h
  have hprev := psum109_40
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos109c 41 - ((-884163/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos109_br_41).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum109_42 : ((939923/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 42, cos109c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 42, cos109c k)
      = (∑ k ∈ Finset.Icc 11 41, cos109c k) + cos109c 42 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 41) (by norm_num) cos109c
    simpa using h
  have hprev := psum109_41
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos109c 42 - ((539413/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos109_br_42).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum109_43 : ((3766681/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 43, cos109c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 43, cos109c k)
      = (∑ k ∈ Finset.Icc 11 42, cos109c k) + cos109c 43 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 42) (by norm_num) cos109c
    simpa using h
  have hprev := psum109_42
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos109c 43 - ((7029/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos109_br_43).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum109_44 : ((3167231/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 44, cos109c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 44, cos109c k)
      = (∑ k ∈ Finset.Icc 11 43, cos109c k) + cos109c 44 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 43) (by norm_num) cos109c
    simpa using h
  have hprev := psum109_43
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos109c 44 - ((-59941/100000 : ℚ) : ℝ) :=
    (abs_le.mp cos109_br_44).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum109_45 : ((4139477/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 45, cos109c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 45, cos109c k)
      = (∑ k ∈ Finset.Icc 11 44, cos109c k) + cos109c 45 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 44) (by norm_num) cos109c
    simpa using h
  have hprev := psum109_44
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos109c 45 - ((486143/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos109_br_45).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum109_46 : ((3266649/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 46, cos109c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 46, cos109c k)
      = (∑ k ∈ Finset.Icc 11 45, cos109c k) + cos109c 46 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 45) (by norm_num) cos109c
    simpa using h
  have hprev := psum109_45
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos109c 46 - ((-218197/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos109_br_46).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum109_47 : ((3527041/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 47, cos109c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 47, cos109c k)
      = (∑ k ∈ Finset.Icc 11 46, cos109c k) + cos109c 47 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 46) (by norm_num) cos109c
    simpa using h
  have hprev := psum109_46
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos109c 47 - ((16277/62500 : ℚ) : ℝ) :=
    (abs_le.mp cos109_br_47).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum109_48 : ((509723/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 48, cos109c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 48, cos109c k)
      = (∑ k ∈ Finset.Icc 11 47, cos109c k) + cos109c 48 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 47) (by norm_num) cos109c
    simpa using h
  have hprev := psum109_47
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos109c 48 - ((550783/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos109_br_48).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum109_49 : ((3082103/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 49, cos109c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 49, cos109c k)
      = (∑ k ∈ Finset.Icc 11 48, cos109c k) + cos109c 49 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 48) (by norm_num) cos109c
    simpa using h
  have hprev := psum109_48
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos109c 49 - ((-995641/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos109_br_49).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum109_50 : ((234061/62500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 50, cos109c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 50, cos109c k)
      = (∑ k ∈ Finset.Icc 11 49, cos109c k) + cos109c 50 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 49) (by norm_num) cos109c
    simpa using h
  have hprev := psum109_49
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos109c 50 - ((662913/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos109_br_50).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum109_51 : ((4000473/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 51, cos109c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 51, cos109c k)
      = (∑ k ∈ Finset.Icc 11 50, cos109c k) + cos109c 51 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 50) (by norm_num) cos109c
    simpa using h
  have hprev := psum109_50
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos109c 51 - ((255537/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos109_br_51).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum109_52 : ((3041441/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 52, cos109c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 52, cos109c k)
      = (∑ k ∈ Finset.Icc 11 51, cos109c k) + cos109c 52 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 51) (by norm_num) cos109c
    simpa using h
  have hprev := psum109_51
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos109c 52 - ((-59937/62500 : ℚ) : ℝ) :=
    (abs_le.mp cos109_br_52).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum109_53 : ((1876871/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 53, cos109c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 53, cos109c k)
      = (∑ k ∈ Finset.Icc 11 52, cos109c k) + cos109c 53 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 52) (by norm_num) cos109c
    simpa using h
  have hprev := psum109_52
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos109c 53 - ((712341/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos109_br_53).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum109_54 : ((4060019/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 54, cos109c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 54, cos109c k)
      = (∑ k ∈ Finset.Icc 11 53, cos109c k) + cos109c 54 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 53) (by norm_num) cos109c
    simpa using h
  have hprev := psum109_53
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos109c 54 - ((306317/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos109_br_54).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum109_55 : ((1533463/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 55, cos109c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 55, cos109c k)
      = (∑ k ∈ Finset.Icc 11 54, cos109c k) + cos109c 55 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 54) (by norm_num) cos109c
    simpa using h
  have hprev := psum109_54
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos109c 55 - ((-993053/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos109_br_55).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum109_56 : ((1778037/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 56, cos109c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 56, cos109c k)
      = (∑ k ∈ Finset.Icc 11 55, cos109c k) + cos109c 56 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 55) (by norm_num) cos109c
    simpa using h
  have hprev := psum109_55
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos109c 56 - ((122297/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos109_br_56).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum109_57 : ((2100577/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 57, cos109c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 57, cos109c k)
      = (∑ k ∈ Finset.Icc 11 56, cos109c k) + cos109c 57 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 56) (by norm_num) cos109c
    simpa using h
  have hprev := psum109_56
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos109c 57 - ((2016/3125 : ℚ) : ℝ) :=
    (abs_le.mp cos109_br_57).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum109_58 : ((130843/40000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 58, cos109c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 58, cos109c k)
      = (∑ k ∈ Finset.Icc 11 57, cos109c k) + cos109c 58 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 57) (by norm_num) cos109c
    simpa using h
  have hprev := psum109_57
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos109c 58 - ((-930039/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos109_br_58).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum109_59 : ((1593677/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 59, cos109c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 59, cos109c k)
      = (∑ k ∈ Finset.Icc 11 58, cos109c k) + cos109c 59 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 58) (by norm_num) cos109c
    simpa using h
  have hprev := psum109_58
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos109c 59 - ((-83681/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos109_br_59).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum109_60 : ((208581/50000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 60, cos109c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 60, cos109c k)
      = (∑ k ∈ Finset.Icc 11 59, cos109c k) + cos109c 60 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 59) (by norm_num) cos109c
    simpa using h
  have hprev := psum109_59
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos109c 60 - ((492153/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos109_br_60).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum109_61 : ((943633/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 61, cos109c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 61, cos109c k)
      = (∑ k ∈ Finset.Icc 11 60, cos109c k) + cos109c 61 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 60) (by norm_num) cos109c
    simpa using h
  have hprev := psum109_60
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos109c 61 - ((-49631/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos109_br_61).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum109_62 : ((1477393/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 62, cos109c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 62, cos109c k)
      = (∑ k ∈ Finset.Icc 11 61, cos109c k) + cos109c 62 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 61) (by norm_num) cos109c
    simpa using h
  have hprev := psum109_61
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos109c 62 - ((-409853/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos109_br_62).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum109_63 : ((1830127/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 63, cos109c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 63, cos109c k)
      = (∑ k ∈ Finset.Icc 11 62, cos109c k) + cos109c 63 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 62) (by norm_num) cos109c
    simpa using h
  have hprev := psum109_62
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos109c 63 - ((176377/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos109_br_63).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum109_64 : ((4258919/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 64, cos109c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 64, cos109c k)
      = (∑ k ∈ Finset.Icc 11 63, cos109c k) + cos109c 64 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 63) (by norm_num) cos109c
    simpa using h
  have hprev := psum109_63
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos109c 64 - ((119741/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos109_br_64).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum109_65 : ((106013/31250 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 65, cos109c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 65, cos109c k)
      = (∑ k ∈ Finset.Icc 11 64, cos109c k) + cos109c 65 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 64) (by norm_num) cos109c
    simpa using h
  have hprev := psum109_64
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos109c 65 - ((-866463/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos109_br_65).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum109_66 : ((2976083/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 66, cos109c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 66, cos109c k)
      = (∑ k ∈ Finset.Icc 11 65, cos109c k) + cos109c 66 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 65) (by norm_num) cos109c
    simpa using h
  have hprev := psum109_65
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos109c 66 - ((-416293/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos109_br_66).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum109_67 : ((488947/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 67, cos109c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 67, cos109c k)
      = (∑ k ∈ Finset.Icc 11 66, cos109c k) + cos109c 67 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 66) (by norm_num) cos109c
    simpa using h
  have hprev := psum109_66
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos109c 67 - ((935533/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos109_br_67).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum109_68 : ((2111619/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 68, cos109c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 68, cos109c k)
      = (∑ k ∈ Finset.Icc 11 67, cos109c k) + cos109c 68 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 67) (by norm_num) cos109c
    simpa using h
  have hprev := psum109_67
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos109c 68 - ((155851/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos109_br_68).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum109_69 : ((816709/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 69, cos109c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 69, cos109c k)
      = (∑ k ∈ Finset.Icc 11 68, cos109c k) + cos109c 69 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 68) (by norm_num) cos109c
    simpa using h
  have hprev := psum109_68
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos109c 69 - ((-478181/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos109_br_69).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum109_70 : ((2972293/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 70, cos109c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 70, cos109c k)
      = (∑ k ∈ Finset.Icc 11 69, cos109c k) + cos109c 70 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 69) (by norm_num) cos109c
    simpa using h
  have hprev := psum109_69
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos109c 70 - ((-294503/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos109_br_70).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum109_71 : ((980087/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 71, cos109c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 71, cos109c k)
      = (∑ k ∈ Finset.Icc 11 70, cos109c k) + cos109c 71 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 70) (by norm_num) cos109c
    simpa using h
  have hprev := psum109_70
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos109c 71 - ((189619/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos109_br_71).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum109_72 : ((535229/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 72, cos109c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 72, cos109c k)
      = (∑ k ∈ Finset.Icc 11 71, cos109c k) + cos109c 72 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 71) (by norm_num) cos109c
    simpa using h
  have hprev := psum109_71
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos109c 72 - ((90381/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos109_br_72).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum109_73 : ((3375863/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 73, cos109c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 73, cos109c k)
      = (∑ k ∈ Finset.Icc 11 72, cos109c k) + cos109c 73 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 72) (by norm_num) cos109c
    simpa using h
  have hprev := psum109_72
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos109c 73 - ((-905929/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos109_br_73).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum109_74 : ((718651/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 74, cos109c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 74, cos109c k)
      = (∑ k ∈ Finset.Icc 11 73, cos109c k) + cos109c 74 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 73) (by norm_num) cos109c
    simpa using h
  have hprev := psum109_73
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos109c 74 - ((-501219/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos109_br_74).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum109_75 : ((3681001/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 75, cos109c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 75, cos109c k)
      = (∑ k ∈ Finset.Icc 11 74, cos109c k) + cos109c 75 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 74) (by norm_num) cos109c
    simpa using h
  have hprev := psum109_74
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos109c 75 - ((806437/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos109_br_75).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum109_76 : ((4369709/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 76, cos109c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 76, cos109c k)
      = (∑ k ∈ Finset.Icc 11 75, cos109c k) + cos109c 76 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 75) (by norm_num) cos109c
    simpa using h
  have hprev := psum109_75
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos109c 76 - ((172187/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos109_br_76).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum109_77 : ((1876267/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 77, cos109c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 77, cos109c k)
      = (∑ k ∈ Finset.Icc 11 76, cos109c k) + cos109c 77 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 76) (by norm_num) cos109c
    simpa using h
  have hprev := psum109_76
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos109c 77 - ((-123427/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos109_br_77).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum109_78 : ((2875281/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 78, cos109c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 78, cos109c k)
      = (∑ k ∈ Finset.Icc 11 77, cos109c k) + cos109c 78 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 77) (by norm_num) cos109c
    simpa using h
  have hprev := psum109_77
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos109c 78 - ((-877213/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos109_br_78).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum109_79 : ((3188411/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 79, cos109c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 79, cos109c k)
      = (∑ k ∈ Finset.Icc 11 78, cos109c k) + cos109c 79 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 78) (by norm_num) cos109c
    simpa using h
  have hprev := psum109_78
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos109c 79 - ((31317/100000 : ℚ) : ℝ) :=
    (abs_le.mp cos109_br_79).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum109_80 : ((104533/25000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 80, cos109c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 80, cos109c k)
      = (∑ k ∈ Finset.Icc 11 79, cos109c k) + cos109c 80 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 79) (by norm_num) cos109c
    simpa using h
  have hprev := psum109_79
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos109c 80 - ((992949/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos109_br_80).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum109_81 : ((2139523/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 81, cos109c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 81, cos109c k)
      = (∑ k ∈ Finset.Icc 11 80, cos109c k) + cos109c 81 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 80) (by norm_num) cos109c
    simpa using h
  have hprev := psum109_80
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos109c 81 - ((48883/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos109_br_81).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum109_82 : ((3333379/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 82, cos109c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 82, cos109c k)
      = (∑ k ∈ Finset.Icc 11 81, cos109c k) + cos109c 82 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 81) (by norm_num) cos109c
    simpa using h
  have hprev := psum109_81
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos109c 82 - ((-945627/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos109_br_82).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum109_83 : ((2784607/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 83, cos109c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 83, cos109c k)
      = (∑ k ∈ Finset.Icc 11 82, cos109c k) + cos109c 83 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 82) (by norm_num) cos109c
    simpa using h
  have hprev := psum109_82
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos109c 83 - ((-137183/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos109_br_83).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum109_84 : ((861843/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 84, cos109c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 84, cos109c k)
      = (∑ k ∈ Finset.Icc 11 83, cos109c k) + cos109c 84 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 83) (by norm_num) cos109c
    simpa using h
  have hprev := psum109_83
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos109c 84 - ((132561/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos109_br_84).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum109_85 : ((2175247/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 85, cos109c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 85, cos109c k)
      = (∑ k ∈ Finset.Icc 11 84, cos109c k) + cos109c 85 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 84) (by norm_num) cos109c
    simpa using h
  have hprev := psum109_84
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos109c 85 - ((451581/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos109_br_85).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum109_86 : ((4203201/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 86, cos109c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 86, cos109c k)
      = (∑ k ∈ Finset.Icc 11 85, cos109c k) + cos109c 86 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 85) (by norm_num) cos109c
    simpa using h
  have hprev := psum109_85
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos109c 86 - ((-147253/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos109_br_86).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum109_87 : ((804099/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 87, cos109c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 87, cos109c k)
      = (∑ k ∈ Finset.Icc 11 86, cos109c k) + cos109c 87 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 86) (by norm_num) cos109c
    simpa using h
  have hprev := psum109_86
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos109c 87 - ((-197353/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos109_br_87).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum109_88 : ((343443/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 88, cos109c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 88, cos109c k)
      = (∑ k ∈ Finset.Icc 11 87, cos109c k) + cos109c 88 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 87) (by norm_num) cos109c
    simpa using h
  have hprev := psum109_87
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos109c 88 - ((-117203/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos109_br_88).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum109_89 : ((856131/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 89, cos109c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 89, cos109c k)
      = (∑ k ∈ Finset.Icc 11 88, cos109c k) + cos109c 89 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 88) (by norm_num) cos109c
    simpa using h
  have hprev := psum109_88
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos109c 89 - ((33851/50000 : ℚ) : ℝ) :=
    (abs_le.mp cos109_br_89).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum109_90 : ((4349089/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 90, cos109c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 90, cos109c k)
      = (∑ k ∈ Finset.Icc 11 89, cos109c k) + cos109c 90 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 89) (by norm_num) cos109c
    simpa using h
  have hprev := psum109_89
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos109c 90 - ((184921/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos109_br_90).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum109_91 : ((540577/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 91, cos109c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 91, cos109c k)
      = (∑ k ∈ Finset.Icc 11 90, cos109c k) + cos109c 91 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 90) (by norm_num) cos109c
    simpa using h
  have hprev := psum109_90
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos109c 91 - ((-24433/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos109_br_91).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum109_92 : ((3386961/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 92, cos109c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 92, cos109c k)
      = (∑ k ∈ Finset.Icc 11 91, cos109c k) + cos109c 92 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 91) (by norm_num) cos109c
    simpa using h
  have hprev := psum109_91
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos109c 92 - ((-187523/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos109_br_92).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum109_93 : ((541423/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 93, cos109c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 93, cos109c k)
      = (∑ k ∈ Finset.Icc 11 92, cos109c k) + cos109c 93 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 92) (by norm_num) cos109c
    simpa using h
  have hprev := psum109_92
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos109c 93 - ((-339903/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos109_br_93).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum109_94 : ((389159/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 94, cos109c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 94, cos109c k)
      = (∑ k ∈ Finset.Icc 11 93, cos109c k) + cos109c 94 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 93) (by norm_num) cos109c
    simpa using h
  have hprev := psum109_93
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos109c 94 - ((406197/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos109_br_94).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum109_95 : ((257077/62500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 95, cos109c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 95, cos109c k)
      = (∑ k ∈ Finset.Icc 11 94, cos109c k) + cos109c 95 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 94) (by norm_num) cos109c
    simpa using h
  have hprev := psum109_94
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos109c 95 - ((1/1 : ℚ) : ℝ) :=
    (abs_le.mp cos109_br_95).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum109_96 : ((4528683/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 96, cos109c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 96, cos109c k)
      = (∑ k ∈ Finset.Icc 11 95, cos109c k) + cos109c 96 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 95) (by norm_num) cos109c
    simpa using h
  have hprev := psum109_95
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos109c 96 - ((415491/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos109_br_96).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum109_97 : ((1941807/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 97, cos109c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 97, cos109c k)
      = (∑ k ∈ Finset.Icc 11 96, cos109c k) + cos109c 97 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 96) (by norm_num) cos109c
    simpa using h
  have hprev := psum109_96
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos109c 97 - ((-645029/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos109_br_97).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum109_98 : ((2914223/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 98, cos109c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 98, cos109c k)
      = (∑ k ∈ Finset.Icc 11 97, cos109c k) + cos109c 98 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 97) (by norm_num) cos109c
    simpa using h
  have hprev := psum109_97
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos109c 98 - ((-969351/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos109_br_98).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum109_99 : ((2699893/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 99, cos109c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 99, cos109c k)
      = (∑ k ∈ Finset.Icc 11 98, cos109c k) + cos109c 99 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 98) (by norm_num) cos109c
    simpa using h
  have hprev := psum109_98
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos109c 99 - ((-21429/100000 : ℚ) : ℝ) :=
    (abs_le.mp cos109_br_99).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum109_100 : ((3470287/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 100, cos109c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 100, cos109c k)
      = (∑ k ∈ Finset.Icc 11 99, cos109c k) + cos109c 100 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 99) (by norm_num) cos109c
    simpa using h
  have hprev := psum109_99
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos109c 100 - ((385217/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos109_br_100).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

/-- **The Abel floor at `t = 109`.** -/
theorem psum109_floor : ∀ j : ℕ, 11 ≤ j → j ≤ 100 →
    ((-1035763/1000000 : ℚ) : ℝ) ≤ ∑ k ∈ Finset.Icc 11 j, cos109c k := by
  intro j hj1 hj2
  interval_cases j
  · exact le_trans (by norm_num) psum109_11
  · exact le_trans (by norm_num) psum109_12
  · exact le_trans (by norm_num) psum109_13
  · exact le_trans (by norm_num) psum109_14
  · exact le_trans (by norm_num) psum109_15
  · exact le_trans (by norm_num) psum109_16
  · exact le_trans (by norm_num) psum109_17
  · exact le_trans (by norm_num) psum109_18
  · exact le_trans (by norm_num) psum109_19
  · exact le_trans (by norm_num) psum109_20
  · exact le_trans (by norm_num) psum109_21
  · exact le_trans (by norm_num) psum109_22
  · exact le_trans (by norm_num) psum109_23
  · exact le_trans (by norm_num) psum109_24
  · exact le_trans (by norm_num) psum109_25
  · exact le_trans (by norm_num) psum109_26
  · exact le_trans (by norm_num) psum109_27
  · exact le_trans (by norm_num) psum109_28
  · exact le_trans (by norm_num) psum109_29
  · exact le_trans (by norm_num) psum109_30
  · exact le_trans (by norm_num) psum109_31
  · exact le_trans (by norm_num) psum109_32
  · exact le_trans (by norm_num) psum109_33
  · exact le_trans (by norm_num) psum109_34
  · exact le_trans (by norm_num) psum109_35
  · exact le_trans (by norm_num) psum109_36
  · exact le_trans (by norm_num) psum109_37
  · exact le_trans (by norm_num) psum109_38
  · exact le_trans (by norm_num) psum109_39
  · exact le_trans (by norm_num) psum109_40
  · exact le_trans (by norm_num) psum109_41
  · exact le_trans (by norm_num) psum109_42
  · exact le_trans (by norm_num) psum109_43
  · exact le_trans (by norm_num) psum109_44
  · exact le_trans (by norm_num) psum109_45
  · exact le_trans (by norm_num) psum109_46
  · exact le_trans (by norm_num) psum109_47
  · exact le_trans (by norm_num) psum109_48
  · exact le_trans (by norm_num) psum109_49
  · exact le_trans (by norm_num) psum109_50
  · exact le_trans (by norm_num) psum109_51
  · exact le_trans (by norm_num) psum109_52
  · exact le_trans (by norm_num) psum109_53
  · exact le_trans (by norm_num) psum109_54
  · exact le_trans (by norm_num) psum109_55
  · exact le_trans (by norm_num) psum109_56
  · exact le_trans (by norm_num) psum109_57
  · exact le_trans (by norm_num) psum109_58
  · exact le_trans (by norm_num) psum109_59
  · exact le_trans (by norm_num) psum109_60
  · exact le_trans (by norm_num) psum109_61
  · exact le_trans (by norm_num) psum109_62
  · exact le_trans (by norm_num) psum109_63
  · exact le_trans (by norm_num) psum109_64
  · exact le_trans (by norm_num) psum109_65
  · exact le_trans (by norm_num) psum109_66
  · exact le_trans (by norm_num) psum109_67
  · exact le_trans (by norm_num) psum109_68
  · exact le_trans (by norm_num) psum109_69
  · exact le_trans (by norm_num) psum109_70
  · exact le_trans (by norm_num) psum109_71
  · exact le_trans (by norm_num) psum109_72
  · exact le_trans (by norm_num) psum109_73
  · exact le_trans (by norm_num) psum109_74
  · exact le_trans (by norm_num) psum109_75
  · exact le_trans (by norm_num) psum109_76
  · exact le_trans (by norm_num) psum109_77
  · exact le_trans (by norm_num) psum109_78
  · exact le_trans (by norm_num) psum109_79
  · exact le_trans (by norm_num) psum109_80
  · exact le_trans (by norm_num) psum109_81
  · exact le_trans (by norm_num) psum109_82
  · exact le_trans (by norm_num) psum109_83
  · exact le_trans (by norm_num) psum109_84
  · exact le_trans (by norm_num) psum109_85
  · exact le_trans (by norm_num) psum109_86
  · exact le_trans (by norm_num) psum109_87
  · exact le_trans (by norm_num) psum109_88
  · exact le_trans (by norm_num) psum109_89
  · exact le_trans (by norm_num) psum109_90
  · exact le_trans (by norm_num) psum109_91
  · exact le_trans (by norm_num) psum109_92
  · exact le_trans (by norm_num) psum109_93
  · exact le_trans (by norm_num) psum109_94
  · exact le_trans (by norm_num) psum109_95
  · exact le_trans (by norm_num) psum109_96
  · exact le_trans (by norm_num) psum109_97
  · exact le_trans (by norm_num) psum109_98
  · exact le_trans (by norm_num) psum109_99
  · exact le_trans (by norm_num) psum109_100

end CriticalLinePhasor.DVP

section AxiomAudit
#print axioms CriticalLinePhasor.DVP.psum109_floor
#print axioms CriticalLinePhasor.DVP.psum109_100
end AxiomAudit
