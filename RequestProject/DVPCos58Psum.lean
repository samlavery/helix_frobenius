import RequestProject.DVPCos58Table

/-!
# The cosine partial-sum floor, `t = 58`

The cumulative certified lower bounds `Vlow j ≤ ∑_{k∈[11,j]} cos(58·log k)`
(exact rational cumulative sums of the table values minus the accumulated
certificate widths), and the uniform Abel floor `Cmin` over `j ∈ [11,100]`.
This is the single number that replaces the ~235-station sweep.
-/

open Finset

noncomputable section

namespace CriticalLinePhasor.DVP

/-- The cosine sequence of the `t = 58` segment certificate. -/
def cos58c (n : ℕ) : ℝ := Real.cos (58 * Real.log n)

theorem psum58_11 : ((330779/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 11, cos58c k := by
  rw [Finset.Icc_self, Finset.sum_singleton]
  have h : -((1/25000 : ℚ) : ℝ) ≤ cos58c 11 - ((330799/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos58_br_11).1
  push_cast at h ⊢
  linarith

theorem psum58_12 : ((1586929/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 12, cos58c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 12, cos58c k)
      = (∑ k ∈ Finset.Icc 11 11, cos58c k) + cos58c 12 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 11) (by norm_num) cos58c
    simpa using h
  have hprev := psum58_11
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos58c 12 - ((925411/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos58_br_12).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum58_13 : ((572103/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 13, cos58c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 13, cos58c k)
      = (∑ k ∈ Finset.Icc 11 12, cos58c k) + cos58c 13 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 12) (by norm_num) cos58c
    simpa using h
  have hprev := psum58_12
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos58c 13 - ((-442683/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos58_br_13).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum58_14 : ((501417/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 14, cos58c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 14, cos58c k)
      = (∑ k ∈ Finset.Icc 11 13, cos58c k) + cos58c 14 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 13) (by norm_num) cos58c
    simpa using h
  have hprev := psum58_13
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos58c 14 - ((-642749/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos58_br_14).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum58_15 : ((93831/62500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 15, cos58c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 15, cos58c k)
      = (∑ k ∈ Finset.Icc 11 14, cos58c k) + cos58c 15 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 14) (by norm_num) cos58c
    simpa using h
  have hprev := psum58_14
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos58c 15 - ((999919/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos58_br_15).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum58_16 : ((133943/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 16, cos58c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 16, cos58c k)
      = (∑ k ∈ Finset.Icc 11 15, cos58c k) + cos58c 16 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 15) (by norm_num) cos58c
    simpa using h
  have hprev := psum58_15
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos58c 16 - ((-831541/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos58_br_16).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum58_17 : ((1240279/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 17, cos58c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 17, cos58c k)
      = (∑ k ∈ Finset.Icc 11 16, cos58c k) + cos58c 17 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 16) (by norm_num) cos58c
    simpa using h
  have hprev := psum58_16
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos58c 17 - ((142651/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos58_br_17).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum58_18 : ((410029/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 18, cos58c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 18, cos58c k)
      = (∑ k ∈ Finset.Icc 11 17, cos58c k) + cos58c 18 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 17) (by norm_num) cos58c
    simpa using h
  have hprev := psum58_17
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos58c 18 - ((-420181/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos58_br_18).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum58_19 : ((1245359/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 19, cos58c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 19, cos58c k)
      = (∑ k ∈ Finset.Icc 11 18, cos58c k) + cos58c 19 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 18) (by norm_num) cos58c
    simpa using h
  have hprev := psum58_18
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos58c 19 - ((425341/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos58_br_19).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum58_20 : ((3379/5000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 20, cos58c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 20, cos58c k)
      = (∑ k ∈ Finset.Icc 11 19, cos58c k) + cos58c 20 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 19) (by norm_num) cos58c
    simpa using h
  have hprev := psum58_19
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos58c 20 - ((-569519/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos58_br_20).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum58_21 : ((367489/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 21, cos58c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 21, cos58c k)
      = (∑ k ∈ Finset.Icc 11 20, cos58c k) + cos58c 21 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 20) (by norm_num) cos58c
    simpa using h
  have hprev := psum58_20
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos58c 21 - ((198549/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos58_br_21).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum58_22 : ((491819/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 22, cos58c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 22, cos58c k)
      = (∑ k ∈ Finset.Icc 11 21, cos58c k) + cos58c 22 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 21) (by norm_num) cos58c
    simpa using h
  have hprev := psum58_21
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos58c 22 - ((-978097/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos58_br_22).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum58_23 : ((1429873/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 23, cos58c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 23, cos58c k)
      = (∑ k ∈ Finset.Icc 11 22, cos58c k) + cos58c 23 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 22) (by norm_num) cos58c
    simpa using h
  have hprev := psum58_22
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos58c 23 - ((469047/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos58_br_23).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum58_24 : ((114039/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 24, cos58c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 24, cos58c k)
      = (∑ k ∈ Finset.Icc 11 23, cos58c k) + cos58c 24 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 23) (by norm_num) cos58c
    simpa using h
  have hprev := psum58_23
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos58c 24 - ((-517521/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos58_br_24).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum58_25 : ((85541/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 25, cos58c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 25, cos58c k)
      = (∑ k ∈ Finset.Icc 11 24, cos58c k) + cos58c 25 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 24) (by norm_num) cos58c
    simpa using h
  have hprev := psum58_24
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos58c 25 - ((-28493/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos58_br_25).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum58_26 : ((78701/50000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 26, cos58c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 26, cos58c k)
      = (∑ k ∈ Finset.Icc 11 25, cos58c k) + cos58c 26 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 25) (by norm_num) cos58c
    simpa using h
  have hprev := psum58_25
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos58c 26 - ((222433/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos58_br_26).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum58_27 : ((343173/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 27, cos58c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 27, cos58c k)
      = (∑ k ∈ Finset.Icc 11 26, cos58c k) + cos58c 27 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 26) (by norm_num) cos58c
    simpa using h
  have hprev := psum58_26
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos58c 27 - ((-443817/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos58_br_27).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum58_28 : ((746183/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 28, cos58c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 28, cos58c k)
      = (∑ k ∈ Finset.Icc 11 27, cos58c k) + cos58c 28 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 27) (by norm_num) cos58c
    simpa using h
  have hprev := psum58_27
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos58c 28 - ((59877/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos58_br_28).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum58_29 : ((1611761/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 29, cos58c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 29, cos58c k)
      = (∑ k ∈ Finset.Icc 11 28, cos58c k) + cos58c 29 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 28) (by norm_num) cos58c
    simpa using h
  have hprev := psum58_28
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos58c 29 - ((432809/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos58_br_29).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum58_30 : ((51011/62500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 30, cos58c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 30, cos58c k)
      = (∑ k ∈ Finset.Icc 11 29, cos58c k) + cos58c 30 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 29) (by norm_num) cos58c
    simpa using h
  have hprev := psum58_29
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos58c 30 - ((-159109/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos58_br_30).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum58_31 : ((501687/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 31, cos58c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 31, cos58c k)
      = (∑ k ∈ Finset.Icc 11 30, cos58c k) + cos58c 31 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 30) (by norm_num) cos58c
    simpa using h
  have hprev := psum58_30
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos58c 31 - ((-314449/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos58_br_31).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum58_32 : ((300087/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 32, cos58c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 32, cos58c k)
      = (∑ k ∈ Finset.Icc 11 31, cos58c k) + cos58c 32 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 31) (by norm_num) cos58c
    simpa using h
  have hprev := psum58_31
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos58c 32 - ((249697/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos58_br_32).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum58_33 : ((1336427/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 33, cos58c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 33, cos58c k)
      = (∑ k ∈ Finset.Icc 11 32, cos58c k) + cos58c 33 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 32) (by norm_num) cos58c
    simpa using h
  have hprev := psum58_32
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos58c 33 - ((-2562/15625 : ℚ) : ℝ) :=
    (abs_le.mp cos58_br_33).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum58_34 : ((19443/50000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 34, cos58c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 34, cos58c k)
      = (∑ k ∈ Finset.Icc 11 33, cos58c k) + cos58c 34 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 33) (by norm_num) cos58c
    simpa using h
  have hprev := psum58_33
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos58c 34 - ((-947527/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos58_br_34).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum58_35 : ((405509/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 35, cos58c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 35, cos58c k)
      = (∑ k ∈ Finset.Icc 11 34, cos58c k) + cos58c 35 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 34) (by norm_num) cos58c
    simpa using h
  have hprev := psum58_34
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos58c 35 - ((211099/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos58_br_35).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum58_36 : ((211131/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 36, cos58c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 36, cos58c k)
      = (∑ k ∈ Finset.Icc 11 35, cos58c k) + cos58c 36 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 35) (by norm_num) cos58c
    simpa using h
  have hprev := psum58_35
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos58c 36 - ((87807/100000 : ℚ) : ℝ) :=
    (abs_le.mp cos58_br_36).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum58_37 : ((1194449/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 37, cos58c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 37, cos58c k)
      = (∑ k ∈ Finset.Icc 11 36, cos58c k) + cos58c 37 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 36) (by norm_num) cos58c
    simpa using h
  have hprev := psum58_36
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos58c 37 - ((-494559/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos58_br_37).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum58_38 : ((313629/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 38, cos58c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 38, cos58c k)
      = (∑ k ∈ Finset.Icc 11 37, cos58c k) + cos58c 38 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 37) (by norm_num) cos58c
    simpa using h
  have hprev := psum58_37
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos58c 38 - ((-44039/50000 : ℚ) : ℝ) :=
    (abs_le.mp cos58_br_38).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum58_39 : ((145923/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 39, cos58c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 39, cos58c k)
      = (∑ k ∈ Finset.Icc 11 38, cos58c k) + cos58c 39 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 38) (by norm_num) cos58c
    simpa using h
  have hprev := psum58_38
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos58c 39 - ((208013/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos58_br_39).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum58_40 : ((1676679/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 40, cos58c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 40, cos58c k)
      = (∑ k ∈ Finset.Icc 11 39, cos58c k) + cos58c 40 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 39) (by norm_num) cos58c
    simpa using h
  have hprev := psum58_39
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos58c 40 - ((29597/31250 : ℚ) : ℝ) :=
    (abs_le.mp cos58_br_40).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum58_41 : ((1489663/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 41, cos58c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 41, cos58c k)
      = (∑ k ∈ Finset.Icc 11 40, cos58c k) + cos58c 41 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 40) (by norm_num) cos58c
    simpa using h
  have hprev := psum58_40
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos58c 41 - ((-5843/31250 : ℚ) : ℝ) :=
    (abs_le.mp cos58_br_41).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum58_42 : ((97947/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 42, cos58c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 42, cos58c k)
      = (∑ k ∈ Finset.Icc 11 41, cos58c k) + cos58c 42 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 41) (by norm_num) cos58c
    simpa using h
  have hprev := psum58_41
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos58c 42 - ((-62493/62500 : ℚ) : ℝ) :=
    (abs_le.mp cos58_br_42).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum58_43 : ((299773/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 43, cos58c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 43, cos58c k)
      = (∑ k ∈ Finset.Icc 11 42, cos58c k) + cos58c 43 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 42) (by norm_num) cos58c
    simpa using h
  have hprev := psum58_42
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos58c 43 - ((-94961/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos58_br_43).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum58_44 : ((75583/62500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 44, cos58c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 44, cos58c k)
      = (∑ k ∈ Finset.Icc 11 43, cos58c k) + cos58c 44 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 43) (by norm_num) cos58c
    simpa using h
  have hprev := psum58_43
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos58c 44 - ((181919/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos58_br_44).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum58_45 : ((462583/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 45, cos58c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 45, cos58c k)
      = (∑ k ∈ Finset.Icc 11 44, cos58c k) + cos58c 45 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 44) (by norm_num) cos58c
    simpa using h
  have hprev := psum58_44
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos58c 45 - ((160261/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos58_br_45).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum58_46 : ((1303173/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 46, cos58c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 46, cos58c k)
      = (∑ k ∈ Finset.Icc 11 45, cos58c k) + cos58c 46 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 45) (by norm_num) cos58c
    simpa using h
  have hprev := psum58_45
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos58c 46 - ((-547119/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos58_br_46).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum58_47 : ((335591/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 47, cos58c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 47, cos58c k)
      = (∑ k ∈ Finset.Icc 11 46, cos58c k) + cos58c 47 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 46) (by norm_num) cos58c
    simpa using h
  have hprev := psum58_46
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos58c 47 - ((-483771/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos58_br_47).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum58_48 : ((120737/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 48, cos58c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 48, cos58c k)
      = (∑ k ∈ Finset.Icc 11 47, cos58c k) + cos58c 48 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 47) (by norm_num) cos58c
    simpa using h
  have hprev := psum58_47
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos58c 48 - ((-94077/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos58_br_48).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum58_49 : ((283353/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 49, cos58c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 49, cos58c k)
      = (∑ k ∈ Finset.Icc 11 48, cos58c k) + cos58c 49 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 48) (by norm_num) cos58c
    simpa using h
  have hprev := psum58_48
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos58c 49 - ((445989/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos58_br_49).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum58_50 : ((118531/62500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 50, cos58c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 50, cos58c k)
      = (∑ k ∈ Finset.Icc 11 49, cos58c k) + cos58c 50 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 49) (by norm_num) cos58c
    simpa using h
  have hprev := psum58_49
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos58c 50 - ((190781/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos58_br_50).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum58_51 : ((1619697/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 51, cos58c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 51, cos58c k)
      = (∑ k ∈ Finset.Icc 11 50, cos58c k) + cos58c 51 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 50) (by norm_num) cos58c
    simpa using h
  have hprev := psum58_50
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos58c 51 - ((-276759/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos58_br_51).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum58_52 : ((79137/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 52, cos58c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 52, cos58c k)
      = (∑ k ∈ Finset.Icc 11 51, cos58c k) + cos58c 52 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 51) (by norm_num) cos58c
    simpa using h
  have hprev := psum58_51
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos58c 52 - ((-986561/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos58_br_52).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum58_53 : ((43807/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 53, cos58c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 53, cos58c k)
      = (∑ k ∈ Finset.Icc 11 52, cos58c k) + cos58c 53 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 52) (by norm_num) cos58c
    simpa using h
  have hprev := psum58_52
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos58c 53 - ((-589249/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos58_br_53).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum58_54 : ((60293/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 54, cos58c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 54, cos58c k)
      = (∑ k ∈ Finset.Icc 11 53, cos58c k) + cos58c 54 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 53) (by norm_num) cos58c
    simpa using h
  have hprev := psum58_53
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos58c 54 - ((438577/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos58_br_54).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum58_55 : ((59237/40000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 55, cos58c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 55, cos58c k)
      = (∑ k ∈ Finset.Icc 11 54, cos58c k) + cos58c 55 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 54) (by norm_num) cos58c
    simpa using h
  have hprev := psum58_54
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos58c 55 - ((998621/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos58_br_55).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum58_56 : ((253431/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 56, cos58c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 56, cos58c k)
      = (∑ k ∈ Finset.Icc 11 55, cos58c k) + cos58c 56 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 55) (by norm_num) cos58c
    simpa using h
  have hprev := psum58_55
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos58c 56 - ((546563/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos58_br_56).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum58_57 : ((318791/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 57, cos58c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 57, cos58c k)
      = (∑ k ∈ Finset.Icc 11 56, cos58c k) + cos58c 57 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 56) (by norm_num) cos58c
    simpa using h
  have hprev := psum58_56
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos58c 57 - ((-433453/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos58_br_57).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum58_58 : ((300189/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 58, cos58c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 58, cos58c k)
      = (∑ k ∈ Finset.Icc 11 57, cos58c k) + cos58c 58 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 57) (by norm_num) cos58c
    simpa using h
  have hprev := psum58_57
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos58c 58 - ((-993537/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos58_br_58).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum58_59 : ((-38567/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 59, cos58c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 59, cos58c k)
      = (∑ k ∈ Finset.Icc 11 58, cos58c k) + cos58c 59 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 58) (by norm_num) cos58c
    simpa using h
  have hprev := psum58_58
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos58c 59 - ((-127781/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos58_br_59).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum58_60 : ((11971/50000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 60, cos58c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 60, cos58c k)
      = (∑ k ∈ Finset.Icc 11 59, cos58c k) + cos58c 60 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 59) (by norm_num) cos58c
    simpa using h
  have hprev := psum58_59
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos58c 60 - ((278027/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos58_br_60).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum58_61 : ((592653/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 61, cos58c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 61, cos58c k)
      = (∑ k ∈ Finset.Icc 11 60, cos58c k) + cos58c 61 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 60) (by norm_num) cos58c
    simpa using h
  have hprev := psum58_60
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos58c 61 - ((472963/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos58_br_61).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum58_62 : ((1001667/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 62, cos58c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 62, cos58c k)
      = (∑ k ∈ Finset.Icc 11 61, cos58c k) + cos58c 62 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 61) (by norm_num) cos58c
    simpa using h
  have hprev := psum58_61
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos58c 62 - ((204517/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos58_br_62).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum58_63 : ((2033313/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 63, cos58c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 63, cos58c k)
      = (∑ k ∈ Finset.Icc 11 62, cos58c k) + cos58c 63 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 62) (by norm_num) cos58c
    simpa using h
  have hprev := psum58_62
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos58c 63 - ((30019/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos58_br_63).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum58_64 : ((252077/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 64, cos58c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 64, cos58c k)
      = (∑ k ∈ Finset.Icc 11 63, cos58c k) + cos58c 64 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 63) (by norm_num) cos58c
    simpa using h
  have hprev := psum58_63
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos58c 64 - ((-96611/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos58_br_64).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum58_65 : ((282697/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 65, cos58c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 65, cos58c k)
      = (∑ k ∈ Finset.Icc 11 64, cos58c k) + cos58c 65 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 64) (by norm_num) cos58c
    simpa using h
  have hprev := psum58_64
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos58c 65 - ((-61103/62500 : ℚ) : ℝ) :=
    (abs_le.mp cos58_br_65).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum58_66 : ((-43327/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 66, cos58c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 66, cos58c k)
      = (∑ k ∈ Finset.Icc 11 65, cos58c k) + cos58c 66 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 65) (by norm_num) cos58c
    simpa using h
  have hprev := psum58_65
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos58c 66 - ((-91193/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos58_br_66).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum58_67 : ((214911/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 67, cos58c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 67, cos58c k)
      = (∑ k ∈ Finset.Icc 11 66, cos58c k) + cos58c 67 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 66) (by norm_num) cos58c
    simpa using h
  have hprev := psum58_66
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos58c 67 - ((388259/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos58_br_67).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum58_68 : ((1166353/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 68, cos58c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 68, cos58c k)
      = (∑ k ∈ Finset.Icc 11 67, cos58c k) + cos58c 68 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 67) (by norm_num) cos58c
    simpa using h
  have hprev := psum58_67
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos58c 68 - ((475741/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos58_br_68).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum58_69 : ((506779/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 69, cos58c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 69, cos58c k)
      = (∑ k ∈ Finset.Icc 11 68, cos58c k) + cos58c 69 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 68) (by norm_num) cos58c
    simpa using h
  have hprev := psum58_68
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos58c 69 - ((860803/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos58_br_69).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum58_70 : ((1113999/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 70, cos58c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 70, cos58c k)
      = (∑ k ∈ Finset.Icc 11 69, cos58c k) + cos58c 70 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 69) (by norm_num) cos58c
    simpa using h
  have hprev := psum58_69
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos58c 70 - ((100461/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos58_br_70).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum58_71 : ((164659/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 71, cos58c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 71, cos58c k)
      = (∑ k ∈ Finset.Icc 11 70, cos58c k) + cos58c 71 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 70) (by norm_num) cos58c
    simpa using h
  have hprev := psum58_70
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos58c 71 - ((-72671/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos58_br_71).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum58_72 : ((656221/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 72, cos58c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 72, cos58c k)
      = (∑ k ∈ Finset.Icc 11 71, cos58c k) + cos58c 72 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 71) (by norm_num) cos58c
    simpa using h
  have hprev := psum58_71
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos58c 72 - ((-990329/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos58_br_72).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum58_73 : ((-133303/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 73, cos58c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 73, cos58c k)
      = (∑ k ∈ Finset.Icc 11 72, cos58c k) + cos58c 73 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 72) (by norm_num) cos58c
    simpa using h
  have hprev := psum58_72
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos58c 73 - ((-197371/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos58_br_73).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum58_74 : ((-25389/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 74, cos58c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 74, cos58c k)
      = (∑ k ∈ Finset.Icc 11 73, cos58c k) + cos58c 74 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 73) (by norm_num) cos58c
    simpa using h
  have hprev := psum58_73
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos58c 74 - ((-120547/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos58_br_74).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum58_75 : ((89341/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 75, cos58c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 75, cos58c k)
      = (∑ k ∈ Finset.Icc 11 74, cos58c k) + cos58c 75 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 74) (by norm_num) cos58c
    simpa using h
  have hprev := psum58_74
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos58c 75 - ((305647/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos58_br_75).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum58_76 : ((1346847/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 76, cos58c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 76, cos58c k)
      = (∑ k ∈ Finset.Icc 11 75, cos58c k) + cos58c 76 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 75) (by norm_num) cos58c
    simpa using h
  have hprev := psum58_75
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos58c 76 - ((989523/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos58_br_76).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum58_77 : ((2164559/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 77, cos58c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 77, cos58c k)
      = (∑ k ∈ Finset.Icc 11 76, cos58c k) + cos58c 77 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 76) (by norm_num) cos58c
    simpa using h
  have hprev := psum58_76
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos58c 77 - ((102219/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos58_br_77).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum58_78 : ((474419/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 78, cos58c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 78, cos58c k)
      = (∑ k ∈ Finset.Icc 11 77, cos58c k) + cos58c 78 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 77) (by norm_num) cos58c
    simpa using h
  have hprev := psum58_77
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos58c 78 - ((25947/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos58_br_78).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum58_79 : ((1866723/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 79, cos58c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 79, cos58c k)
      = (∑ k ∈ Finset.Icc 11 78, cos58c k) + cos58c 79 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 78) (by norm_num) cos58c
    simpa using h
  have hprev := psum58_78
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos58c 79 - ((-126333/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos58_br_79).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum58_80 : ((228699/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 80, cos58c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 80, cos58c k)
      = (∑ k ∈ Finset.Icc 11 79, cos58c k) + cos58c 80 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 79) (by norm_num) cos58c
    simpa using h
  have hprev := psum58_79
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos58c 80 - ((-951887/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos58_br_80).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum58_81 : ((-549/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 81, cos58c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 81, cos58c k)
      = (∑ k ∈ Finset.Icc 11 80, cos58c k) + cos58c 81 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 80) (by norm_num) cos58c
    simpa using h
  have hprev := psum58_80
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos58c 81 - ((-917501/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos58_br_81).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum58_82 : ((-437827/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 82, cos58c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 82, cos58c k)
      = (∑ k ∈ Finset.Icc 11 81, cos58c k) + cos58c 82 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 81) (by norm_num) cos58c
    simpa using h
  have hprev := psum58_81
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos58c 82 - ((-217521/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos58_br_82).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum58_83 : ((-93801/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 83, cos58c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 83, cos58c k)
      = (∑ k ∈ Finset.Icc 11 82, cos58c k) + cos58c 83 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 82) (by norm_num) cos58c
    simpa using h
  have hprev := psum58_82
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos58c 83 - ((50053/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos58_br_83).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum58_84 : ((624359/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 84, cos58c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 84, cos58c k)
      = (∑ k ∈ Finset.Icc 11 83, cos58c k) + cos58c 84 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 83) (by norm_num) cos58c
    simpa using h
  have hprev := psum58_83
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos58c 84 - ((812001/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos58_br_84).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum58_85 : ((405581/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 85, cos58c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 85, cos58c k)
      = (∑ k ∈ Finset.Icc 11 84, cos58c k) + cos58c 85 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 84) (by norm_num) cos58c
    simpa using h
  have hprev := psum58_84
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos58c 85 - ((199601/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos58_br_85).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum58_86 : ((235971/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 86, cos58c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 86, cos58c k)
      = (∑ k ∈ Finset.Icc 11 85, cos58c k) + cos58c 86 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 85) (by norm_num) cos58c
    simpa using h
  have hprev := psum58_85
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos58c 86 - ((368713/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos58_br_86).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum58_87 : ((78679/31250 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 87, cos58c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 87, cos58c k)
      = (∑ k ∈ Finset.Icc 11 86, cos58c k) + cos58c 87 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 86) (by norm_num) cos58c
    simpa using h
  have hprev := psum58_86
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos58c 87 - ((79029/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos58_br_87).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum58_88 : ((254329/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 88, cos58c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 88, cos58c k)
      = (∑ k ∈ Finset.Icc 11 87, cos58c k) + cos58c 88 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 87) (by norm_num) cos58c
    simpa using h
  have hprev := psum58_87
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos58c 88 - ((-30191/62500 : ℚ) : ℝ) :=
    (abs_le.mp cos58_br_88).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum58_89 : ((1117983/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 89, cos58c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 89, cos58c k)
      = (∑ k ∈ Finset.Icc 11 88, cos58c k) + cos58c 89 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 88) (by norm_num) cos58c
    simpa using h
  have hprev := psum58_88
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos58c 89 - ((-916609/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos58_br_89).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum58_90 : ((72921/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 90, cos58c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 90, cos58c k)
      = (∑ k ∈ Finset.Icc 11 89, cos58c k) + cos58c 90 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 89) (by norm_num) cos58c
    simpa using h
  have hprev := psum58_89
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos58c 90 - ((-972101/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos58_br_90).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum58_91 : ((-9863/20000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 91, cos58c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 91, cos58c k)
      = (∑ k ∈ Finset.Icc 11 90, cos58c k) + cos58c 91 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 90) (by norm_num) cos58c
    simpa using h
  have hprev := psum58_90
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos58c 91 - ((-79869/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos58_br_91).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum58_92 : ((-110481/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 92, cos58c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 92, cos58c k)
      = (∑ k ∈ Finset.Icc 11 91, cos58c k) + cos58c 92 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 91) (by norm_num) cos58c
    simpa using h
  have hprev := psum58_91
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos58c 92 - ((-11843/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos58_br_92).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum58_93 : ((-367/25000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 93, cos58c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 93, cos58c k)
      = (∑ k ∈ Finset.Icc 11 92, cos58c k) + cos58c 93 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 92) (by norm_num) cos58c
    simpa using h
  have hprev := psum58_92
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos58c 93 - ((107553/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos58_br_93).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum58_94 : ((182589/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 94, cos58c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 94, cos58c k)
      = (∑ k ∈ Finset.Icc 11 93, cos58c k) + cos58c 94 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 93) (by norm_num) cos58c
    simpa using h
  have hprev := psum58_93
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos58c 94 - ((185533/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos58_br_94).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum58_95 : ((75453/40000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 95, cos58c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 95, cos58c k)
      = (∑ k ∈ Finset.Icc 11 94, cos58c k) + cos58c 95 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 94) (by norm_num) cos58c
    simpa using h
  have hprev := psum58_94
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos58c 95 - ((48671/50000 : ℚ) : ℝ) :=
    (abs_le.mp cos58_br_95).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum58_96 : ((2554929/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 96, cos58c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 96, cos58c k)
      = (∑ k ∈ Finset.Icc 11 95, cos58c k) + cos58c 96 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 95) (by norm_num) cos58c
    simpa using h
  have hprev := psum58_95
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos58c 96 - ((167161/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos58_br_96).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum58_97 : ((1342927/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 97, cos58c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 97, cos58c k)
      = (∑ k ∈ Finset.Icc 11 96, cos58c k) + cos58c 97 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 96) (by norm_num) cos58c
    simpa using h
  have hprev := psum58_96
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos58c 97 - ((26193/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos58_br_97).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum58_98 : ((1119351/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 98, cos58c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 98, cos58c k)
      = (∑ k ∈ Finset.Icc 11 97, cos58c k) + cos58c 98 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 97) (by norm_num) cos58c
    simpa using h
  have hprev := psum58_97
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos58c 98 - ((-55889/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos58_br_98).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum58_99 : ((1370061/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 99, cos58c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 99, cos58c k)
      = (∑ k ∈ Finset.Icc 11 98, cos58c k) + cos58c 99 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 98) (by norm_num) cos58c
    simpa using h
  have hprev := psum58_98
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos58c 99 - ((-868601/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos58_br_99).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum58_100 : ((3721/10000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 100, cos58c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 100, cos58c k)
      = (∑ k ∈ Finset.Icc 11 99, cos58c k) + cos58c 100 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 99) (by norm_num) cos58c
    simpa using h
  have hprev := psum58_99
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos58c 100 - ((-997921/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos58_br_100).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

/-- **The Abel floor**: `Cmin ≤ ∑_{k∈[11,j]} cos(58·log k)` for every
`j ∈ [11,100]`. -/
theorem psum58_floor : ∀ j : ℕ, 11 ≤ j → j ≤ 100 →
    ((-110481/200000 : ℚ) : ℝ) ≤ ∑ k ∈ Finset.Icc 11 j, cos58c k := by
  intro j hj1 hj2
  interval_cases j
  · exact le_trans (by norm_num) psum58_11
  · exact le_trans (by norm_num) psum58_12
  · exact le_trans (by norm_num) psum58_13
  · exact le_trans (by norm_num) psum58_14
  · exact le_trans (by norm_num) psum58_15
  · exact le_trans (by norm_num) psum58_16
  · exact le_trans (by norm_num) psum58_17
  · exact le_trans (by norm_num) psum58_18
  · exact le_trans (by norm_num) psum58_19
  · exact le_trans (by norm_num) psum58_20
  · exact le_trans (by norm_num) psum58_21
  · exact le_trans (by norm_num) psum58_22
  · exact le_trans (by norm_num) psum58_23
  · exact le_trans (by norm_num) psum58_24
  · exact le_trans (by norm_num) psum58_25
  · exact le_trans (by norm_num) psum58_26
  · exact le_trans (by norm_num) psum58_27
  · exact le_trans (by norm_num) psum58_28
  · exact le_trans (by norm_num) psum58_29
  · exact le_trans (by norm_num) psum58_30
  · exact le_trans (by norm_num) psum58_31
  · exact le_trans (by norm_num) psum58_32
  · exact le_trans (by norm_num) psum58_33
  · exact le_trans (by norm_num) psum58_34
  · exact le_trans (by norm_num) psum58_35
  · exact le_trans (by norm_num) psum58_36
  · exact le_trans (by norm_num) psum58_37
  · exact le_trans (by norm_num) psum58_38
  · exact le_trans (by norm_num) psum58_39
  · exact le_trans (by norm_num) psum58_40
  · exact le_trans (by norm_num) psum58_41
  · exact le_trans (by norm_num) psum58_42
  · exact le_trans (by norm_num) psum58_43
  · exact le_trans (by norm_num) psum58_44
  · exact le_trans (by norm_num) psum58_45
  · exact le_trans (by norm_num) psum58_46
  · exact le_trans (by norm_num) psum58_47
  · exact le_trans (by norm_num) psum58_48
  · exact le_trans (by norm_num) psum58_49
  · exact le_trans (by norm_num) psum58_50
  · exact le_trans (by norm_num) psum58_51
  · exact le_trans (by norm_num) psum58_52
  · exact le_trans (by norm_num) psum58_53
  · exact le_trans (by norm_num) psum58_54
  · exact le_trans (by norm_num) psum58_55
  · exact le_trans (by norm_num) psum58_56
  · exact le_trans (by norm_num) psum58_57
  · exact le_trans (by norm_num) psum58_58
  · exact le_trans (by norm_num) psum58_59
  · exact le_trans (by norm_num) psum58_60
  · exact le_trans (by norm_num) psum58_61
  · exact le_trans (by norm_num) psum58_62
  · exact le_trans (by norm_num) psum58_63
  · exact le_trans (by norm_num) psum58_64
  · exact le_trans (by norm_num) psum58_65
  · exact le_trans (by norm_num) psum58_66
  · exact le_trans (by norm_num) psum58_67
  · exact le_trans (by norm_num) psum58_68
  · exact le_trans (by norm_num) psum58_69
  · exact le_trans (by norm_num) psum58_70
  · exact le_trans (by norm_num) psum58_71
  · exact le_trans (by norm_num) psum58_72
  · exact le_trans (by norm_num) psum58_73
  · exact le_trans (by norm_num) psum58_74
  · exact le_trans (by norm_num) psum58_75
  · exact le_trans (by norm_num) psum58_76
  · exact le_trans (by norm_num) psum58_77
  · exact le_trans (by norm_num) psum58_78
  · exact le_trans (by norm_num) psum58_79
  · exact le_trans (by norm_num) psum58_80
  · exact le_trans (by norm_num) psum58_81
  · exact le_trans (by norm_num) psum58_82
  · exact le_trans (by norm_num) psum58_83
  · exact le_trans (by norm_num) psum58_84
  · exact le_trans (by norm_num) psum58_85
  · exact le_trans (by norm_num) psum58_86
  · exact le_trans (by norm_num) psum58_87
  · exact le_trans (by norm_num) psum58_88
  · exact le_trans (by norm_num) psum58_89
  · exact le_trans (by norm_num) psum58_90
  · exact le_trans (by norm_num) psum58_91
  · exact le_trans (by norm_num) psum58_92
  · exact le_trans (by norm_num) psum58_93
  · exact le_trans (by norm_num) psum58_94
  · exact le_trans (by norm_num) psum58_95
  · exact le_trans (by norm_num) psum58_96
  · exact le_trans (by norm_num) psum58_97
  · exact le_trans (by norm_num) psum58_98
  · exact le_trans (by norm_num) psum58_99
  · exact le_trans (by norm_num) psum58_100

end CriticalLinePhasor.DVP

section AxiomAudit
#print axioms CriticalLinePhasor.DVP.psum58_floor
#print axioms CriticalLinePhasor.DVP.psum58_100
end AxiomAudit
