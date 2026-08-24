import RequestProject.DVPCos126Table

/-!
# The cosine partial-sum floor, `t = 126`
-/

open Finset

noncomputable section

namespace CriticalLinePhasor.DVP

/-- The cosine sequence of the `t = 126` segment certificate. -/
def cos126c (n : ℕ) : ℝ := Real.cos (((126:ℕ):ℝ) * Real.log n)

theorem psum126_11 : ((171337/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 11, cos126c k := by
  rw [Finset.Icc_self, Finset.sum_singleton]
  have h : -((1/25000 : ℚ) : ℝ) ≤ cos126c 11 - ((34269/40000 : ℚ) : ℝ) :=
    (abs_le.mp cos126_br_11).1
  push_cast at h ⊢
  linarith

theorem psum126_12 : ((67231/50000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 12, cos126c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 12, cos126c k)
      = (∑ k ∈ Finset.Icc 11 11, cos126c k) + cos126c 12 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 11) (by norm_num) cos126c
    simpa using h
  have hprev := psum126_11
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos126c 12 - ((19519/40000 : ℚ) : ℝ) :=
    (abs_le.mp cos126_br_12).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum126_13 : ((105921/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 13, cos126c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 13, cos126c k)
      = (∑ k ∈ Finset.Icc 11 12, cos126c k) + cos126c 13 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 12) (by norm_num) cos126c
    simpa using h
  have hprev := psum126_12
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos126c 13 - ((-14389/15625 : ℚ) : ℝ) :=
    (abs_le.mp cos126_br_13).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum126_14 : ((261421/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 14, cos126c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 14, cos126c k)
      = (∑ k ∈ Finset.Icc 11 13, cos126c k) + cos126c 14 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 13) (by norm_num) cos126c
    simpa using h
  have hprev := psum126_13
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos126c 14 - ((883461/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos126_br_14).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum126_15 : ((481369/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 15, cos126c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 15, cos126c k)
      = (∑ k ∈ Finset.Icc 11 14, cos126c k) + cos126c 15 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 14) (by norm_num) cos126c
    simpa using h
  have hprev := psum126_14
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos126c 15 - ((-344327/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos126_br_15).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum126_16 : ((77157/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 16, cos126c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 16, cos126c k)
      = (∑ k ∈ Finset.Icc 11 15, cos126c k) + cos126c 16 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 15) (by norm_num) cos126c
    simpa using h
  have hprev := psum126_15
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos126c 16 - ((-12631/15625 : ℚ) : ℝ) :=
    (abs_le.mp cos126_br_16).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum126_17 : ((278327/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 17, cos126c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 17, cos126c k)
      = (∑ k ∈ Finset.Icc 11 16, cos126c k) + cos126c 17 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 16) (by norm_num) cos126c
    simpa using h
  have hprev := psum126_16
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos126c 17 - ((20119/50000 : ℚ) : ℝ) :=
    (abs_le.mp cos126_br_17).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum126_18 : ((1528447/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 18, cos126c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 18, cos126c k)
      = (∑ k ∈ Finset.Icc 11 17, cos126c k) + cos126c 18 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 17) (by norm_num) cos126c
    simpa using h
  have hprev := psum126_17
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos126c 18 - ((971833/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos126_br_18).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum126_19 : ((155391/62500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 19, cos126c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 19, cos126c k)
      = (∑ k ∈ Finset.Icc 11 18, cos126c k) + cos126c 19 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 18) (by norm_num) cos126c
    simpa using h
  have hprev := psum126_18
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos126c 19 - ((957849/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos126_br_19).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum126_20 : ((211079/62500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 20, cos126c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 20, cos126c k)
      = (∑ k ∈ Finset.Icc 11 19, cos126c k) + cos126c 20 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 19) (by norm_num) cos126c
    simpa using h
  have hprev := psum126_19
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos126c 20 - ((111381/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos126_br_20).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum126_21 : ((2160731/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 21, cos126c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 21, cos126c k)
      = (∑ k ∈ Finset.Icc 11 20, cos126c k) + cos126c 21 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 20) (by norm_num) cos126c
    simpa using h
  have hprev := psum126_20
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos126c 21 - ((472119/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos126_br_21).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum126_22 : ((2658857/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 22, cos126c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 22, cos126c k)
      = (∑ k ∈ Finset.Icc 11 21, cos126c k) + cos126c 22 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 21) (by norm_num) cos126c
    simpa using h
  have hprev := psum126_21
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos126c 22 - ((249073/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos126_br_22).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum126_23 : ((1207339/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 23, cos126c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 23, cos126c k)
      = (∑ k ∈ Finset.Icc 11 22, cos126c k) + cos126c 23 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 22) (by norm_num) cos126c
    simpa using h
  have hprev := psum126_22
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos126c 23 - ((719021/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos126_br_23).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum126_24 : ((118373/20000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 24, cos126c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 24, cos126c k)
      = (∑ k ∈ Finset.Icc 11 23, cos126c k) + cos126c 24 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 23) (by norm_num) cos126c
    simpa using h
  have hprev := psum126_23
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos126c 24 - ((-23601/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos126_br_24).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum126_25 : ((2483583/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 25, cos126c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 25, cos126c k)
      = (∑ k ∈ Finset.Icc 11 24, cos126c k) + cos126c 25 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 24) (by norm_num) cos126c
    simpa using h
  have hprev := psum126_24
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos126c 25 - ((-237861/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos126_br_25).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum126_26 : ((4450999/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 26, cos126c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 26, cos126c k)
      = (∑ k ∈ Finset.Icc 11 25, cos126c k) + cos126c 26 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 25) (by norm_num) cos126c
    simpa using h
  have hprev := psum126_25
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos126c 26 - ((-516127/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos126_br_26).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum126_27 : ((660569/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 27, cos126c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 27, cos126c k)
      = (∑ k ∈ Finset.Icc 11 26, cos126c k) + cos126c 27 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 26) (by norm_num) cos126c
    simpa using h
  have hprev := psum126_26
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos126c 27 - ((833593/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos126_br_27).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum126_28 : ((1431027/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 28, cos126c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 28, cos126c k)
      = (∑ k ∈ Finset.Icc 11 27, cos126c k) + cos126c 28 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 27) (by norm_num) cos126c
    simpa using h
  have hprev := psum126_27
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos126c 28 - ((109899/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos126_br_28).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum126_29 : ((4737529/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 29, cos126c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 29, cos126c k)
      = (∑ k ∈ Finset.Icc 11 28, cos126c k) + cos126c 29 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 28) (by norm_num) cos126c
    simpa using h
  have hprev := psum126_28
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos126c 29 - ((-986539/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos126_br_29).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum126_30 : ((1002101/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 30, cos126c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 30, cos126c k)
      = (∑ k ∈ Finset.Icc 11 29, cos126c k) + cos126c 30 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 29) (by norm_num) cos126c
    simpa using h
  have hprev := psum126_29
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos126c 30 - ((34127/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos126_br_30).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum126_31 : ((708109/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 31, cos126c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 31, cos126c k)
      = (∑ k ∈ Finset.Icc 11 30, cos126c k) + cos126c 31 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 30) (by norm_num) cos126c
    simpa using h
  have hprev := psum126_30
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos126c 31 - ((654407/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos126_br_31).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum126_32 : ((4664833/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 32, cos126c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 32, cos126c k)
      = (∑ k ∈ Finset.Icc 11 31, cos126c k) + cos126c 32 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 31) (by norm_num) cos126c
    simpa using h
  have hprev := psum126_31
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos126c 32 - ((-999999/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos126_br_32).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum126_33 : ((2702647/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 33, cos126c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 33, cos126c k)
      = (∑ k ∈ Finset.Icc 11 32, cos126c k) + cos126c 33 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 32) (by norm_num) cos126c
    simpa using h
  have hprev := psum126_32
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos126c 33 - ((740501/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos126_br_33).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum126_34 : ((1298237/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 34, cos126c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 34, cos126c k)
      = (∑ k ∈ Finset.Icc 11 33, cos126c k) + cos126c 34 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 33) (by norm_num) cos126c
    simpa using h
  have hprev := psum126_33
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos126c 34 - ((-106153/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos126_br_34).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum126_35 : ((1225087/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 35, cos126c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 35, cos126c k)
      = (∑ k ∈ Finset.Icc 11 34, cos126c k) + cos126c 35 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 34) (by norm_num) cos126c
    simpa using h
  have hprev := psum126_34
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos126c 35 - ((-3657/12500 : ℚ) : ℝ) :=
    (abs_le.mp cos126_br_35).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum126_36 : ((277411/50000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 36, cos126c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 36, cos126c k)
      = (∑ k ∈ Finset.Icc 11 35, cos126c k) + cos126c 36 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 35) (by norm_num) cos126c
    simpa using h
  have hprev := psum126_35
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos126c 36 - ((80989/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos126_br_36).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum126_37 : ((2349213/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 37, cos126c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 37, cos126c k)
      = (∑ k ∈ Finset.Icc 11 36, cos126c k) + cos126c 37 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 36) (by norm_num) cos126c
    simpa using h
  have hprev := psum126_36
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos126c 37 - ((-424877/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos126_br_37).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum126_38 : ((1128449/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 38, cos126c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 38, cos126c k)
      = (∑ k ∈ Finset.Icc 11 37, cos126c k) + cos126c 38 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 37) (by norm_num) cos126c
    simpa using h
  have hprev := psum126_37
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos126c 38 - ((943859/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos126_br_38).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum126_39 : ((291451/62500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 39, cos126c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 39, cos126c k)
      = (∑ k ∈ Finset.Icc 11 38, cos126c k) + cos126c 39 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 38) (by norm_num) cos126c
    simpa using h
  have hprev := psum126_38
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos126c 39 - ((-978989/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos126_br_39).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum126_40 : ((1412723/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 40, cos126c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 40, cos126c k)
      = (∑ k ∈ Finset.Icc 11 39, cos126c k) + cos126c 40 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 39) (by norm_num) cos126c
    simpa using h
  have hprev := psum126_39
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos126c 40 - ((246929/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos126_br_40).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum126_41 : ((4668327/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 41, cos126c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 41, cos126c k)
      = (∑ k ∈ Finset.Icc 11 40, cos126c k) + cos126c 41 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 40) (by norm_num) cos126c
    simpa using h
  have hprev := psum126_40
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos126c 41 - ((-39301/40000 : ℚ) : ℝ) :=
    (abs_le.mp cos126_br_41).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum126_42 : ((1125161/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 42, cos126c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 42, cos126c k)
      = (∑ k ∈ Finset.Icc 11 41, cos126c k) + cos126c 42 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 41) (by norm_num) cos126c
    simpa using h
  have hprev := psum126_41
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos126c 42 - ((478759/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos126_br_42).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum126_43 : ((4733869/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 43, cos126c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 43, cos126c k)
      = (∑ k ∈ Finset.Icc 11 42, cos126c k) + cos126c 43 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 42) (by norm_num) cos126c
    simpa using h
  have hprev := psum126_42
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos126c 43 - ((-111487/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos126_br_43).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum126_44 : ((5489453/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 44, cos126c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 44, cos126c k)
      = (∑ k ∈ Finset.Icc 11 43, cos126c k) + cos126c 44 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 43) (by norm_num) cos126c
    simpa using h
  have hprev := psum126_43
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos126c 44 - ((94453/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos126_br_44).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum126_45 : ((4969633/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 45, cos126c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 45, cos126c k)
      = (∑ k ∈ Finset.Icc 11 44, cos126c k) + cos126c 45 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 44) (by norm_num) cos126c
    simpa using h
  have hprev := psum126_44
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos126c 45 - ((-25989/50000 : ℚ) : ℝ) :=
    (abs_le.mp cos126_br_45).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum126_46 : ((1028611/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 46, cos126c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 46, cos126c k)
      = (∑ k ∈ Finset.Icc 11 45, cos126c k) + cos126c 46 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 45) (by norm_num) cos126c
    simpa using h
  have hprev := psum126_45
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos126c 46 - ((86731/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos126_br_46).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum126_47 : ((5397647/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 47, cos126c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 47, cos126c k)
      = (∑ k ∈ Finset.Icc 11 46, cos126c k) + cos126c 47 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 46) (by norm_num) cos126c
    simpa using h
  have hprev := psum126_46
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos126c 47 - ((31829/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos126_br_47).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum126_48 : ((2359329/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 48, cos126c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 48, cos126c k)
      = (∑ k ∈ Finset.Icc 11 47, cos126c k) + cos126c 48 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 47) (by norm_num) cos126c
    simpa using h
  have hprev := psum126_47
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos126c 48 - ((-678949/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos126_br_48).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum126_49 : ((5679423/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 49, cos126c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 49, cos126c k)
      = (∑ k ∈ Finset.Icc 11 48, cos126c k) + cos126c 49 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 48) (by norm_num) cos126c
    simpa using h
  have hprev := psum126_48
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos126c 49 - ((192161/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos126_br_49).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum126_50 : ((4728633/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 50, cos126c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 50, cos126c k)
      = (∑ k ∈ Finset.Icc 11 49, cos126c k) + cos126c 50 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 49) (by norm_num) cos126c
    simpa using h
  have hprev := psum126_49
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos126c 50 - ((-3803/4000 : ℚ) : ℝ) :=
    (abs_le.mp cos126_br_50).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum126_51 : ((2650397/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 51, cos126c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 51, cos126c k)
      = (∑ k ∈ Finset.Icc 11 50, cos126c k) + cos126c 51 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 50) (by norm_num) cos126c
    simpa using h
  have hprev := psum126_50
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos126c 51 - ((572201/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos126_br_51).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum126_52 : ((673297/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 52, cos126c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 52, cos126c k)
      = (∑ k ∈ Finset.Icc 11 51, cos126c k) + cos126c 52 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 51) (by norm_num) cos126c
    simpa using h
  have hprev := psum126_51
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos126c 52 - ((42811/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos126_br_52).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum126_53 : ((930053/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 53, cos126c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 53, cos126c k)
      = (∑ k ∈ Finset.Icc 11 52, cos126c k) + cos126c 53 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 52) (by norm_num) cos126c
    simpa using h
  have hprev := psum126_52
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos126c 53 - ((-736071/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos126_br_53).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum126_54 : ((1412327/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 54, cos126c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 54, cos126c k)
      = (∑ k ∈ Finset.Icc 11 53, cos126c k) + cos126c 54 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 53) (by norm_num) cos126c
    simpa using h
  have hprev := psum126_53
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos126c 54 - ((999083/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos126_br_54).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum126_55 : ((1001261/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 55, cos126c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 55, cos126c k)
      = (∑ k ∈ Finset.Icc 11 54, cos126c k) + cos126c 55 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 54) (by norm_num) cos126c
    simpa using h
  have hprev := psum126_54
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos126c 55 - ((-642963/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos126_br_55).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum126_56 : ((302139/62500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 56, cos126c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 56, cos126c k)
      = (∑ k ∈ Finset.Icc 11 55, cos126c k) + cos126c 56 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 55) (by norm_num) cos126c
    simpa using h
  have hprev := psum126_55
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos126c 56 - ((-172041/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos126_br_56).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum126_57 : ((2859091/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 57, cos126c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 57, cos126c k)
      = (∑ k ∈ Finset.Icc 11 56, cos126c k) + cos126c 57 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 56) (by norm_num) cos126c
    simpa using h
  have hprev := psum126_56
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos126c 57 - ((441999/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos126_br_57).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum126_58 : ((150743/31250 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 58, cos126c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 58, cos126c k)
      = (∑ k ∈ Finset.Icc 11 57, cos126c k) + cos126c 58 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 57) (by norm_num) cos126c
    simpa using h
  have hprev := psum126_57
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos126c 58 - ((-447183/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos126_br_58).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum126_59 : ((1235693/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 59, cos126c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 59, cos126c k)
      = (∑ k ∈ Finset.Icc 11 58, cos126c k) + cos126c 59 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 58) (by norm_num) cos126c
    simpa using h
  have hprev := psum126_58
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos126c 59 - ((29759/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos126_br_59).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum126_60 : ((89514/15625 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 60, cos126c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 60, cos126c k)
      = (∑ k ∈ Finset.Icc 11 59, cos126c k) + cos126c 60 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 59) (by norm_num) cos126c
    simpa using h
  have hprev := psum126_59
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos126c 60 - ((196541/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos126_br_60).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum126_61 : ((480497/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 61, cos126c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 61, cos126c k)
      = (∑ k ∈ Finset.Icc 11 60, cos126c k) + cos126c 61 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 60) (by norm_num) cos126c
    simpa using h
  have hprev := psum126_60
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos126c 61 - ((-461943/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos126_br_61).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum126_62 : ((195607/40000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 62, cos126c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 62, cos126c k)
      = (∑ k ∈ Finset.Icc 11 61, cos126c k) + cos126c 62 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 61) (by norm_num) cos126c
    simpa using h
  have hprev := psum126_61
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos126c 62 - ((17049/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos126_br_62).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum126_63 : ((5752641/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 63, cos126c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 63, cos126c k)
      = (∑ k ∈ Finset.Icc 11 62, cos126c k) + cos126c 63 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 62) (by norm_num) cos126c
    simpa using h
  have hprev := psum126_62
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos126c 63 - ((431253/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos126_br_63).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum126_64 : ((1235659/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 64, cos126c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 64, cos126c k)
      = (∑ k ∈ Finset.Icc 11 63, cos126c k) + cos126c 64 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 63) (by norm_num) cos126c
    simpa using h
  have hprev := psum126_63
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos126c 64 - ((-161993/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos126_br_64).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum126_65 : ((940207/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 65, cos126c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 65, cos126c k)
      = (∑ k ∈ Finset.Icc 11 64, cos126c k) + cos126c 65 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 64) (by norm_num) cos126c
    simpa using h
  have hprev := psum126_64
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos126c 65 - ((-241561/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos126_br_65).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum126_66 : ((1423767/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 66, cos126c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 66, cos126c k)
      = (∑ k ∈ Finset.Icc 11 65, cos126c k) + cos126c 66 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 65) (by norm_num) cos126c
    simpa using h
  have hprev := psum126_65
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos126c 66 - ((994073/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos126_br_66).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum126_67 : ((1318879/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 67, cos126c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 67, cos126c k)
      = (∑ k ∈ Finset.Icc 11 66, cos126c k) + cos126c 67 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 66) (by norm_num) cos126c
    simpa using h
  have hprev := psum126_66
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos126c 67 - ((-52439/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos126_br_67).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum126_68 : ((452951/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 68, cos126c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 68, cos126c k)
      = (∑ k ∈ Finset.Icc 11 67, cos126c k) + cos126c 68 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 67) (by norm_num) cos126c
    simpa using h
  have hprev := psum126_67
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos126c 68 - ((-372983/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos126_br_68).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum126_69 : ((167799/31250 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 69, cos126c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 69, cos126c k)
      = (∑ k ∈ Finset.Icc 11 68, cos126c k) + cos126c 69 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 68) (by norm_num) cos126c
    simpa using h
  have hprev := psum126_68
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos126c 69 - ((420049/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos126_br_69).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum126_70 : ((88979/15625 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 70, cos126c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 70, cos126c k)
      = (∑ k ∈ Finset.Icc 11 69, cos126c k) + cos126c 70 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 69) (by norm_num) cos126c
    simpa using h
  have hprev := psum126_69
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos126c 70 - ((40641/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos126_br_70).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum126_71 : ((73456/15625 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 71, cos126c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 71, cos126c k)
      = (∑ k ∈ Finset.Icc 11 70, cos126c k) + cos126c 71 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 70) (by norm_num) cos126c
    simpa using h
  have hprev := psum126_70
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos126c 71 - ((-124179/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos126_br_71).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum126_72 : ((4777859/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 72, cos126c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 72, cos126c k)
      = (∑ k ∈ Finset.Icc 11 71, cos126c k) + cos126c 72 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 71) (by norm_num) cos126c
    simpa using h
  have hprev := psum126_71
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos126c 72 - ((15343/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos126_br_72).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum126_73 : ((574821/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 73, cos126c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 73, cos126c k)
      = (∑ k ∈ Finset.Icc 11 72, cos126c k) + cos126c 73 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 72) (by norm_num) cos126c
    simpa using h
  have hprev := psum126_72
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos126c 73 - ((970391/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos126_br_73).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum126_74 : ((1342581/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 74, cos126c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 74, cos126c k)
      = (∑ k ∈ Finset.Icc 11 73, cos126c k) + cos126c 74 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 73) (by norm_num) cos126c
    simpa using h
  have hprev := psum126_73
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos126c 74 - ((-188923/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos126_br_74).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum126_75 : ((562069/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 75, cos126c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 75, cos126c k)
      = (∑ k ∈ Finset.Icc 11 74, cos126c k) + cos126c 75 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 74) (by norm_num) cos126c
    simpa using h
  have hprev := psum126_74
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos126c 75 - ((-218433/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos126_br_75).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum126_76 : ((2533079/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 76, cos126c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 76, cos126c k)
      = (∑ k ∈ Finset.Icc 11 75, cos126c k) + cos126c 76 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 75) (by norm_num) cos126c
    simpa using h
  have hprev := psum126_75
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos126c 76 - ((284823/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos126_br_76).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum126_77 : ((1460551/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 77, cos126c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 77, cos126c k)
      = (∑ k ∈ Finset.Icc 11 76, cos126c k) + cos126c 77 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 76) (by norm_num) cos126c
    simpa using h
  have hprev := psum126_76
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos126c 77 - ((388043/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos126_br_77).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum126_78 : ((5169803/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 78, cos126c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 78, cos126c k)
      = (∑ k ∈ Finset.Icc 11 77, cos126c k) + cos126c 78 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 77) (by norm_num) cos126c
    simpa using h
  have hprev := psum126_77
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos126c 78 - ((-672361/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos126_br_78).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum126_79 : ((4453047/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 79, cos126c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 79, cos126c k)
      = (∑ k ∈ Finset.Icc 11 78, cos126c k) + cos126c 79 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 78) (by norm_num) cos126c
    simpa using h
  have hprev := psum126_78
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos126c 79 - ((-179179/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos126_br_79).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum126_80 : ((516043/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 80, cos126c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 80, cos126c k)
      = (∑ k ∈ Finset.Icc 11 79, cos126c k) + cos126c 80 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 79) (by norm_num) cos126c
    simpa using h
  have hprev := psum126_79
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos126c 80 - ((707423/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos126_br_80).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum126_81 : ((2935551/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 81, cos126c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 81, cos126c k)
      = (∑ k ∈ Finset.Icc 11 80, cos126c k) + cos126c 81 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 80) (by norm_num) cos126c
    simpa using h
  have hprev := psum126_80
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos126c 81 - ((88839/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos126_br_81).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum126_82 : ((2592697/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 82, cos126c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 82, cos126c k)
      = (∑ k ∈ Finset.Icc 11 81, cos126c k) + cos126c 82 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 81) (by norm_num) cos126c
    simpa using h
  have hprev := psum126_81
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos126c 82 - ((-171417/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos126_br_82).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum126_83 : ((1107077/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 83, cos126c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 83, cos126c k)
      = (∑ k ∈ Finset.Icc 11 82, cos126c k) + cos126c 83 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 82) (by norm_num) cos126c
    simpa using h
  have hprev := psum126_82
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos126c 83 - ((-378523/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos126_br_83).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum126_84 : ((503363/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 84, cos126c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 84, cos126c k)
      = (∑ k ∈ Finset.Icc 11 83, cos126c k) + cos126c 84 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 83) (by norm_num) cos126c
    simpa using h
  have hprev := psum126_83
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos126c 84 - ((302681/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos126_br_84).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum126_85 : ((2937593/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 85, cos126c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 85, cos126c k)
      = (∑ k ∈ Finset.Icc 11 84, cos126c k) + cos126c 85 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 84) (by norm_num) cos126c
    simpa using h
  have hprev := psum126_84
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos126c 85 - ((210399/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos126_br_85).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum126_86 : ((169349/31250 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 86, cos126c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 86, cos126c k)
      = (∑ k ∈ Finset.Icc 11 85, cos126c k) + cos126c 86 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 85) (by norm_num) cos126c
    simpa using h
  have hprev := psum126_85
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos126c 86 - ((-227989/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos126_br_86).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum126_87 : ((2241499/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 87, cos126c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 87, cos126c k)
      = (∑ k ∈ Finset.Icc 11 86, cos126c k) + cos126c 87 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 86) (by norm_num) cos126c
    simpa using h
  have hprev := psum126_86
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos126c 87 - ((-93613/100000 : ℚ) : ℝ) :=
    (abs_le.mp cos126_br_87).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum126_88 : ((470953/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 88, cos126c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 88, cos126c k)
      = (∑ k ∈ Finset.Icc 11 87, cos126c k) + cos126c 88 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 87) (by norm_num) cos126c
    simpa using h
  have hprev := psum126_87
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos126c 88 - ((56643/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos126_br_88).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum126_89 : ((570617/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 89, cos126c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 89, cos126c k)
      = (∑ k ∈ Finset.Icc 11 88, cos126c k) + cos126c 89 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 88) (by norm_num) cos126c
    simpa using h
  have hprev := psum126_88
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos126c 89 - ((24917/25000 : ℚ) : ℝ) :=
    (abs_le.mp cos126_br_89).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum126_90 : ((1157499/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 90, cos126c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 90, cos126c k)
      = (∑ k ∈ Finset.Icc 11 89, cos126c k) + cos126c 90 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 89) (by norm_num) cos126c
    simpa using h
  have hprev := psum126_89
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos126c 90 - ((16273/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos126_br_90).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum126_91 : ((2410529/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 91, cos126c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 91, cos126c k)
      = (∑ k ∈ Finset.Icc 11 90, cos126c k) + cos126c 91 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 90) (by norm_num) cos126c
    simpa using h
  have hprev := psum126_90
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos126c 91 - ((-966397/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos126_br_91).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum126_92 : ((2191359/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 92, cos126c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 92, cos126c k)
      = (∑ k ∈ Finset.Icc 11 91, cos126c k) + cos126c 92 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 91) (by norm_num) cos126c
    simpa using h
  have hprev := psum126_91
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos126c 92 - ((-4383/10000 : ℚ) : ℝ) :=
    (abs_le.mp cos126_br_92).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum126_93 : ((5171241/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 93, cos126c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 93, cos126c k)
      = (∑ k ∈ Finset.Icc 11 92, cos126c k) + cos126c 93 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 92) (by norm_num) cos126c
    simpa using h
  have hprev := psum126_92
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos126c 93 - ((788563/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos126_br_93).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum126_94 : ((5945443/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 94, cos126c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 94, cos126c k)
      = (∑ k ∈ Finset.Icc 11 93, cos126c k) + cos126c 94 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 93) (by norm_num) cos126c
    simpa using h
  have hprev := psum126_93
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos126c 94 - ((387121/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos126_br_94).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum126_95 : ((5512393/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 95, cos126c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 95, cos126c k)
      = (∑ k ∈ Finset.Icc 11 94, cos126c k) + cos126c 95 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 94) (by norm_num) cos126c
    simpa using h
  have hprev := psum126_94
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos126c 95 - ((-43301/100000 : ℚ) : ℝ) :=
    (abs_le.mp cos126_br_95).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum126_96 : ((4531581/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 96, cos126c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 96, cos126c k)
      = (∑ k ∈ Finset.Icc 11 95, cos126c k) + cos126c 96 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 95) (by norm_num) cos126c
    simpa using h
  have hprev := psum126_95
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos126c 96 - ((-245193/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos126_br_96).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum126_97 : ((2231463/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 97, cos126c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 97, cos126c k)
      = (∑ k ∈ Finset.Icc 11 96, cos126c k) + cos126c 97 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 96) (by norm_num) cos126c
    simpa using h
  have hprev := psum126_96
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos126c 97 - ((-13723/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos126_br_97).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum126_98 : ((2701617/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 98, cos126c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 98, cos126c k)
      = (∑ k ∈ Finset.Icc 11 97, cos126c k) + cos126c 98 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 97) (by norm_num) cos126c
    simpa using h
  have hprev := psum126_97
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos126c 98 - ((235087/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos126_br_98).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum126_99 : ((5999381/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 99, cos126c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 99, cos126c k)
      = (∑ k ∈ Finset.Icc 11 98, cos126c k) + cos126c 99 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 98) (by norm_num) cos126c
    simpa using h
  have hprev := psum126_98
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos126c 99 - ((596187/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos126_br_99).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum126_100 : ((2706069/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 100, cos126c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 100, cos126c k)
      = (∑ k ∈ Finset.Icc 11 99, cos126c k) + cos126c 100 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 99) (by norm_num) cos126c
    simpa using h
  have hprev := psum126_99
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos126c 100 - ((-587203/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos126_br_100).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

/-- **The Abel floor at `t = 126`.** -/
theorem psum126_floor : ∀ j : ℕ, 11 ≤ j → j ≤ 100 →
    ((0 : ℚ) : ℝ) ≤ ∑ k ∈ Finset.Icc 11 j, cos126c k := by
  intro j hj1 hj2
  interval_cases j
  · exact le_trans (by norm_num) psum126_11
  · exact le_trans (by norm_num) psum126_12
  · exact le_trans (by norm_num) psum126_13
  · exact le_trans (by norm_num) psum126_14
  · exact le_trans (by norm_num) psum126_15
  · exact le_trans (by norm_num) psum126_16
  · exact le_trans (by norm_num) psum126_17
  · exact le_trans (by norm_num) psum126_18
  · exact le_trans (by norm_num) psum126_19
  · exact le_trans (by norm_num) psum126_20
  · exact le_trans (by norm_num) psum126_21
  · exact le_trans (by norm_num) psum126_22
  · exact le_trans (by norm_num) psum126_23
  · exact le_trans (by norm_num) psum126_24
  · exact le_trans (by norm_num) psum126_25
  · exact le_trans (by norm_num) psum126_26
  · exact le_trans (by norm_num) psum126_27
  · exact le_trans (by norm_num) psum126_28
  · exact le_trans (by norm_num) psum126_29
  · exact le_trans (by norm_num) psum126_30
  · exact le_trans (by norm_num) psum126_31
  · exact le_trans (by norm_num) psum126_32
  · exact le_trans (by norm_num) psum126_33
  · exact le_trans (by norm_num) psum126_34
  · exact le_trans (by norm_num) psum126_35
  · exact le_trans (by norm_num) psum126_36
  · exact le_trans (by norm_num) psum126_37
  · exact le_trans (by norm_num) psum126_38
  · exact le_trans (by norm_num) psum126_39
  · exact le_trans (by norm_num) psum126_40
  · exact le_trans (by norm_num) psum126_41
  · exact le_trans (by norm_num) psum126_42
  · exact le_trans (by norm_num) psum126_43
  · exact le_trans (by norm_num) psum126_44
  · exact le_trans (by norm_num) psum126_45
  · exact le_trans (by norm_num) psum126_46
  · exact le_trans (by norm_num) psum126_47
  · exact le_trans (by norm_num) psum126_48
  · exact le_trans (by norm_num) psum126_49
  · exact le_trans (by norm_num) psum126_50
  · exact le_trans (by norm_num) psum126_51
  · exact le_trans (by norm_num) psum126_52
  · exact le_trans (by norm_num) psum126_53
  · exact le_trans (by norm_num) psum126_54
  · exact le_trans (by norm_num) psum126_55
  · exact le_trans (by norm_num) psum126_56
  · exact le_trans (by norm_num) psum126_57
  · exact le_trans (by norm_num) psum126_58
  · exact le_trans (by norm_num) psum126_59
  · exact le_trans (by norm_num) psum126_60
  · exact le_trans (by norm_num) psum126_61
  · exact le_trans (by norm_num) psum126_62
  · exact le_trans (by norm_num) psum126_63
  · exact le_trans (by norm_num) psum126_64
  · exact le_trans (by norm_num) psum126_65
  · exact le_trans (by norm_num) psum126_66
  · exact le_trans (by norm_num) psum126_67
  · exact le_trans (by norm_num) psum126_68
  · exact le_trans (by norm_num) psum126_69
  · exact le_trans (by norm_num) psum126_70
  · exact le_trans (by norm_num) psum126_71
  · exact le_trans (by norm_num) psum126_72
  · exact le_trans (by norm_num) psum126_73
  · exact le_trans (by norm_num) psum126_74
  · exact le_trans (by norm_num) psum126_75
  · exact le_trans (by norm_num) psum126_76
  · exact le_trans (by norm_num) psum126_77
  · exact le_trans (by norm_num) psum126_78
  · exact le_trans (by norm_num) psum126_79
  · exact le_trans (by norm_num) psum126_80
  · exact le_trans (by norm_num) psum126_81
  · exact le_trans (by norm_num) psum126_82
  · exact le_trans (by norm_num) psum126_83
  · exact le_trans (by norm_num) psum126_84
  · exact le_trans (by norm_num) psum126_85
  · exact le_trans (by norm_num) psum126_86
  · exact le_trans (by norm_num) psum126_87
  · exact le_trans (by norm_num) psum126_88
  · exact le_trans (by norm_num) psum126_89
  · exact le_trans (by norm_num) psum126_90
  · exact le_trans (by norm_num) psum126_91
  · exact le_trans (by norm_num) psum126_92
  · exact le_trans (by norm_num) psum126_93
  · exact le_trans (by norm_num) psum126_94
  · exact le_trans (by norm_num) psum126_95
  · exact le_trans (by norm_num) psum126_96
  · exact le_trans (by norm_num) psum126_97
  · exact le_trans (by norm_num) psum126_98
  · exact le_trans (by norm_num) psum126_99
  · exact le_trans (by norm_num) psum126_100

end CriticalLinePhasor.DVP

section AxiomAudit
#print axioms CriticalLinePhasor.DVP.psum126_floor
#print axioms CriticalLinePhasor.DVP.psum126_100
end AxiomAudit
