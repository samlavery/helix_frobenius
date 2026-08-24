import RequestProject.DVPCos780o2Table

/-!
# The cosine partial-sum floor, `t = 780/2` (N = 500)
-/

open Finset

noncomputable section

namespace CriticalLinePhasor.DVP

/-- The cosine sequence of the `t = 780/2` segment certificate. -/
def cos780o2c (n : ℕ) : ℝ := Real.cos (((780:ℕ):ℝ) * (Real.log n / 2))

theorem psum780o2_11 : ((263563/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 11, cos780o2c k := by
  rw [Finset.Icc_self, Finset.sum_singleton]
  have h : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 11 - ((263613/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_11).1
  push_cast at h ⊢
  linarith

theorem psum780o2_12 : ((118943/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 12, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 12, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 11, cos780o2c k) + cos780o2c 12 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 11) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_11
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 12 - ((67689/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_12).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_13 : ((858467/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 13, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 13, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 12, cos780o2c k) + cos780o2c 13 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 12) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_12
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 13 - ((65963/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_13).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_14 : ((302841/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 14, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 14, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 13, cos780o2c k) + cos780o2c 14 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 13) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_13
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 14 - ((352997/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_14).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_15 : ((1028069/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 15, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 15, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 14, cos780o2c k) + cos780o2c 15 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 14) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_14
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 15 - ((422437/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_15).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_16 : ((288039/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 16, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 16, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 15, cos780o2c k) + cos780o2c 16 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 15) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_15
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 16 - ((25761/31250 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_16).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_17 : ((1755857/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 17, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 17, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 16, cos780o2c k) + cos780o2c 17 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 16) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_16
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 17 - ((9866/15625 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_17).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_18 : ((1339443/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 18, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 18, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 17, cos780o2c k) + cos780o2c 18 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 17) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_17
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 18 - ((-104091/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_18).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_19 : ((2757779/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 19, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 19, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 18, cos780o2c k) + cos780o2c 19 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 18) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_18
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 19 - ((78993/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_19).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_20 : ((1850733/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 20, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 20, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 19, cos780o2c k) + cos780o2c 20 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 19) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_19
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 20 - ((943787/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_20).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_21 : ((1172217/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 21, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 21, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 20, cos780o2c k) + cos780o2c 21 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 20) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_20
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 21 - ((493751/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_21).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_22 : ((533739/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 22, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 22, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 21, cos780o2c k) + cos780o2c 22 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 21) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_21
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 22 - ((324311/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_22).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_23 : ((4614673/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 23, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 23, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 22, cos780o2c k) + cos780o2c 23 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 22) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_22
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 23 - ((-722617/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_23).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_24 : ((70812/15625 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 24, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 24, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 23, cos780o2c k) + cos780o2c 24 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 23) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_23
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 24 - ((-16521/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_24).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_25 : ((482291/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 25, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 25, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 24, cos780o2c k) + cos780o2c 25 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 24) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_24
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 25 - ((145521/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_25).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_26 : ((61739/12500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 26, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 26, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 25, cos780o2c k) + cos780o2c 26 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 25) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_25
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 26 - ((11631/100000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_26).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_27 : ((1011297/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 27, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 27, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 26, cos780o2c k) + cos780o2c 27 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 26) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_26
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 27 - ((-111729/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_27).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_28 : ((4534323/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 28, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 28, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 27, cos780o2c k) + cos780o2c 28 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 27) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_27
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 28 - ((97847/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_28).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_29 : ((1383111/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 29, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 29, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 28, cos780o2c k) + cos780o2c 29 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 28) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_28
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 29 - ((998221/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_29).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_30 : ((251501/40000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 30, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 30, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 29, cos780o2c k) + cos780o2c 30 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 29) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_29
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 30 - ((755181/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_30).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_31 : ((687999/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 31, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 31, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 30, cos780o2c k) + cos780o2c 31 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 30) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_30
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 31 - ((118513/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_31).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_32 : ((7610091/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 32, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 32, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 31, cos780o2c k) + cos780o2c 32 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 31) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_31
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 32 - ((730201/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_32).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_33 : ((8592607/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 33, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 33, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 32, cos780o2c k) + cos780o2c 33 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 32) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_32
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 33 - ((122827/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_33).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_34 : ((9333017/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 34, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 34, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 33, cos780o2c k) + cos780o2c 34 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 33) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_33
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 34 - ((74051/100000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_34).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_35 : ((2229599/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 35, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 35, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 34, cos780o2c k) + cos780o2c 35 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 34) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_34
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 35 - ((-414521/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_35).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_36 : ((1001499/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 36, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 36, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 35, cos780o2c k) + cos780o2c 36 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 35) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_35
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 36 - ((-14161/15625 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_36).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_37 : ((4345411/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 37, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 37, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 36, cos780o2c k) + cos780o2c 37 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 36) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_36
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 37 - ((67893/100000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_37).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_38 : ((2229557/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 38, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 38, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 37, cos780o2c k) + cos780o2c 38 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 37) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_37
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 38 - ((113753/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_38).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_39 : ((8113421/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 39, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 39, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 38, cos780o2c k) + cos780o2c 39 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 38) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_38
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 39 - ((-804707/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_39).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_40 : ((9095989/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 40, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 40, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 39, cos780o2c k) + cos780o2c 40 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 39) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_39
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 40 - ((245667/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_40).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_41 : ((8096067/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 41, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 41, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 40, cos780o2c k) + cos780o2c 41 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 40) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_40
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 41 - ((-499911/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_41).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_42 : ((142124/15625 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 42, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 42, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 41, cos780o2c k) + cos780o2c 42 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 41) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_41
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 42 - ((999969/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_42).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_43 : ((254011/31250 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 43, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 43, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 42, cos780o2c k) + cos780o2c 43 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 42) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_42
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 43 - ((-241871/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_43).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_44 : ((4441809/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 44, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 44, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 43, cos780o2c k) + cos780o2c 44 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 43) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_43
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 44 - ((377683/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_44).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_45 : ((434447/50000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 45, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 45, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 44, cos780o2c k) + cos780o2c 45 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 44) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_44
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 45 - ((-97289/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_45).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_46 : ((8077953/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 46, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 46, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 45, cos780o2c k) + cos780o2c 46 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 45) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_45
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 46 - ((-610887/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_46).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_47 : ((9070211/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 47, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 47, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 46, cos780o2c k) + cos780o2c 47 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 46) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_46
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 47 - ((496179/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_47).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_48 : ((4419539/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 48, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 48, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 47, cos780o2c k) + cos780o2c 48 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 47) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_47
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 48 - ((-231033/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_48).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_49 : ((7926153/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 49, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 49, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 48, cos780o2c k) + cos780o2c 49 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 48) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_48
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 49 - ((-36513/40000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_49).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_50 : ((8357193/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 50, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 50, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 49, cos780o2c k) + cos780o2c 50 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 49) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_49
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 50 - ((21557/50000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_50).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_51 : ((1861591/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 51, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 51, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 50, cos780o2c k) + cos780o2c 51 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 50) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_50
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 51 - ((475431/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_51).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_52 : ((1854799/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 52, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 52, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 51, cos780o2c k) + cos780o2c 52 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 51) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_51
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 52 - ((-1693/50000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_52).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_53 : ((521843/62500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 53, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 53, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 52, cos780o2c k) + cos780o2c 53 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 52) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_52
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 53 - ((-924407/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_53).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_54 : ((1506571/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 54, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 54, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 53, cos780o2c k) + cos780o2c 54 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 53) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_53
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 54 - ((-816533/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_54).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_55 : ((116413/15625 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 55, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 55, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 54, cos780o2c k) + cos780o2c 55 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 54) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_54
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 55 - ((-82323/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_55).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_56 : ((4032361/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 56, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 56, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 55, cos780o2c k) + cos780o2c 56 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 55) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_55
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 56 - ((61439/100000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_56).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_57 : ((4511501/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 57, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 57, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 56, cos780o2c k) + cos780o2c 57 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 56) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_56
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 57 - ((47919/50000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_57).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_58 : ((5000457/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 58, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 58, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 57, cos780o2c k) + cos780o2c 58 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 57) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_57
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 58 - ((244503/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_58).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_59 : ((5414839/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 59, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 59, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 58, cos780o2c k) + cos780o2c 59 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 58) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_58
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 59 - ((12951/15625 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_59).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_60 : ((2295597/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 60, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 60, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 59, cos780o2c k) + cos780o2c 60 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 59) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_59
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 60 - ((648407/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_60).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_61 : ((2998487/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 61, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 61, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 60, cos780o2c k) + cos780o2c 61 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 60) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_60
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 61 - ((516063/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_61).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_62 : ((3114757/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 62, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 62, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 61, cos780o2c k) + cos780o2c 62 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 61) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_61
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 62 - ((23259/50000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_62).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_63 : ((3240439/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 63, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 63, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 62, cos780o2c k) + cos780o2c 63 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 62) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_62
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 63 - ((125707/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_63).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_64 : ((13581243/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 64, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 64, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 63, cos780o2c k) + cos780o2c 64 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 63) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_63
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 64 - ((619587/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_64).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_65 : ((7183711/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 65, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 65, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 64, cos780o2c k) + cos780o2c 65 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 64) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_64
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 65 - ((786279/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_65).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_66 : ((1913877/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 66, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 66, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 65, cos780o2c k) + cos780o2c 66 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 65) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_65
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 66 - ((471847/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_66).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_67 : ((16307619/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 67, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 67, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 66, cos780o2c k) + cos780o2c 67 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 66) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_66
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 67 - ((996703/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_67).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_68 : ((8570193/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 68, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 68, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 67, cos780o2c k) + cos780o2c 68 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 67) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_67
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 68 - ((832867/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_68).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_69 : ((17524739/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 69, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 69, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 68, cos780o2c k) + cos780o2c 69 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 68) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_68
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 69 - ((384453/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_69).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_70 : ((1725119/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 70, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 70, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 69, cos780o2c k) + cos780o2c 70 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 69) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_69
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 70 - ((-273449/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_70).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_71 : ((3278947/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 71, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 71, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 70, cos780o2c k) + cos780o2c 71 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 70) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_70
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 71 - ((-171271/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_71).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_72 : ((15435227/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 72, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 72, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 71, cos780o2c k) + cos780o2c 72 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 71) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_71
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 72 - ((-59963/62500 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_72).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_73 : ((3765797/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 73, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 73, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 72, cos780o2c k) + cos780o2c 73 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 72) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_72
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 73 - ((-371939/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_73).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_74 : ((3124869/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 74, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 74, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 73, cos780o2c k) + cos780o2c 74 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 73) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_73
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 74 - ((561257/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_74).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_75 : ((16621561/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 75, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 75, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 74, cos780o2c k) + cos780o2c 75 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 74) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_74
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 75 - ((249329/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_75).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_76 : ((849617/50000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 76, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 76, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 75, cos780o2c k) + cos780o2c 76 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 75) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_75
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 76 - ((370879/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_76).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_77 : ((4067833/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 77, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 77, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 76, cos780o2c k) + cos780o2c 77 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 76) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_76
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 77 - ((-180227/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_77).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_78 : ((7693319/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 78, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 78, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 77, cos780o2c k) + cos780o2c 78 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 77) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_77
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 78 - ((-442297/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_78).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_79 : ((7806943/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 79, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 79, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 78, cos780o2c k) + cos780o2c 79 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 78) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_78
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 79 - ((56837/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_79).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_80 : ((8306569/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 80, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 80, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 79, cos780o2c k) + cos780o2c 80 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 79) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_79
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 80 - ((124919/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_80).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_81 : ((3341853/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 81, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 81, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 80, cos780o2c k) + cos780o2c 81 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 80) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_80
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 81 - ((96227/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_81).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_82 : ((7861733/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 82, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 82, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 81, cos780o2c k) + cos780o2c 82 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 81) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_81
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 82 - ((-985699/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_82).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_83 : ((3885031/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 83, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 83, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 82, cos780o2c k) + cos780o2c 83 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 82) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_82
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 83 - ((-91621/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_83).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_84 : ((132239/8000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 84, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 84, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 83, cos780o2c k) + cos780o2c 84 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 83) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_83
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 84 - ((989851/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_84).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_85 : ((8287699/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 85, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 85, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 84, cos780o2c k) + cos780o2c 85 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 84) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_84
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 85 - ((45623/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_85).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_86 : ((7790419/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 86, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 86, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 85, cos780o2c k) + cos780o2c 86 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 85) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_85
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 86 - ((-49723/50000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_86).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_87 : ((3176959/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 87, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 87, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 86, cos780o2c k) + cos780o2c 87 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 86) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_86
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 87 - ((304057/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_87).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_88 : ((8364871/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 88, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 88, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 87, cos780o2c k) + cos780o2c 88 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 87) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_87
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 88 - ((845047/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_88).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_89 : ((997843/62500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 89, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 89, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 88, cos780o2c k) + cos780o2c 89 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 88) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_88
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 89 - ((-382077/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_89).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_90 : ((7813/500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 90, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 90, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 89, cos780o2c k) + cos780o2c 90 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 89) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_89
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 90 - ((-84847/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_90).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_91 : ((8312147/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 91, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 91, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 90, cos780o2c k) + cos780o2c 91 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 90) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_90
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 91 - ((499197/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_91).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_92 : ((1008679/62500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 92, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 92, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 91, cos780o2c k) + cos780o2c 92 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 91) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_91
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 92 - ((-48533/100000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_92).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_93 : ((7800443/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 93, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 93, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 92, cos780o2c k) + cos780o2c 93 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 92) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_92
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 93 - ((-268939/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_93).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_94 : ((1660043/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 94, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 94, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 93, cos780o2c k) + cos780o2c 94 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 93) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_93
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 94 - ((249911/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_94).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_95 : ((4017567/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 95, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 95, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 94, cos780o2c k) + cos780o2c 95 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 94) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_94
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 95 - ((-265031/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_95).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_96 : ((7847981/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 96, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 96, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 95, cos780o2c k) + cos780o2c 96 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 95) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_95
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 96 - ((-187103/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_96).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_97 : ((8327429/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 97, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 97, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 96, cos780o2c k) + cos780o2c 97 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 96) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_96
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 97 - ((239749/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_97).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_98 : ((15813443/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 98, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 98, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 97, cos780o2c k) + cos780o2c 98 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 97) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_97
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 98 - ((-168263/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_98).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_99 : ((1599421/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 99, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 99, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 98, cos780o2c k) + cos780o2c 99 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 98) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_98
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 99 - ((180867/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_99).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_100 : ((16555577/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 100, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 100, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 99, cos780o2c k) + cos780o2c 100 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 99) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_99
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 100 - ((561467/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_100).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_101 : ((15583097/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 101, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 101, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 100, cos780o2c k) + cos780o2c 101 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 100) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_100
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 101 - ((-48619/50000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_101).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_102 : ((4119179/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 102, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 102, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 101, cos780o2c k) + cos780o2c 102 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 101) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_101
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 102 - ((893719/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_102).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_103 : ((16048613/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 103, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 103, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 102, cos780o2c k) + cos780o2c 103 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 102) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_102
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 103 - ((-428003/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_103).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_104 : ((15865287/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 104, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 104, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 103, cos780o2c k) + cos780o2c 104 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 103) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_103
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 104 - ((-91613/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_104).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_105 : ((3312949/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 105, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 105, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 104, cos780o2c k) + cos780o2c 105 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 104) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_104
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 105 - ((349779/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_105).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_106 : ((623741/40000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 106, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 106, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 105, cos780o2c k) + cos780o2c 106 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 105) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_105
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 106 - ((-12139/12500 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_106).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_107 : ((3310923/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 107, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 107, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 106, cos780o2c k) + cos780o2c 107 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 106) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_106
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 107 - ((96119/100000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_107).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_108 : ((7916863/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 108, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 108, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 107, cos780o2c k) + cos780o2c 108 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 107) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_107
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 108 - ((-720789/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_108).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_109 : ((16178457/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 109, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 109, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 108, cos780o2c k) + cos780o2c 109 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 108) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_108
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 109 - ((344831/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_109).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_110 : ((2030791/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 110, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 110, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 109, cos780o2c k) + cos780o2c 110 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 109) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_109
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 110 - ((67971/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_110).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_111 : ((3161193/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 111, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 111, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 110, cos780o2c k) + cos780o2c 111 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 110) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_110
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 111 - ((-440263/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_111).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_112 : ((8265783/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 112, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 112, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 111, cos780o2c k) + cos780o2c 112 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 111) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_111
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 112 - ((725701/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_112).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_113 : ((7812009/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 113, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 113, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 112, cos780o2c k) + cos780o2c 113 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 112) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_112
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 113 - ((-113431/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_113).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_114 : ((16614261/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 114, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 114, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 113, cos780o2c k) + cos780o2c 114 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 113) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_113
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 114 - ((990343/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_114).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_115 : ((15622021/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 115, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 115, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 114, cos780o2c k) + cos780o2c 115 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 114) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_114
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 115 - ((-49607/50000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_115).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_116 : ((4139411/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 116, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 116, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 115, cos780o2c k) + cos780o2c 116 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 115) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_115
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 116 - ((935723/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_116).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_117 : ((3928451/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 117, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 117, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 116, cos780o2c k) + cos780o2c 117 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 116) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_116
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 117 - ((-42187/50000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_117).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_118 : ((205617/12500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 118, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 118, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 117, cos780o2c k) + cos780o2c 118 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 117) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_117
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 118 - ((91957/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_118).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_119 : ((15822729/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 119, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 119, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 118, cos780o2c k) + cos780o2c 119 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 118) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_118
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 119 - ((-626531/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_119).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_120 : ((3269923/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 120, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 120, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 119, cos780o2c k) + cos780o2c 120 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 119) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_119
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 120 - ((263493/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_120).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_121 : ((3976367/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 121, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 121, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 120, cos780o2c k) + cos780o2c 121 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 120) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_120
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 121 - ((-444047/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_121).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_122 : ((4071807/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 122, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 122, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 121, cos780o2c k) + cos780o2c 122 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 121) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_121
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 122 - ((19093/50000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_122).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_123 : ((15944499/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 123, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 123, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 122, cos780o2c k) + cos780o2c 123 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 122) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_122
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 123 - ((-342629/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_123).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_124 : ((3254331/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 124, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 124, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 123, cos780o2c k) + cos780o2c 124 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 123) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_123
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 124 - ((40907/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_124).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_125 : ((637431/40000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 125, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 125, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 124, cos780o2c k) + cos780o2c 125 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 124) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_124
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 125 - ((-16789/50000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_125).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_126 : ((4075819/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 126, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 126, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 125, cos780o2c k) + cos780o2c 126 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 125) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_125
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 126 - ((367601/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_126).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_127 : ((15881737/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 127, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 127, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 126, cos780o2c k) + cos780o2c 127 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 126) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_126
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 127 - ((-421439/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_127).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_128 : ((8188293/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 128, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 128, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 127, cos780o2c k) + cos780o2c 128 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 127) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_127
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 128 - ((494949/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_128).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_129 : ((3947987/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 129, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 129, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 128, cos780o2c k) + cos780o2c 129 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 128) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_128
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 129 - ((-292269/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_129).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_130 : ((4119161/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 130, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 130, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 129, cos780o2c k) + cos780o2c 130 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 129) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_129
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 130 - ((171199/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_130).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_131 : ((1961081/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 131, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 131, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 130, cos780o2c k) + cos780o2c 131 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 130) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_130
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 131 - ((-98487/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_131).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_132 : ((8286001/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 132, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 132, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 131, cos780o2c k) + cos780o2c 132 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 131) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_131
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 132 - ((441727/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_132).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_133 : ((3122699/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 133, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 133, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 132, cos780o2c k) + cos780o2c 133 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 132) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_132
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 133 - ((-958407/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_133).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_134 : ((8305501/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 134, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 134, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 133, cos780o2c k) + cos780o2c 134 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 133) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_133
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 134 - ((997607/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_134).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_135 : ((1562579/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 135, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 135, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 134, cos780o2c k) + cos780o2c 135 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 134) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_134
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 135 - ((-123139/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_135).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_136 : ((4133021/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 136, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 136, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 135, cos780o2c k) + cos780o2c 136 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 135) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_135
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 136 - ((453197/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_136).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_137 : ((3156107/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 137, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 137, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 136, cos780o2c k) + cos780o2c 137 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 136) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_136
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 137 - ((-751449/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_137).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_138 : ((16298867/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 138, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 138, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 137, cos780o2c k) + cos780o2c 138 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 137) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_137
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 138 - ((16201/31250 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_138).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_139 : ((16081181/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 139, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 139, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 138, cos780o2c k) + cos780o2c 139 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 138) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_138
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 139 - ((-108793/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_139).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_140 : ((15954881/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 140, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 140, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 139, cos780o2c k) + cos780o2c 140 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 139) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_139
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 140 - ((-631/5000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_140).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_141 : ((8213737/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 141, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 141, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 140, cos780o2c k) + cos780o2c 141 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 140) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_140
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 141 - ((472693/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_141).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_142 : ((3914521/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 142, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 142, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 141, cos780o2c k) + cos780o2c 142 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 141) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_141
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 142 - ((-76929/100000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_142).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_143 : ((8308351/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 143, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 143, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 142, cos780o2c k) + cos780o2c 143 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 142) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_142
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 143 - ((479359/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_143).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_144 : ((1953221/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 144, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 144, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 143, cos780o2c k) + cos780o2c 144 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 143) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_143
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 144 - ((-495417/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_144).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_145 : ((4115793/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 145, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 145, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 144, cos780o2c k) + cos780o2c 145 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 144) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_144
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 145 - ((13086/15625 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_145).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_146 : ((15956213/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 146, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 146, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 145, cos780o2c k) + cos780o2c 146 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 145) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_145
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 146 - ((-506859/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_146).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_147 : ((3201627/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 147, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 147, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 146, cos780o2c k) + cos780o2c 147 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 146) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_146
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 147 - ((26011/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_147).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_148 : ((256858/15625 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 148, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 148, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 147, cos780o2c k) + cos780o2c 148 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 147) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_147
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 148 - ((430877/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_148).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_149 : ((7809593/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 149, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 149, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 148, cos780o2c k) + cos780o2c 149 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 148) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_148
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 149 - ((-409813/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_149).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_150 : ((8308057/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 150, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 150, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 149, cos780o2c k) + cos780o2c 150 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 149) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_149
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 150 - ((249257/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_150).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_151 : ((7862923/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 151, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 151, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 150, cos780o2c k) + cos780o2c 151 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 150) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_150
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 151 - ((-111271/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_151).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_152 : ((811581/50000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 152, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 152, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 151, cos780o2c k) + cos780o2c 152 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 151) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_151
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 152 - ((252937/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_152).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_153 : ((8142653/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 153, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 153, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 152, cos780o2c k) + cos780o2c 153 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 152) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_152
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 153 - ((26893/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_153).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_154 : ((15676307/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 154, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 154, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 153, cos780o2c k) + cos780o2c 154 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 153) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_153
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 154 - ((-608899/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_154).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_155 : ((3326379/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 155, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 155, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 154, cos780o2c k) + cos780o2c 155 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 154) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_154
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 155 - ((119461/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_155).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_156 : ((15687297/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 156, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 156, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 155, cos780o2c k) + cos780o2c 156 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 155) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_155
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 156 - ((-472249/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_156).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_157 : ((16240639/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 157, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 157, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 156, cos780o2c k) + cos780o2c 157 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 156) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_156
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 157 - ((276721/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_157).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_158 : ((1631937/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 158, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 158, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 157, cos780o2c k) + cos780o2c 158 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 157) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_157
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 158 - ((78831/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_158).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_159 : ((1953801/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 159, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 159, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 158, cos780o2c k) + cos780o2c 159 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 158) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_158
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 159 - ((-344431/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_159).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_160 : ((2077971/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 160, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 160, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 159, cos780o2c k) + cos780o2c 160 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 159) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_159
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 160 - ((49673/50000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_160).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_161 : ((15796793/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 161, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 161, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 160, cos780o2c k) + cos780o2c 161 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 160) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_160
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 161 - ((-1323/1600 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_161).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_162 : ((16041011/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 162, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 162, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 161, cos780o2c k) + cos780o2c 162 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 161) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_161
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 162 - ((122159/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_162).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_163 : ((1032233/62500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 163, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 163, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 162, cos780o2c k) + cos780o2c 163 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 162) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_162
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 163 - ((474817/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_163).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_164 : ((15566319/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 164, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 164, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 163, cos780o2c k) + cos780o2c 164 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 163) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_163
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 164 - ((-949309/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_164).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_165 : ((16466223/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 165, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 165, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 164, cos780o2c k) + cos780o2c 165 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 164) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_164
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 165 - ((225001/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_165).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_166 : ((16137653/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 166, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 166, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 165, cos780o2c k) + cos780o2c 166 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 165) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_165
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 166 - ((-32847/100000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_166).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_167 : ((15689551/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 167, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 167, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 166, cos780o2c k) + cos780o2c 167 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 166) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_166
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 167 - ((-224001/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_167).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_168 : ((16646829/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 168, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 168, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 167, cos780o2c k) + cos780o2c 168 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 167) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_167
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 168 - ((478689/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_168).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_169 : ((3157191/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 169, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 169, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 168, cos780o2c k) + cos780o2c 169 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 168) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_168
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 169 - ((-430387/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_169).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_170 : ((399517/25000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 170, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 170, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 169, cos780o2c k) + cos780o2c 170 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 169) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_169
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 170 - ((7793/40000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_170).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_171 : ((8296107/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 171, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 171, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 170, cos780o2c k) + cos780o2c 171 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 170) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_170
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 171 - ((305817/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_171).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_172 : ((3898283/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 172, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 172, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 171, cos780o2c k) + cos780o2c 172 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 171) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_171
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 172 - ((-499491/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_172).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_173 : ((1626377/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 173, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 173, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 172, cos780o2c k) + cos780o2c 173 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 172) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_172
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 173 - ((335369/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_173).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_174 : ((8210777/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 174, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 174, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 173, cos780o2c k) + cos780o2c 174 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 173) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_173
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 174 - ((39471/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_174).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_175 : ((1943323/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 175, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 175, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 174, cos780o2c k) + cos780o2c 175 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 174) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_174
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 175 - ((-87487/100000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_175).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_176 : ((8231053/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 176, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 176, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 175, cos780o2c k) + cos780o2c 176 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 175) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_175
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 176 - ((457811/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_176).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_177 : ((811939/50000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 177, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 177, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 176, cos780o2c k) + cos780o2c 177 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 176) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_176
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 177 - ((-111613/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_177).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_178 : ((15579831/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 178, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 178, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 177, cos780o2c k) + cos780o2c 178 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 177) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_177
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 178 - ((-658849/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_178).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_179 : ((4143551/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 179, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 179, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 178, cos780o2c k) + cos780o2c 179 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 178) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_178
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 179 - ((994473/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_179).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_180 : ((4024393/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 180, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 180, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 179, cos780o2c k) + cos780o2c 180 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 179) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_179
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 180 - ((-119133/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_180).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_181 : ((3907991/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 181, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 181, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 180, cos780o2c k) + cos780o2c 181 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 180) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_180
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 181 - ((-116377/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_181).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_182 : ((8313737/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 182, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 182, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 181, cos780o2c k) + cos780o2c 182 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 181) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_181
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 182 - ((99561/100000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_182).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_183 : ((8007149/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 183, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 183, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 182, cos780o2c k) + cos780o2c 183 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 182) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_182
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 183 - ((-153269/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_183).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_184 : ((3916347/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 184, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 184, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 183, cos780o2c k) + cos780o2c 184 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 183) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_183
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 184 - ((-34881/100000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_184).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_185 : ((8323951/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 185, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 185, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 184, cos780o2c k) + cos780o2c 185 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 184) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_184
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 185 - ((491307/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_185).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_186 : ((15989653/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 186, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 186, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 185, cos780o2c k) + cos780o2c 186 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 185) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_185
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 186 - ((-658149/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_186).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_187 : ((15663567/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 187, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 187, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 186, cos780o2c k) + cos780o2c 187 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 186) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_186
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 187 - ((-162993/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_187).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_188 : ((16647819/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 188, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 188, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 187, cos780o2c k) + cos780o2c 188 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 187) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_187
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 188 - ((30761/31250 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_188).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_189 : ((3204513/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 189, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 189, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 188, cos780o2c k) + cos780o2c 189 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 188) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_188
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 189 - ((-312577/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_189).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_190 : ((625019/40000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 190, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 190, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 189, cos780o2c k) + cos780o2c 190 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 189) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_189
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 190 - ((-39699/100000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_190).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_191 : ((2077881/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 191, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 191, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 190, cos780o2c k) + cos780o2c 191 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 190) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_190
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 191 - ((997673/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_191).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_192 : ((3222797/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 192, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 192, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 191, cos780o2c k) + cos780o2c 192 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 191) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_191
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 192 - ((-508963/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_192).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_193 : ((1556449/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 193, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 193, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 192, cos780o2c k) + cos780o2c 193 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 192) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_192
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 193 - ((-109879/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_193).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_194 : ((2069379/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 194, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 194, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 193, cos780o2c k) + cos780o2c 194 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 193) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_193
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 194 - ((495321/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_194).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_195 : ((3252373/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 195, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 195, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 194, cos780o2c k) + cos780o2c 195 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 194) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_194
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 195 - ((-293067/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_195).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_196 : ((7755483/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 196, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 196, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 195, cos780o2c k) + cos780o2c 196 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 195) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_195
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 196 - ((-750799/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_196).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_197 : ((8208801/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 197, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 197, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 196, cos780o2c k) + cos780o2c 197 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 196) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_196
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 197 - ((56671/62500 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_197).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_198 : ((4112231/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 198, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 198, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 197, cos780o2c k) + cos780o2c 198 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 197) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_197
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 198 - ((15711/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_198).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_199 : ((15513817/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 199, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 199, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 198, cos780o2c k) + cos780o2c 199 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 198) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_198
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 199 - ((-935007/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_199).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_200 : ((8096431/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 200, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 200, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 199, cos780o2c k) + cos780o2c 200 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 199) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_199
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 200 - ((135829/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_200).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_201 : ((2078447/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 201, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 201, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 200, cos780o2c k) + cos780o2c 201 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 200) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_200
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 201 - ((217407/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_201).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_202 : ((15631101/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 202, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 202, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 201, cos780o2c k) + cos780o2c 202 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 201) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_201
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 202 - ((-7971/8000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_202).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_203 : ((15897699/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 203, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 203, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 202, cos780o2c k) + cos780o2c 203 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 202) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_202
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 203 - ((133349/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_203).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_204 : ((16714009/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 204, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 204, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 203, cos780o2c k) + cos780o2c 204 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 203) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_203
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 204 - ((81641/100000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_204).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_205 : ((15899371/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 205, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 205, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 204, cos780o2c k) + cos780o2c 205 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 204) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_204
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 205 - ((-407269/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_205).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_206 : ((7805777/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 206, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 206, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 205, cos780o2c k) + cos780o2c 206 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 205) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_205
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 206 - ((-287717/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_206).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_207 : ((16611117/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 207, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 207, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 206, cos780o2c k) + cos780o2c 207 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 206) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_206
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 207 - ((999663/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_207).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_208 : ((651301/40000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 208, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 208, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 207, cos780o2c k) + cos780o2c 208 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 207) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_207
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 208 - ((-82123/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_208).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_209 : ((7738507/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 209, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 209, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 208, cos780o2c k) + cos780o2c 209 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 208) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_208
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 209 - ((-805411/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_209).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_210 : ((8137833/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 210, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 210, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 209, cos780o2c k) + cos780o2c 210 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 209) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_209
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 210 - ((24961/31250 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_210).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_211 : ((4157811/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 211, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 211, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 210, cos780o2c k) + cos780o2c 211 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 210) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_210
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 211 - ((177839/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_211).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_212 : ((7817617/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 212, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 212, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 211, cos780o2c k) + cos780o2c 212 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 211) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_211
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 212 - ((-99591/100000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_212).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_213 : ((3952071/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 213, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 213, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 212, cos780o2c k) + cos780o2c 213 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 212) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_212
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 213 - ((3463/20000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_213).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_214 : ((1671717/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 214, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 214, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 213, cos780o2c k) + cos780o2c 214 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 213) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_213
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 214 - ((454493/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_214).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_215 : ((16090351/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 215, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 215, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 214, cos780o2c k) + cos780o2c 215 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 214) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_214
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 215 - ((-626719/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_215).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_216 : ((967593/62500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 216, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 216, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 215, cos780o2c k) + cos780o2c 216 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 215) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_215
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 216 - ((-608763/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_216).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_217 : ((16392869/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 217, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 217, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 216, cos780o2c k) + cos780o2c 217 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 216) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_216
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 217 - ((911481/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_217).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_218 : ((663721/40000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 218, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 218, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 217, cos780o2c k) + cos780o2c 218 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 217) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_217
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 218 - ((3129/15625 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_218).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_219 : ((15593003/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 219, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 219, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 218, cos780o2c k) + cos780o2c 219 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 218) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_218
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 219 - ((-499961/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_219).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_220 : ((494051/31250 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 220, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 220, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 219, cos780o2c k) + cos780o2c 220 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 219) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_219
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 220 - ((216729/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_220).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_221 : ((3344817/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 221, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 221, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 220, cos780o2c k) + cos780o2c 221 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 220) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_220
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 221 - ((914553/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_221).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_222 : ((16154161/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 222, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 222, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 221, cos780o2c k) + cos780o2c 222 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 221) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_221
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 222 - ((-17807/31250 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_222).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_223 : ((7724509/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 223, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 223, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 222, cos780o2c k) + cos780o2c 223 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 222) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_222
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 223 - ((-705043/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_223).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_224 : ((16269537/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 224, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 224, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 223, cos780o2c k) + cos780o2c 224 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 223) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_223
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 224 - ((820619/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_224).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_225 : ((417427/25000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 225, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 225, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 224, cos780o2c k) + cos780o2c 225 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 224) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_224
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 225 - ((427643/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_225).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_226 : ((3147363/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 226, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 226, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 225, cos780o2c k) + cos780o2c 226 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 225) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_225
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 226 - ((-192033/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_226).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_227 : ((7802483/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 227, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 227, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 226, cos780o2c k) + cos780o2c 227 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 226) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_226
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 227 - ((-131749/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_227).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_228 : ((8302401/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 228, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 228, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 227, cos780o2c k) + cos780o2c 228 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 227) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_227
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 228 - ((15624/15625 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_228).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_229 : ((411447/25000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 229, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 229, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 228, cos780o2c k) + cos780o2c 229 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 228) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_228
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 229 - ((-73411/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_229).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_230 : ((15495601/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 230, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 230, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 229, cos780o2c k) + cos780o2c 230 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 229) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_229
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 230 - ((-962179/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_230).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_231 : ((15882233/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 231, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 231, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 230, cos780o2c k) + cos780o2c 231 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 230) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_230
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 231 - ((96683/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_231).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_232 : ((8377211/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 232, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 232, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 231, cos780o2c k) + cos780o2c 232 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 231) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_231
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 232 - ((872289/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_232).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_233 : ((1617527/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 233, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 233, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 232, cos780o2c k) + cos780o2c 233 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 232) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_232
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 233 - ((-144763/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_233).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_234 : ((3855351/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 234, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 234, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 233, cos780o2c k) + cos780o2c 234 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 233) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_233
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 234 - ((-376883/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_234).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_235 : ((16145137/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 235, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 235, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 234, cos780o2c k) + cos780o2c 235 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 234) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_234
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 235 - ((723833/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_235).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_236 : ((8385433/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 236, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 236, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 235, cos780o2c k) + cos780o2c 236 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 235) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_235
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 236 - ((625829/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_236).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_237 : ((15944277/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 237, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 237, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 236, cos780o2c k) + cos780o2c 237 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 236) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_236
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 237 - ((-826489/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_237).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_238 : ((15441533/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 238, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 238, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 237, cos780o2c k) + cos780o2c 238 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 237) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_237
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 238 - ((-125661/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_238).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_239 : ((8168249/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 239, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 239, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 238, cos780o2c k) + cos780o2c 239 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 238) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_238
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 239 - ((179013/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_239).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_240 : ((16730059/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 240, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 240, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 239, cos780o2c k) + cos780o2c 240 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 239) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_239
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 240 - ((393661/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_240).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_241 : ((15791891/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 241, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 241, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 240, cos780o2c k) + cos780o2c 241 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 240) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_240
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 241 - ((-234517/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_241).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_242 : ((7743523/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 242, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 242, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 241, cos780o2c k) + cos780o2c 242 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 241) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_241
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 242 - ((-60949/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_242).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_243 : ((16450121/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 243, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 243, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 242, cos780o2c k) + cos780o2c 243 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 242) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_242
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 243 - ((38527/40000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_243).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_244 : ((16689053/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 244, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 244, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 243, cos780o2c k) + cos780o2c 244 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 243) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_243
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 244 - ((29879/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_244).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_245 : ((15712423/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 245, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 245, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 244, cos780o2c k) + cos780o2c 245 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 244) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_244
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 245 - ((-97653/100000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_245).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_246 : ((3102873/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 246, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 246, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 245, cos780o2c k) + cos780o2c 246 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 245) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_245
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 246 - ((-98979/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_246).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_247 : ((824833/50000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 247, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 247, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 246, cos780o2c k) + cos780o2c 247 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 246) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_246
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 247 - ((196479/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_247).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_248 : ((33357/2000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 248, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 248, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 247, cos780o2c k) + cos780o2c 248 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 247) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_247
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 248 - ((9097/50000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_248).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_249 : ((7847673/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 249, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 249, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 248, cos780o2c k) + cos780o2c 249 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 248) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_248
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 249 - ((-491527/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_249).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_250 : ((1550443/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 250, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 250, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 249, cos780o2c k) + cos780o2c 250 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 249) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_249
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 250 - ((-5963/31250 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_250).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_251 : ((3296641/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 251, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 251, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 250, cos780o2c k) + cos780o2c 251 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 250) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_250
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 251 - ((7831/8000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_251).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_252 : ((4176803/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 252, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 252, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 251, cos780o2c k) + cos780o2c 252 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 251) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_251
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 252 - ((224107/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_252).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_253 : ((15738763/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 253, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 253, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 252, cos780o2c k) + cos780o2c 253 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 252) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_252
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 253 - ((-968349/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_253).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_254 : ((15457897/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 254, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 254, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 253, cos780o2c k) + cos780o2c 254 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 253) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_253
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 254 - ((-140383/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_254).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_255 : ((16406097/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 255, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 255, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 254, cos780o2c k) + cos780o2c 255 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 254) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_254
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 255 - ((9483/10000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_255).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_256 : ((2095641/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 256, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 256, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 255, cos780o2c k) + cos780o2c 256 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 255) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_255
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 256 - ((359131/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_256).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_257 : ((3170199/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 257, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 257, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 256, cos780o2c k) + cos780o2c 257 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 256) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_256
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 257 - ((-914033/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_257).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_258 : ((7697263/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 258, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 258, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 257, cos780o2c k) + cos780o2c 258 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 257) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_257
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 258 - ((-456369/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_258).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_259 : ((16254189/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 259, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 259, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 258, cos780o2c k) + cos780o2c 259 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 258) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_258
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 259 - ((859763/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_259).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_260 : ((16821933/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 260, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 260, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 259, cos780o2c k) + cos780o2c 260 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 259) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_259
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 260 - ((141961/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_260).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_261 : ((16042721/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 261, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 261, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 260, cos780o2c k) + cos780o2c 261 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 260) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_260
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 261 - ((-97389/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_261).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_262 : ((15355917/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 262, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 262, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 261, cos780o2c k) + cos780o2c 262 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 261) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_261
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 262 - ((-42919/62500 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_262).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_263 : ((8010881/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 263, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 263, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 262, cos780o2c k) + cos780o2c 263 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 262) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_262
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 263 - ((133189/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_263).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_264 : ((16824919/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 264, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 264, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 263, cos780o2c k) + cos780o2c 264 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 263) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_263
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 264 - ((803257/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_264).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_265 : ((16309201/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 265, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 265, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 264, cos780o2c k) + cos780o2c 265 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 264) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_264
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 265 - ((-257809/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_265).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_266 : ((15404293/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 266, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 266, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 265, cos780o2c k) + cos780o2c 266 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 265) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_265
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 266 - ((-113101/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_266).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_267 : ((1573057/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 267, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 267, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 266, cos780o2c k) + cos780o2c 267 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 266) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_266
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 267 - ((326377/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_267).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_268 : ((16706453/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 268, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 268, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 267, cos780o2c k) + cos780o2c 268 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 267) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_267
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 268 - ((975983/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_268).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_269 : ((8302599/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 269, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 269, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 268, cos780o2c k) + cos780o2c 269 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 268) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_268
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 269 - ((-20231/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_269).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_270 : ((15605347/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 270, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 270, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 269, cos780o2c k) + cos780o2c 270 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 269) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_269
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 270 - ((-999751/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_270).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_271 : ((3090897/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 271, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 271, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 270, cos780o2c k) + cos780o2c 271 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 270) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_270
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 271 - ((-75381/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_271).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_272 : ((16413853/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 272, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 272, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 271, cos780o2c k) + cos780o2c 272 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 271) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_271
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 272 - ((239867/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_272).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_273 : ((4206587/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 273, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 273, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 272, cos780o2c k) + cos780o2c 273 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 272) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_272
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 273 - ((82519/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_273).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_274 : ((7992201/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 274, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 274, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 273, cos780o2c k) + cos780o2c 274 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 273) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_273
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 274 - ((-420923/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_274).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_275 : ((1915599/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 275, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 275, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 274, cos780o2c k) + cos780o2c 275 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 274) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_274
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 275 - ((-65951/100000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_275).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_276 : ((15965427/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 276, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 276, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 275, cos780o2c k) + cos780o2c 276 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 275) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_275
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 276 - ((128147/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_276).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_277 : ((4206377/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 277, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 277, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 276, cos780o2c k) + cos780o2c 277 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 276) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_276
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 277 - ((860181/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_277).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_278 : ((8231999/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 278, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 278, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 277, cos780o2c k) + cos780o2c 278 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 277) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_277
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 278 - ((-36141/100000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_278).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_279 : ((967731/62500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 279, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 279, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 278, cos780o2c k) + cos780o2c 279 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 278) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_278
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 279 - ((-490101/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_279).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_280 : ((1938437/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 280, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 280, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 279, cos780o2c k) + cos780o2c 280 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 279) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_279
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 280 - ((239/10000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_280).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_281 : ((257737/15625 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 281, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 281, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 280, cos780o2c k) + cos780o2c 281 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 280) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_280
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 281 - ((246943/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_281).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_282 : ((336607/20000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 282, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 282, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 281, cos780o2c k) + cos780o2c 282 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 281) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_281
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 282 - ((167641/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_282).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_283 : ((7984273/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 283, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 283, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 282, cos780o2c k) + cos780o2c 283 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 282) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_282
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 283 - ((-107713/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_283).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_284 : ((15303599/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 284, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 284, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 283, cos780o2c k) + cos780o2c 284 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 283) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_283
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 284 - ((-664847/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_284).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_285 : ((3975879/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 285, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 285, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 284, cos780o2c k) + cos780o2c 285 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 284) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_284
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 285 - ((600017/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_285).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_286 : ((16808687/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 286, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 286, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 285, cos780o2c k) + cos780o2c 286 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 285) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_285
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 286 - ((905271/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_286).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_287 : ((16581351/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 287, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 287, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 286, cos780o2c k) + cos780o2c 287 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 286) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_286
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 287 - ((-56809/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_287).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_288 : ((15581363/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 288, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 288, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 287, cos780o2c k) + cos780o2c 288 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 287) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_287
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 288 - ((-62493/62500 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_288).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_289 : ((15378637/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 289, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 289, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 288, cos780o2c k) + cos780o2c 289 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 288) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_288
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 289 - ((-101313/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_289).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_290 : ((16288477/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 290, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 290, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 289, cos780o2c k) + cos780o2c 290 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 289) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_289
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 290 - ((45497/50000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_290).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_291 : ((3379659/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 291, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 291, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 290, cos780o2c k) + cos780o2c 291 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 290) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_290
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 291 - ((304959/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_291).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_292 : ((8133933/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 292, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 292, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 291, cos780o2c k) + cos780o2c 292 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 291) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_291
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 292 - ((-630329/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_292).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_293 : ((7682473/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 293, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 293, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 292, cos780o2c k) + cos780o2c 293 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 292) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_292
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 293 - ((-45141/50000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_293).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_294 : ((15565951/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 294, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 294, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 293, cos780o2c k) + cos780o2c 294 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 293) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_293
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 294 - ((40221/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_294).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_295 : ((8282441/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 295, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 295, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 294, cos780o2c k) + cos780o2c 295 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 294) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_294
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 295 - ((999031/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_295).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_296 : ((3371109/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 296, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 296, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 295, cos780o2c k) + cos780o2c 296 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 295) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_295
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 296 - ((290763/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_296).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_297 : ((3200633/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 297, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 297, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 296, cos780o2c k) + cos780o2c 297 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 296) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_296
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 297 - ((-21307/25000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_297).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_298 : ((3819633/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 298, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 298, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 297, cos780o2c k) + cos780o2c 298 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 297) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_297
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 298 - ((-724533/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_298).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_299 : ((15754503/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 299, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 299, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 298, cos780o2c k) + cos780o2c 299 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 298) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_298
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 299 - ((476071/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_299).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_300 : ((16728623/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 300, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 300, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 299, cos780o2c k) + cos780o2c 300 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 299) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_299
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 300 - ((48711/50000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_300).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_301 : ((3354781/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 301, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 301, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 300, cos780o2c k) + cos780o2c 301 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 300) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_300
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 301 - ((22691/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_301).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_302 : ((3956351/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 302, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 302, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 301, cos780o2c k) + cos780o2c 302 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 301) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_301
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 302 - ((-948401/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_302).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_303 : ((762861/50000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 303, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 303, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 302, cos780o2c k) + cos780o2c 303 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 302) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_302
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 303 - ((-142021/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_303).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_304 : ((7943281/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 304, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 304, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 303, cos780o2c k) + cos780o2c 304 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 303) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_303
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 304 - ((314721/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_304).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_305 : ((16811067/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 305, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 305, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 304, cos780o2c k) + cos780o2c 305 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 304) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_304
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 305 - ((184921/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_305).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_306 : ((16714489/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 306, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 306, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 305, cos780o2c k) + cos780o2c 306 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 305) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_305
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 306 - ((-48239/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_306).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_307 : ((983417/62500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 307, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 307, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 306, cos780o2c k) + cos780o2c 307 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 306) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_306
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 307 - ((-979717/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_307).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_308 : ((15251403/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 308, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 308, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 307, cos780o2c k) + cos780o2c 308 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 307) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_307
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 308 - ((-483169/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_308).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_309 : ((7970081/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 309, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 309, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 308, cos780o2c k) + cos780o2c 309 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 308) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_308
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 309 - ((688859/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_309).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_310 : ((16840853/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 310, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 310, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 309, cos780o2c k) + cos780o2c 310 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 309) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_309
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 310 - ((900791/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_310).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_311 : ((16706673/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 311, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 311, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 310, cos780o2c k) + cos780o2c 311 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 310) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_310
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 311 - ((-419/3125 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_311).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_312 : ((7861757/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 312, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 312, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 311, cos780o2c k) + cos780o2c 312 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 311) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_311
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 312 - ((-983059/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_312).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_313 : ((952359/62500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 313, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 313, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 312, cos780o2c k) + cos780o2c 313 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 312) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_312
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 313 - ((-48567/100000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_313).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_314 : ((7954817/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 314, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 314, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 313, cos780o2c k) + cos780o2c 314 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 313) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_313
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 314 - ((67199/100000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_314).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_315 : ((16828171/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 315, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 315, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 314, cos780o2c k) + cos780o2c 315 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 314) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_314
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 315 - ((918637/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_315).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_316 : ((3351321/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 316, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 316, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 315, cos780o2c k) + cos780o2c 316 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 315) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_315
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 316 - ((-35733/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_316).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_317 : ((3158391/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 317, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 317, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 316, cos780o2c k) + cos780o2c 317 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 316) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_316
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 317 - ((-19291/20000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_317).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_318 : ((15219383/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 318, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 318, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 317, cos780o2c k) + cos780o2c 318 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 317) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_317
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 318 - ((-71559/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_318).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_319 : ((3159249/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 319, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 319, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 318, cos780o2c k) + cos780o2c 319 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 318) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_318
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 319 - ((288481/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_319).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_320 : ((8380641/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 320, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 320, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 319, cos780o2c k) + cos780o2c 320 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 319) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_319
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 320 - ((965137/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_320).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_321 : ((2106269/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 321, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 321, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 320, cos780o2c k) + cos780o2c 321 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 320) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_320
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 321 - ((8897/100000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_321).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_322 : ((1594823/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 322, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 322, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 321, cos780o2c k) + cos780o2c 322 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 321) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_321
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 322 - ((-450911/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_322).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_323 : ((15225007/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 323, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 323, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 322, cos780o2c k) + cos780o2c 323 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 322) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_322
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 323 - ((-723123/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_323).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_324 : ((3902949/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 324, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 324, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 323, cos780o2c k) + cos780o2c 324 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 323) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_323
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 324 - ((386889/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_324).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_325 : ((519103/31250 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 325, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 325, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 324, cos780o2c k) + cos780o2c 325 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 324) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_324
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 325 - ((2499/2500 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_325).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_326 : ((8474393/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 326, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 326, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 325, cos780o2c k) + cos780o2c 326 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 325) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_325
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 326 - ((33759/100000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_326).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_327 : ((3239463/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 327, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 327, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 326, cos780o2c k) + cos780o2c 327 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 326) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_326
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 327 - ((-751371/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_327).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_328 : ((765287/50000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 328, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 328, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 327, cos780o2c k) + cos780o2c 328 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 327) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_327
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 328 - ((-35659/40000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_328).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_329 : ((769607/50000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 329, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 329, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 328, cos780o2c k) + cos780o2c 329 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 328) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_328
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 329 - ((173/2000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_329).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_330 : ((8173603/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 330, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 330, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 329, cos780o2c k) + cos780o2c 330 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 329) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_329
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 330 - ((477583/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_330).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_331 : ((4246171/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 331, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 331, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 330, cos780o2c k) + cos780o2c 331 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 330) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_330
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 331 - ((318789/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_331).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_332 : ((8259133/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 332, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 332, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 331, cos780o2c k) + cos780o2c 332 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 331) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_331
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 332 - ((-233159/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_332).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_333 : ((1552197/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 333, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 333, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 332, cos780o2c k) + cos780o2c 333 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 332) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_332
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 333 - ((-249049/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_333).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_334 : ((7606441/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 334, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 334, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 333, cos780o2c k) + cos780o2c 334 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 333) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_333
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 334 - ((-77247/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_334).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_335 : ((15965259/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 335, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 335, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 334, cos780o2c k) + cos780o2c 335 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 334) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_334
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 335 - ((752477/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_335).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_336 : ((3373687/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 336, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 336, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 335, cos780o2c k) + cos780o2c 336 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 335) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_335
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 336 - ((225819/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_336).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_337 : ((8418341/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 337, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 337, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 336, cos780o2c k) + cos780o2c 337 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 336) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_336
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 337 - ((-31653/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_337).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_338 : ((15909261/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 338, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 338, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 337, cos780o2c k) + cos780o2c 338 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 337) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_337
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 338 - ((-927321/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_338).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_339 : ((3038051/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 339, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 339, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 338, cos780o2c k) + cos780o2c 339 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 338) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_338
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 339 - ((-359453/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_339).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_340 : ((15529781/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 340, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 340, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 339, cos780o2c k) + cos780o2c 340 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 339) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_339
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 340 - ((169813/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_340).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_341 : ((2065821/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 341, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 341, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 340, cos780o2c k) + cos780o2c 341 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 340) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_340
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 341 - ((996887/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_341).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_342 : ((1063289/62500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 342, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 342, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 341, cos780o2c k) + cos780o2c 342 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 341) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_341
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 342 - ((121539/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_342).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_343 : ((16422573/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 343, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 343, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 342, cos780o2c k) + cos780o2c 343 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 342) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_342
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 343 - ((-589951/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_343).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_344 : ((241274/15625 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 344, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 344, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 343, cos780o2c k) + cos780o2c 344 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 343) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_343
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 344 - ((-980937/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_344).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_345 : ((1520069/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 345, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 345, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 344, cos780o2c k) + cos780o2c 345 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 344) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_344
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 345 - ((-120373/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_345).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_346 : ((249608/15625 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 346, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 346, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 345, cos780o2c k) + cos780o2c 346 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 345) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_345
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 346 - ((387161/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_346).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_347 : ((16879399/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 347, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 347, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 346, cos780o2c k) + cos780o2c 347 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 346) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_346
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 347 - ((904587/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_347).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_348 : ((8443703/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 348, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 348, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 347, cos780o2c k) + cos780o2c 348 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 347) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_347
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 348 - ((8107/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_348).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_349 : ((3997791/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 349, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 349, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 348, cos780o2c k) + cos780o2c 349 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 348) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_348
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 349 - ((-448071/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_349).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_350 : ((3799667/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 350, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 350, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 349, cos780o2c k) + cos780o2c 350 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 349) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_349
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 350 - ((-198099/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_350).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_351 : ((15395259/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 351, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 351, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 350, cos780o2c k) + cos780o2c 351 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 350) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_350
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 351 - ((196691/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_351).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_352 : ((3272139/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 352, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 352, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 351, cos780o2c k) + cos780o2c 352 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 351) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_351
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 352 - ((30173/31250 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_352).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_353 : ((3405151/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 353, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 353, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 352, cos780o2c k) + cos780o2c 353 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 352) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_352
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 353 - ((16629/25000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_353).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_354 : ((16658859/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 354, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 354, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 353, cos780o2c k) + cos780o2c 354 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 353) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_353
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 354 - ((-91699/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_354).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_355 : ((195791/12500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 355, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 355, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 354, cos780o2c k) + cos780o2c 355 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 354) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_354
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 355 - ((-995479/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_355).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_356 : ((7562259/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 356, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 356, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 355, cos780o2c k) + cos780o2c 356 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 355) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_355
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 356 - ((-269331/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_356).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_357 : ((15625719/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 357, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 357, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 356, cos780o2c k) + cos780o2c 357 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 356) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_356
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 357 - ((501301/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_357).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_358 : ((16624597/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 358, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 358, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 357, cos780o2c k) + cos780o2c 358 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 357) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_357
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 358 - ((499489/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_358).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_359 : ((1704837/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 359, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 359, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 358, cos780o2c k) + cos780o2c 359 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 358) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_358
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 359 - ((423873/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_359).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_360 : ((8222679/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 360, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 360, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 359, cos780o2c k) + cos780o2c 360 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 359) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_359
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 360 - ((-18841/31250 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_360).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_361 : ((15457741/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 361, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 361, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 360, cos780o2c k) + cos780o2c 361 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 360) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_360
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 361 - ((-987517/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_361).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_362 : ((3026007/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 362, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 362, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 361, cos780o2c k) + cos780o2c 362 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 361) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_361
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 362 - ((-163803/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_362).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_363 : ((7902881/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 363, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 363, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 362, cos780o2c k) + cos780o2c 363 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 362) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_362
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 363 - ((675827/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_363).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_364 : ((8387999/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 364, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 364, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 363, cos780o2c k) + cos780o2c 364 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 363) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_363
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 364 - ((30323/31250 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_364).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_365 : ((8514871/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 365, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 365, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 364, cos780o2c k) + cos780o2c 365 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 364) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_364
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 365 - ((63461/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_365).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_366 : ((254767/15625 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 366, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 366, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 365, cos780o2c k) + cos780o2c 366 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 365) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_365
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 366 - ((-362277/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_366).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_367 : ((15350753/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 367, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 367, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 366, cos780o2c k) + cos780o2c 367 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 366) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_366
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 367 - ((-190847/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_367).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_368 : ((15146243/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 368, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 368, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 367, cos780o2c k) + cos780o2c 368 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 367) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_367
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 368 - ((-20441/100000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_368).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_369 : ((15899059/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 369, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 369, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 368, cos780o2c k) + cos780o2c 369 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 368) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_368
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 369 - ((188229/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_369).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_370 : ((336853/20000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 370, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 370, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 369, cos780o2c k) + cos780o2c 370 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 369) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_369
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 370 - ((943691/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_370).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_371 : ((2127821/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 371, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 371, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 370, cos780o2c k) + cos780o2c 371 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 370) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_370
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 371 - ((90009/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_371).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_372 : ((3251783/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 372, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 372, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 371, cos780o2c k) + cos780o2c 372 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 371) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_371
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 372 - ((-763553/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_372).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_373 : ((7658869/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 373, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 373, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 372, cos780o2c k) + cos780o2c 373 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 372) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_372
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 373 - ((-941077/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_373).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_374 : ((15136981/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 374, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 374, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 373, cos780o2c k) + cos780o2c 374 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 373) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_373
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 374 - ((-180657/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_374).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_375 : ((15894569/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 375, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 375, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 374, cos780o2c k) + cos780o2c 375 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 374) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_374
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 375 - ((94711/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_375).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_376 : ((8420647/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 376, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 376, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 375, cos780o2c k) + cos780o2c 376 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 375) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_375
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 376 - ((37873/40000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_376).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_377 : ((17047091/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 377, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 377, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 376, cos780o2c k) + cos780o2c 377 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 376) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_376
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 377 - ((205897/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_377).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_378 : ((16311949/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 378, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 378, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 377, cos780o2c k) + cos780o2c 378 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 377) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_377
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 378 - ((-367521/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_378).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_379 : ((7676143/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 379, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 379, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 378, cos780o2c k) + cos780o2c 379 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 378) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_378
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 379 - ((-959563/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_379).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_380 : ((15097237/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 380, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 380, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 379, cos780o2c k) + cos780o2c 380 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 379) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_379
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 380 - ((-254949/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_380).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_381 : ((7895617/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 381, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 381, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 380, cos780o2c k) + cos780o2c 381 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 380) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_380
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 381 - ((694097/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_381).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_382 : ((419183/25000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 382, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 382, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 381, cos780o2c k) + cos780o2c 382 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 381) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_381
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 382 - ((488093/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_382).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_383 : ((17093669/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 383, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 383, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 382, cos780o2c k) + cos780o2c 383 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 382) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_382
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 383 - ((326449/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_383).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_384 : ((8230673/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 384, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 384, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 383, cos780o2c k) + cos780o2c 384 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 383) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_383
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 384 - ((-632223/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_384).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_385 : ((15469419/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 385, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 385, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 384, cos780o2c k) + cos780o2c 385 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 384) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_384
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 385 - ((-991827/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_385).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_386 : ((15051357/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 386, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 386, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 385, cos780o2c k) + cos780o2c 386 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 385) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_385
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 386 - ((-208981/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_386).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_387 : ((7798739/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 387, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 387, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 386, cos780o2c k) + cos780o2c 387 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 386) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_386
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 387 - ((546221/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_387).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_388 : ((16597287/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 388, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 388, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 387, cos780o2c k) + cos780o2c 388 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 387) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_387
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 388 - ((999909/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_388).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_389 : ((17122781/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 389, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 389, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 388, cos780o2c k) + cos780o2c 389 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 388) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_388
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 389 - ((262797/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_389).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_390 : ((521551/31250 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 390, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 390, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 389, cos780o2c k) + cos780o2c 390 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 389) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_389
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 390 - ((-433049/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_390).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_391 : ((3924309/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 391, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 391, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 390, cos780o2c k) + cos780o2c 391 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 390) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_390
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 391 - ((-124037/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_391).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_392 : ((15053813/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 392, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 392, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 391, cos780o2c k) + cos780o2c 392 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 391) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_391
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 392 - ((-643323/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_392).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_393 : ((959017/62500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 393, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 393, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 392, cos780o2c k) + cos780o2c 393 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 392) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_392
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 393 - ((290559/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_393).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_394 : ((4075967/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 394, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 394, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 393, cos780o2c k) + cos780o2c 394 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 393) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_393
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 394 - ((59981/62500 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_394).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_395 : ((682649/40000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 395, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 395, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 394, cos780o2c k) + cos780o2c 395 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 394) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_394
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 395 - ((762457/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_395).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_396 : ((8473697/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 396, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 396, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 395, cos780o2c k) + cos780o2c 396 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 395) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_395
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 396 - ((-118731/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_396).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_397 : ((8027457/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 397, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 397, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 396, cos780o2c k) + cos780o2c 397 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 396) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_396
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 397 - ((-44619/50000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_397).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_398 : ((15183517/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 398, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 398, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 397, cos780o2c k) + cos780o2c 398 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 397) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_397
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 398 - ((-871297/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_398).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_399 : ((15104327/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 399, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 399, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 398, cos780o2c k) + cos780o2c 399 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 398) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_398
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 399 - ((-7909/100000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_399).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_400 : ((3971427/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 400, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 400, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 399, cos780o2c k) + cos780o2c 400 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 399) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_399
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 400 - ((781481/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_400).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_401 : ((3368187/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 401, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 401, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 400, cos780o2c k) + cos780o2c 401 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 400) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_400
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 401 - ((955327/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_401).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_402 : ((4283953/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 402, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 402, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 401, cos780o2c k) + cos780o2c 402 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 401) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_401
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 402 - ((294977/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_402).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_403 : ((16515099/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 403, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 403, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 402, cos780o2c k) + cos780o2c 403 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 402) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_402
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 403 - ((-620613/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_403).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_404 : ((1939641/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 404, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 404, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 403, cos780o2c k) + cos780o2c 404 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 403) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_403
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 404 - ((-997871/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_404).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_405 : ((7500857/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 405, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 405, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 404, cos780o2c k) + cos780o2c 405 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 404) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_404
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 405 - ((-257657/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_405).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_406 : ((963109/62500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 406, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 406, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 405, cos780o2c k) + cos780o2c 406 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 405) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_405
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 406 - ((40813/100000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_406).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_407 : ((16391461/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 407, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 407, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 406, cos780o2c k) + cos780o2c 407 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 406) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_406
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 407 - ((981817/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_407).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_408 : ((17112003/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 408, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 408, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 407, cos780o2c k) + cos780o2c 408 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 407) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_407
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 408 - ((360321/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_408).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_409 : ((2120309/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 409, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 409, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 408, cos780o2c k) + cos780o2c 409 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 408) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_408
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 409 - ((-149431/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_409).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_410 : ((16070091/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 410, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 410, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 409, cos780o2c k) + cos780o2c 410 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 409) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_409
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 410 - ((-892281/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_410).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_411 : ((7591881/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 411, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 411, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 410, cos780o2c k) + cos780o2c 411 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 410) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_410
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 411 - ((-886229/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_411).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_412 : ((15042731/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 412, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 412, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 411, cos780o2c k) + cos780o2c 412 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 411) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_411
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 412 - ((-140931/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_412).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_413 : ((15762793/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 413, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 413, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 412, cos780o2c k) + cos780o2c 413 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 412) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_412
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 413 - ((360081/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_413).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_414 : ((4186793/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 414, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 414, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 413, cos780o2c k) + cos780o2c 414 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 413) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_413
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 414 - ((984479/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_414).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_415 : ((17185157/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 415, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 415, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 414, cos780o2c k) + cos780o2c 415 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 414) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_414
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 415 - ((87617/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_415).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_416 : ((16718719/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 416, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 416, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 415, cos780o2c k) + cos780o2c 416 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 415) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_415
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 416 - ((-233169/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_416).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_417 : ((7864869/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 417, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 417, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 416, cos780o2c k) + cos780o2c 417 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 416) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_416
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 417 - ((-988881/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_417).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_418 : ((3755539/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 418, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 418, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 417, cos780o2c k) + cos780o2c 418 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 417) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_417
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 418 - ((-353741/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_418).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_419 : ((3033503/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 419, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 419, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 418, cos780o2c k) + cos780o2c 419 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 418) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_418
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 419 - ((145459/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_419).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_420 : ((8023659/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 420, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 420, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 419, cos780o2c k) + cos780o2c 420 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 419) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_419
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 420 - ((879903/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_420).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_421 : ((8477607/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 421, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 421, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 420, cos780o2c k) + cos780o2c 421 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 420) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_420
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 421 - ((226999/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_421).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_422 : ((8583351/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 422, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 422, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 421, cos780o2c k) + cos780o2c 422 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 421) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_421
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 422 - ((52897/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_422).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_423 : ((51609/3125 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 423, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 423, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 422, cos780o2c k) + cos780o2c 423 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 422) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_422
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 423 - ((-325861/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_423).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_424 : ((15516577/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 424, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 424, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 423, cos780o2c k) + cos780o2c 424 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 423) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_423
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 424 - ((-998203/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_424).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_425 : ((3739591/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 425, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 425, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 424, cos780o2c k) + cos780o2c 425 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 424) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_424
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 425 - ((-558113/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_425).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_426 : ((3819267/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 426, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 426, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 425, cos780o2c k) + cos780o2c 426 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 425) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_425
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 426 - ((79701/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_426).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_427 : ((8111197/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 427, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 427, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 426, cos780o2c k) + cos780o2c 427 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 426) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_426
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 427 - ((472713/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_427).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_428 : ((17058563/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 428, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 428, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 427, cos780o2c k) + cos780o2c 428 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 427) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_427
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 428 - ((836269/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_428).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_429 : ((8569319/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 429, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 429, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 428, cos780o2c k) + cos780o2c 429 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 428) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_428
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 429 - ((3207/40000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_429).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_430 : ((1640211/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 430, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 430, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 429, cos780o2c k) + cos780o2c 430 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 429) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_429
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 430 - ((-184107/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_430).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_431 : ((3853811/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 431, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 431, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 430, cos780o2c k) + cos780o2c 431 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 430) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_430
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 431 - ((-493383/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_431).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_432 : ((3733031/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 432, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 432, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 431, cos780o2c k) + cos780o2c 432 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 431) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_431
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 432 - ((-24151/50000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_432).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_433 : ((3829821/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 433, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 433, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 432, cos780o2c k) + cos780o2c 433 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 432) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_432
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 433 - ((19363/50000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_433).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_434 : ((16282019/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 434, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 434, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 433, cos780o2c k) + cos780o2c 434 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 433) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_433
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 434 - ((192567/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_434).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_435 : ((17093409/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 435, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 435, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 434, cos780o2c k) + cos780o2c 435 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 434) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_434
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 435 - ((81149/100000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_435).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_436 : ((8572233/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 436, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 436, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 435, cos780o2c k) + cos780o2c 436 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 435) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_435
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 436 - ((51157/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_436).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_437 : ((16398209/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 437, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 437, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 436, cos780o2c k) + cos780o2c 437 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 436) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_436
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 437 - ((-746157/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_437).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_438 : ((7705677/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 438, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 438, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 437, cos780o2c k) + cos780o2c 438 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 437) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_437
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 438 - ((-197351/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_438).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_439 : ((14915707/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 439, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 439, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 438, cos780o2c k) + cos780o2c 439 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 438) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_438
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 439 - ((-495547/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_439).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_440 : ((15276199/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 440, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 440, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 439, cos780o2c k) + cos780o2c 440 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 439) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_439
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 440 - ((22537/62500 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_440).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_441 : ((16226413/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 441, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 441, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 440, cos780o2c k) + cos780o2c 441 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 440) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_440
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 441 - ((475157/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_441).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_442 : ((17069939/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 442, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 442, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 441, cos780o2c k) + cos780o2c 442 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 441) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_441
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 442 - ((421813/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_442).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_443 : ((4298043/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 443, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 443, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 442, cos780o2c k) + cos780o2c 443 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 442) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_442
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 443 - ((122333/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_443).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_444 : ((16505523/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 444, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 444, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 443, cos780o2c k) + cos780o2c 444 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 443) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_443
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 444 - ((-686549/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_444).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_445 : ((15507427/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 445, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 445, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 444, cos780o2c k) + cos780o2c 445 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 444) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_444
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 445 - ((-249499/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_445).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_446 : ((14916531/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 446, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 446, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 445, cos780o2c k) + cos780o2c 446 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 445) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_445
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 446 - ((-147699/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_446).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_447 : ((15155493/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 447, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 447, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 446, cos780o2c k) + cos780o2c 447 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 446) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_446
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 447 - ((119531/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_447).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_448 : ((2006549/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 448, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 448, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 447, cos780o2c k) + cos780o2c 448 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 447) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_447
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 448 - ((896999/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_448).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_449 : ((8484371/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 449, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 449, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 448, cos780o2c k) + cos780o2c 449 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 448) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_448
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 449 - ((18329/20000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_449).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_450 : ((3451203/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 450, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 450, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 449, cos780o2c k) + cos780o2c 450 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 449) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_449
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 450 - ((287373/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_450).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_451 : ((16712719/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 451, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 451, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 450, cos780o2c k) + cos780o2c 451 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 450) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_450
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 451 - ((-135799/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_451).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_452 : ((7860711/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 452, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 452, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 451, cos780o2c k) + cos780o2c 452 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 451) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_451
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 452 - ((-991197/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_452).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_453 : ((14975557/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 453, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 453, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 452, cos780o2c k) + cos780o2c 453 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 452) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_452
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 453 - ((-149153/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_453).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_454 : ((3748431/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 454, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 454, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 453, cos780o2c k) + cos780o2c 454 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 453) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_453
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 454 - ((18267/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_454).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_455 : ((3152411/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 455, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 455, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 454, cos780o2c k) + cos780o2c 455 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 454) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_454
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 455 - ((768431/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_455).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_456 : ((3349779/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 456, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 456, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 455, cos780o2c k) + cos780o2c 456 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 455) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_455
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 456 - ((49347/50000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_456).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_457 : ((17275489/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 457, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 457, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 456, cos780o2c k) + cos780o2c 457 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 456) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_456
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 457 - ((263347/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_457).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_458 : ((8491007/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 458, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 458, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 457, cos780o2c k) + cos780o2c 458 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 457) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_457
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 458 - ((-2347/8000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_458).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_459 : ((16069811/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 459, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 459, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 458, cos780o2c k) + cos780o2c 459 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 458) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_458
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 459 - ((-912103/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_459).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_460 : ((3789803/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 460, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 460, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 459, cos780o2c k) + cos780o2c 460 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 459) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_459
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 460 - ((-910499/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_460).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_461 : ((7432959/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 461, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 461, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 460, cos780o2c k) + cos780o2c 461 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 460) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_460
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 461 - ((-146597/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_461).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_462 : ((384659/25000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 462, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 462, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 461, cos780o2c k) + cos780o2c 462 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 461) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_461
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 462 - ((260271/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_462).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_463 : ((8185047/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 463, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 463, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 462, cos780o2c k) + cos780o2c 463 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 462) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_462
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 463 - ((491917/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_463).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_464 : ((2144893/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 464, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 464, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 463, cos780o2c k) + cos780o2c 464 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 463) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_463
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 464 - ((15783/20000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_464).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_465 : ((861439/50000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 465, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 465, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 464, cos780o2c k) + cos780o2c 465 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 464) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_464
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 465 - ((8717/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_465).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_466 : ((8266989/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 466, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 466, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 465, cos780o2c k) + cos780o2c 466 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 465) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_465
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 466 - ((-347351/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_466).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_467 : ((15534429/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 467, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 467, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 466, cos780o2c k) + cos780o2c 467 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 466) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_466
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 467 - ((-999449/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_467).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_468 : ((2977507/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 468, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 468, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 467, cos780o2c k) + cos780o2c 468 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 467) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_467
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 468 - ((-323397/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_468).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_469 : ((7508079/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 469, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 469, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 468, cos780o2c k) + cos780o2c 469 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 468) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_468
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 469 - ((128723/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_469).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_470 : ((7917551/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 470, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 470, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 469, cos780o2c k) + cos780o2c 470 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 469) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_469
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 470 - ((204761/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_470).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_471 : ((8405683/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 471, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 471, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 470, cos780o2c k) + cos780o2c 471 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 470) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_470
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 471 - ((244091/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_471).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_472 : ((3462633/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 472, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 472, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 471, cos780o2c k) + cos780o2c 472 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 471) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_471
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 472 - ((501899/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_472).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_473 : ((4254481/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 473, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 473, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 472, cos780o2c k) + cos780o2c 473 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 472) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_472
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 473 - ((-295141/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_473).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_474 : ((8058149/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 474, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 474, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 473, cos780o2c k) + cos780o2c 474 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 473) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_473
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 474 - ((-450763/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_474).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_475 : ((607419/40000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 475, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 475, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 474, cos780o2c k) + cos780o2c 475 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 474) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_474
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 475 - ((-930723/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_475).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_476 : ((3704493/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 476, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 476, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 475, cos780o2c k) + cos780o2c 476 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 475) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_475
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 476 - ((-367403/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_476).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_477 : ((3811459/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 477, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 477, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 476, cos780o2c k) + cos780o2c 477 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 476) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_476
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 477 - ((106991/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_477).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_478 : ((647901/40000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 478, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 478, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 477, cos780o2c k) + cos780o2c 478 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 477) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_477
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 478 - ((951789/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_478).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_479 : ((17073449/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 479, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 479, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 478, cos780o2c k) + cos780o2c 479 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 478) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_478
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 479 - ((109503/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_479).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_480 : ((17324791/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 480, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 480, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 479, cos780o2c k) + cos780o2c 480 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 479) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_479
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 480 - ((125721/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_480).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_481 : ((839783/50000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 481, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 481, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 480, cos780o2c k) + cos780o2c 481 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 480) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_480
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 481 - ((-529031/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_481).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_482 : ((3954041/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 482, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 482, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 481, cos780o2c k) + cos780o2c 482 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 481) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_481
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 482 - ((-244849/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_482).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_483 : ((14993521/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 483, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 483, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 482, cos780o2c k) + cos780o2c 483 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 482) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_482
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 483 - ((-822543/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_483).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_484 : ((7417431/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 484, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 484, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 483, cos780o2c k) + cos780o2c 484 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 483) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_483
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 484 - ((-158559/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_484).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_485 : ((482391/31250 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 485, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 485, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 484, cos780o2c k) + cos780o2c 485 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 484) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_484
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 485 - ((2407/4000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_485).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_486 : ((3285801/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 486, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 486, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 485, cos780o2c k) + cos780o2c 486 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 485) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_485
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 486 - ((992593/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_486).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_487 : ((3441313/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 487, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 487, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 486, cos780o2c k) + cos780o2c 487 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 486) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_486
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 487 - ((38883/50000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_487).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_488 : ((4324317/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 488, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 488, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 487, cos780o2c k) + cos780o2c 488 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 487) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_487
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 488 - ((90803/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_488).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_489 : ((16647307/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 489, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 489, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 488, cos780o2c k) + cos780o2c 489 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 488) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_488
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 489 - ((-649861/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_489).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_490 : ((3912357/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 490, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 490, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 489, cos780o2c k) + cos780o2c 490 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 489) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_489
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 490 - ((-997779/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_490).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_491 : ((14903133/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 491, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 491, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 490, cos780o2c k) + cos780o2c 491 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 490) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_490
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 491 - ((-149239/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_491).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_492 : ((7427109/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 492, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 492, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 491, cos780o2c k) + cos780o2c 492 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 491) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_491
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 492 - ((-9763/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_492).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_493 : ((7765317/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 493, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 493, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 492, cos780o2c k) + cos780o2c 493 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 492) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_492
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 493 - ((169129/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_493).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_494 : ((2066229/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 494, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 494, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 493, cos780o2c k) + cos780o2c 494 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 493) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_493
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 494 - ((499649/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_494).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_495 : ((17260617/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 495, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 495, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 494, cos780o2c k) + cos780o2c 495 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 494) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_494
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 495 - ((146177/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_495).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_496 : ((1729303/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 496, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 496, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 495, cos780o2c k) + cos780o2c 496 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 495) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_495
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 496 - ((32513/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_496).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_497 : ((8304557/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 497, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 497, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 496, cos780o2c k) + cos780o2c 497 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 496) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_496
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 497 - ((-85477/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_497).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_498 : ((15609589/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 498, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 498, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 497, cos780o2c k) + cos780o2c 498 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 497) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_497
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 498 - ((-39977/40000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_498).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_499 : ((7438363/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 499, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 499, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 498, cos780o2c k) + cos780o2c 499 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 498) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_498
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 499 - ((-732763/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_499).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum780o2_500 : ((2967009/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 500, cos780o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 500, cos780o2c k)
      = (∑ k ∈ Finset.Icc 11 499, cos780o2c k) + cos780o2c 500 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 499) (by norm_num) cos780o2c
    simpa using h
  have hprev := psum780o2_499
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos780o2c 500 - ((-41581/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos780o2_br_500).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

set_option maxHeartbeats 6400000 in
set_option maxRecDepth 16384 in
theorem psum780o2_floor : ∀ j : ℕ, 11 ≤ j → j ≤ 500 →
    ((0 : ℚ) : ℝ) ≤ ∑ k ∈ Finset.Icc 11 j, cos780o2c k := by
  intro j hj1 hj2
  interval_cases j
  · exact le_trans (by norm_num) psum780o2_11
  · exact le_trans (by norm_num) psum780o2_12
  · exact le_trans (by norm_num) psum780o2_13
  · exact le_trans (by norm_num) psum780o2_14
  · exact le_trans (by norm_num) psum780o2_15
  · exact le_trans (by norm_num) psum780o2_16
  · exact le_trans (by norm_num) psum780o2_17
  · exact le_trans (by norm_num) psum780o2_18
  · exact le_trans (by norm_num) psum780o2_19
  · exact le_trans (by norm_num) psum780o2_20
  · exact le_trans (by norm_num) psum780o2_21
  · exact le_trans (by norm_num) psum780o2_22
  · exact le_trans (by norm_num) psum780o2_23
  · exact le_trans (by norm_num) psum780o2_24
  · exact le_trans (by norm_num) psum780o2_25
  · exact le_trans (by norm_num) psum780o2_26
  · exact le_trans (by norm_num) psum780o2_27
  · exact le_trans (by norm_num) psum780o2_28
  · exact le_trans (by norm_num) psum780o2_29
  · exact le_trans (by norm_num) psum780o2_30
  · exact le_trans (by norm_num) psum780o2_31
  · exact le_trans (by norm_num) psum780o2_32
  · exact le_trans (by norm_num) psum780o2_33
  · exact le_trans (by norm_num) psum780o2_34
  · exact le_trans (by norm_num) psum780o2_35
  · exact le_trans (by norm_num) psum780o2_36
  · exact le_trans (by norm_num) psum780o2_37
  · exact le_trans (by norm_num) psum780o2_38
  · exact le_trans (by norm_num) psum780o2_39
  · exact le_trans (by norm_num) psum780o2_40
  · exact le_trans (by norm_num) psum780o2_41
  · exact le_trans (by norm_num) psum780o2_42
  · exact le_trans (by norm_num) psum780o2_43
  · exact le_trans (by norm_num) psum780o2_44
  · exact le_trans (by norm_num) psum780o2_45
  · exact le_trans (by norm_num) psum780o2_46
  · exact le_trans (by norm_num) psum780o2_47
  · exact le_trans (by norm_num) psum780o2_48
  · exact le_trans (by norm_num) psum780o2_49
  · exact le_trans (by norm_num) psum780o2_50
  · exact le_trans (by norm_num) psum780o2_51
  · exact le_trans (by norm_num) psum780o2_52
  · exact le_trans (by norm_num) psum780o2_53
  · exact le_trans (by norm_num) psum780o2_54
  · exact le_trans (by norm_num) psum780o2_55
  · exact le_trans (by norm_num) psum780o2_56
  · exact le_trans (by norm_num) psum780o2_57
  · exact le_trans (by norm_num) psum780o2_58
  · exact le_trans (by norm_num) psum780o2_59
  · exact le_trans (by norm_num) psum780o2_60
  · exact le_trans (by norm_num) psum780o2_61
  · exact le_trans (by norm_num) psum780o2_62
  · exact le_trans (by norm_num) psum780o2_63
  · exact le_trans (by norm_num) psum780o2_64
  · exact le_trans (by norm_num) psum780o2_65
  · exact le_trans (by norm_num) psum780o2_66
  · exact le_trans (by norm_num) psum780o2_67
  · exact le_trans (by norm_num) psum780o2_68
  · exact le_trans (by norm_num) psum780o2_69
  · exact le_trans (by norm_num) psum780o2_70
  · exact le_trans (by norm_num) psum780o2_71
  · exact le_trans (by norm_num) psum780o2_72
  · exact le_trans (by norm_num) psum780o2_73
  · exact le_trans (by norm_num) psum780o2_74
  · exact le_trans (by norm_num) psum780o2_75
  · exact le_trans (by norm_num) psum780o2_76
  · exact le_trans (by norm_num) psum780o2_77
  · exact le_trans (by norm_num) psum780o2_78
  · exact le_trans (by norm_num) psum780o2_79
  · exact le_trans (by norm_num) psum780o2_80
  · exact le_trans (by norm_num) psum780o2_81
  · exact le_trans (by norm_num) psum780o2_82
  · exact le_trans (by norm_num) psum780o2_83
  · exact le_trans (by norm_num) psum780o2_84
  · exact le_trans (by norm_num) psum780o2_85
  · exact le_trans (by norm_num) psum780o2_86
  · exact le_trans (by norm_num) psum780o2_87
  · exact le_trans (by norm_num) psum780o2_88
  · exact le_trans (by norm_num) psum780o2_89
  · exact le_trans (by norm_num) psum780o2_90
  · exact le_trans (by norm_num) psum780o2_91
  · exact le_trans (by norm_num) psum780o2_92
  · exact le_trans (by norm_num) psum780o2_93
  · exact le_trans (by norm_num) psum780o2_94
  · exact le_trans (by norm_num) psum780o2_95
  · exact le_trans (by norm_num) psum780o2_96
  · exact le_trans (by norm_num) psum780o2_97
  · exact le_trans (by norm_num) psum780o2_98
  · exact le_trans (by norm_num) psum780o2_99
  · exact le_trans (by norm_num) psum780o2_100
  · exact le_trans (by norm_num) psum780o2_101
  · exact le_trans (by norm_num) psum780o2_102
  · exact le_trans (by norm_num) psum780o2_103
  · exact le_trans (by norm_num) psum780o2_104
  · exact le_trans (by norm_num) psum780o2_105
  · exact le_trans (by norm_num) psum780o2_106
  · exact le_trans (by norm_num) psum780o2_107
  · exact le_trans (by norm_num) psum780o2_108
  · exact le_trans (by norm_num) psum780o2_109
  · exact le_trans (by norm_num) psum780o2_110
  · exact le_trans (by norm_num) psum780o2_111
  · exact le_trans (by norm_num) psum780o2_112
  · exact le_trans (by norm_num) psum780o2_113
  · exact le_trans (by norm_num) psum780o2_114
  · exact le_trans (by norm_num) psum780o2_115
  · exact le_trans (by norm_num) psum780o2_116
  · exact le_trans (by norm_num) psum780o2_117
  · exact le_trans (by norm_num) psum780o2_118
  · exact le_trans (by norm_num) psum780o2_119
  · exact le_trans (by norm_num) psum780o2_120
  · exact le_trans (by norm_num) psum780o2_121
  · exact le_trans (by norm_num) psum780o2_122
  · exact le_trans (by norm_num) psum780o2_123
  · exact le_trans (by norm_num) psum780o2_124
  · exact le_trans (by norm_num) psum780o2_125
  · exact le_trans (by norm_num) psum780o2_126
  · exact le_trans (by norm_num) psum780o2_127
  · exact le_trans (by norm_num) psum780o2_128
  · exact le_trans (by norm_num) psum780o2_129
  · exact le_trans (by norm_num) psum780o2_130
  · exact le_trans (by norm_num) psum780o2_131
  · exact le_trans (by norm_num) psum780o2_132
  · exact le_trans (by norm_num) psum780o2_133
  · exact le_trans (by norm_num) psum780o2_134
  · exact le_trans (by norm_num) psum780o2_135
  · exact le_trans (by norm_num) psum780o2_136
  · exact le_trans (by norm_num) psum780o2_137
  · exact le_trans (by norm_num) psum780o2_138
  · exact le_trans (by norm_num) psum780o2_139
  · exact le_trans (by norm_num) psum780o2_140
  · exact le_trans (by norm_num) psum780o2_141
  · exact le_trans (by norm_num) psum780o2_142
  · exact le_trans (by norm_num) psum780o2_143
  · exact le_trans (by norm_num) psum780o2_144
  · exact le_trans (by norm_num) psum780o2_145
  · exact le_trans (by norm_num) psum780o2_146
  · exact le_trans (by norm_num) psum780o2_147
  · exact le_trans (by norm_num) psum780o2_148
  · exact le_trans (by norm_num) psum780o2_149
  · exact le_trans (by norm_num) psum780o2_150
  · exact le_trans (by norm_num) psum780o2_151
  · exact le_trans (by norm_num) psum780o2_152
  · exact le_trans (by norm_num) psum780o2_153
  · exact le_trans (by norm_num) psum780o2_154
  · exact le_trans (by norm_num) psum780o2_155
  · exact le_trans (by norm_num) psum780o2_156
  · exact le_trans (by norm_num) psum780o2_157
  · exact le_trans (by norm_num) psum780o2_158
  · exact le_trans (by norm_num) psum780o2_159
  · exact le_trans (by norm_num) psum780o2_160
  · exact le_trans (by norm_num) psum780o2_161
  · exact le_trans (by norm_num) psum780o2_162
  · exact le_trans (by norm_num) psum780o2_163
  · exact le_trans (by norm_num) psum780o2_164
  · exact le_trans (by norm_num) psum780o2_165
  · exact le_trans (by norm_num) psum780o2_166
  · exact le_trans (by norm_num) psum780o2_167
  · exact le_trans (by norm_num) psum780o2_168
  · exact le_trans (by norm_num) psum780o2_169
  · exact le_trans (by norm_num) psum780o2_170
  · exact le_trans (by norm_num) psum780o2_171
  · exact le_trans (by norm_num) psum780o2_172
  · exact le_trans (by norm_num) psum780o2_173
  · exact le_trans (by norm_num) psum780o2_174
  · exact le_trans (by norm_num) psum780o2_175
  · exact le_trans (by norm_num) psum780o2_176
  · exact le_trans (by norm_num) psum780o2_177
  · exact le_trans (by norm_num) psum780o2_178
  · exact le_trans (by norm_num) psum780o2_179
  · exact le_trans (by norm_num) psum780o2_180
  · exact le_trans (by norm_num) psum780o2_181
  · exact le_trans (by norm_num) psum780o2_182
  · exact le_trans (by norm_num) psum780o2_183
  · exact le_trans (by norm_num) psum780o2_184
  · exact le_trans (by norm_num) psum780o2_185
  · exact le_trans (by norm_num) psum780o2_186
  · exact le_trans (by norm_num) psum780o2_187
  · exact le_trans (by norm_num) psum780o2_188
  · exact le_trans (by norm_num) psum780o2_189
  · exact le_trans (by norm_num) psum780o2_190
  · exact le_trans (by norm_num) psum780o2_191
  · exact le_trans (by norm_num) psum780o2_192
  · exact le_trans (by norm_num) psum780o2_193
  · exact le_trans (by norm_num) psum780o2_194
  · exact le_trans (by norm_num) psum780o2_195
  · exact le_trans (by norm_num) psum780o2_196
  · exact le_trans (by norm_num) psum780o2_197
  · exact le_trans (by norm_num) psum780o2_198
  · exact le_trans (by norm_num) psum780o2_199
  · exact le_trans (by norm_num) psum780o2_200
  · exact le_trans (by norm_num) psum780o2_201
  · exact le_trans (by norm_num) psum780o2_202
  · exact le_trans (by norm_num) psum780o2_203
  · exact le_trans (by norm_num) psum780o2_204
  · exact le_trans (by norm_num) psum780o2_205
  · exact le_trans (by norm_num) psum780o2_206
  · exact le_trans (by norm_num) psum780o2_207
  · exact le_trans (by norm_num) psum780o2_208
  · exact le_trans (by norm_num) psum780o2_209
  · exact le_trans (by norm_num) psum780o2_210
  · exact le_trans (by norm_num) psum780o2_211
  · exact le_trans (by norm_num) psum780o2_212
  · exact le_trans (by norm_num) psum780o2_213
  · exact le_trans (by norm_num) psum780o2_214
  · exact le_trans (by norm_num) psum780o2_215
  · exact le_trans (by norm_num) psum780o2_216
  · exact le_trans (by norm_num) psum780o2_217
  · exact le_trans (by norm_num) psum780o2_218
  · exact le_trans (by norm_num) psum780o2_219
  · exact le_trans (by norm_num) psum780o2_220
  · exact le_trans (by norm_num) psum780o2_221
  · exact le_trans (by norm_num) psum780o2_222
  · exact le_trans (by norm_num) psum780o2_223
  · exact le_trans (by norm_num) psum780o2_224
  · exact le_trans (by norm_num) psum780o2_225
  · exact le_trans (by norm_num) psum780o2_226
  · exact le_trans (by norm_num) psum780o2_227
  · exact le_trans (by norm_num) psum780o2_228
  · exact le_trans (by norm_num) psum780o2_229
  · exact le_trans (by norm_num) psum780o2_230
  · exact le_trans (by norm_num) psum780o2_231
  · exact le_trans (by norm_num) psum780o2_232
  · exact le_trans (by norm_num) psum780o2_233
  · exact le_trans (by norm_num) psum780o2_234
  · exact le_trans (by norm_num) psum780o2_235
  · exact le_trans (by norm_num) psum780o2_236
  · exact le_trans (by norm_num) psum780o2_237
  · exact le_trans (by norm_num) psum780o2_238
  · exact le_trans (by norm_num) psum780o2_239
  · exact le_trans (by norm_num) psum780o2_240
  · exact le_trans (by norm_num) psum780o2_241
  · exact le_trans (by norm_num) psum780o2_242
  · exact le_trans (by norm_num) psum780o2_243
  · exact le_trans (by norm_num) psum780o2_244
  · exact le_trans (by norm_num) psum780o2_245
  · exact le_trans (by norm_num) psum780o2_246
  · exact le_trans (by norm_num) psum780o2_247
  · exact le_trans (by norm_num) psum780o2_248
  · exact le_trans (by norm_num) psum780o2_249
  · exact le_trans (by norm_num) psum780o2_250
  · exact le_trans (by norm_num) psum780o2_251
  · exact le_trans (by norm_num) psum780o2_252
  · exact le_trans (by norm_num) psum780o2_253
  · exact le_trans (by norm_num) psum780o2_254
  · exact le_trans (by norm_num) psum780o2_255
  · exact le_trans (by norm_num) psum780o2_256
  · exact le_trans (by norm_num) psum780o2_257
  · exact le_trans (by norm_num) psum780o2_258
  · exact le_trans (by norm_num) psum780o2_259
  · exact le_trans (by norm_num) psum780o2_260
  · exact le_trans (by norm_num) psum780o2_261
  · exact le_trans (by norm_num) psum780o2_262
  · exact le_trans (by norm_num) psum780o2_263
  · exact le_trans (by norm_num) psum780o2_264
  · exact le_trans (by norm_num) psum780o2_265
  · exact le_trans (by norm_num) psum780o2_266
  · exact le_trans (by norm_num) psum780o2_267
  · exact le_trans (by norm_num) psum780o2_268
  · exact le_trans (by norm_num) psum780o2_269
  · exact le_trans (by norm_num) psum780o2_270
  · exact le_trans (by norm_num) psum780o2_271
  · exact le_trans (by norm_num) psum780o2_272
  · exact le_trans (by norm_num) psum780o2_273
  · exact le_trans (by norm_num) psum780o2_274
  · exact le_trans (by norm_num) psum780o2_275
  · exact le_trans (by norm_num) psum780o2_276
  · exact le_trans (by norm_num) psum780o2_277
  · exact le_trans (by norm_num) psum780o2_278
  · exact le_trans (by norm_num) psum780o2_279
  · exact le_trans (by norm_num) psum780o2_280
  · exact le_trans (by norm_num) psum780o2_281
  · exact le_trans (by norm_num) psum780o2_282
  · exact le_trans (by norm_num) psum780o2_283
  · exact le_trans (by norm_num) psum780o2_284
  · exact le_trans (by norm_num) psum780o2_285
  · exact le_trans (by norm_num) psum780o2_286
  · exact le_trans (by norm_num) psum780o2_287
  · exact le_trans (by norm_num) psum780o2_288
  · exact le_trans (by norm_num) psum780o2_289
  · exact le_trans (by norm_num) psum780o2_290
  · exact le_trans (by norm_num) psum780o2_291
  · exact le_trans (by norm_num) psum780o2_292
  · exact le_trans (by norm_num) psum780o2_293
  · exact le_trans (by norm_num) psum780o2_294
  · exact le_trans (by norm_num) psum780o2_295
  · exact le_trans (by norm_num) psum780o2_296
  · exact le_trans (by norm_num) psum780o2_297
  · exact le_trans (by norm_num) psum780o2_298
  · exact le_trans (by norm_num) psum780o2_299
  · exact le_trans (by norm_num) psum780o2_300
  · exact le_trans (by norm_num) psum780o2_301
  · exact le_trans (by norm_num) psum780o2_302
  · exact le_trans (by norm_num) psum780o2_303
  · exact le_trans (by norm_num) psum780o2_304
  · exact le_trans (by norm_num) psum780o2_305
  · exact le_trans (by norm_num) psum780o2_306
  · exact le_trans (by norm_num) psum780o2_307
  · exact le_trans (by norm_num) psum780o2_308
  · exact le_trans (by norm_num) psum780o2_309
  · exact le_trans (by norm_num) psum780o2_310
  · exact le_trans (by norm_num) psum780o2_311
  · exact le_trans (by norm_num) psum780o2_312
  · exact le_trans (by norm_num) psum780o2_313
  · exact le_trans (by norm_num) psum780o2_314
  · exact le_trans (by norm_num) psum780o2_315
  · exact le_trans (by norm_num) psum780o2_316
  · exact le_trans (by norm_num) psum780o2_317
  · exact le_trans (by norm_num) psum780o2_318
  · exact le_trans (by norm_num) psum780o2_319
  · exact le_trans (by norm_num) psum780o2_320
  · exact le_trans (by norm_num) psum780o2_321
  · exact le_trans (by norm_num) psum780o2_322
  · exact le_trans (by norm_num) psum780o2_323
  · exact le_trans (by norm_num) psum780o2_324
  · exact le_trans (by norm_num) psum780o2_325
  · exact le_trans (by norm_num) psum780o2_326
  · exact le_trans (by norm_num) psum780o2_327
  · exact le_trans (by norm_num) psum780o2_328
  · exact le_trans (by norm_num) psum780o2_329
  · exact le_trans (by norm_num) psum780o2_330
  · exact le_trans (by norm_num) psum780o2_331
  · exact le_trans (by norm_num) psum780o2_332
  · exact le_trans (by norm_num) psum780o2_333
  · exact le_trans (by norm_num) psum780o2_334
  · exact le_trans (by norm_num) psum780o2_335
  · exact le_trans (by norm_num) psum780o2_336
  · exact le_trans (by norm_num) psum780o2_337
  · exact le_trans (by norm_num) psum780o2_338
  · exact le_trans (by norm_num) psum780o2_339
  · exact le_trans (by norm_num) psum780o2_340
  · exact le_trans (by norm_num) psum780o2_341
  · exact le_trans (by norm_num) psum780o2_342
  · exact le_trans (by norm_num) psum780o2_343
  · exact le_trans (by norm_num) psum780o2_344
  · exact le_trans (by norm_num) psum780o2_345
  · exact le_trans (by norm_num) psum780o2_346
  · exact le_trans (by norm_num) psum780o2_347
  · exact le_trans (by norm_num) psum780o2_348
  · exact le_trans (by norm_num) psum780o2_349
  · exact le_trans (by norm_num) psum780o2_350
  · exact le_trans (by norm_num) psum780o2_351
  · exact le_trans (by norm_num) psum780o2_352
  · exact le_trans (by norm_num) psum780o2_353
  · exact le_trans (by norm_num) psum780o2_354
  · exact le_trans (by norm_num) psum780o2_355
  · exact le_trans (by norm_num) psum780o2_356
  · exact le_trans (by norm_num) psum780o2_357
  · exact le_trans (by norm_num) psum780o2_358
  · exact le_trans (by norm_num) psum780o2_359
  · exact le_trans (by norm_num) psum780o2_360
  · exact le_trans (by norm_num) psum780o2_361
  · exact le_trans (by norm_num) psum780o2_362
  · exact le_trans (by norm_num) psum780o2_363
  · exact le_trans (by norm_num) psum780o2_364
  · exact le_trans (by norm_num) psum780o2_365
  · exact le_trans (by norm_num) psum780o2_366
  · exact le_trans (by norm_num) psum780o2_367
  · exact le_trans (by norm_num) psum780o2_368
  · exact le_trans (by norm_num) psum780o2_369
  · exact le_trans (by norm_num) psum780o2_370
  · exact le_trans (by norm_num) psum780o2_371
  · exact le_trans (by norm_num) psum780o2_372
  · exact le_trans (by norm_num) psum780o2_373
  · exact le_trans (by norm_num) psum780o2_374
  · exact le_trans (by norm_num) psum780o2_375
  · exact le_trans (by norm_num) psum780o2_376
  · exact le_trans (by norm_num) psum780o2_377
  · exact le_trans (by norm_num) psum780o2_378
  · exact le_trans (by norm_num) psum780o2_379
  · exact le_trans (by norm_num) psum780o2_380
  · exact le_trans (by norm_num) psum780o2_381
  · exact le_trans (by norm_num) psum780o2_382
  · exact le_trans (by norm_num) psum780o2_383
  · exact le_trans (by norm_num) psum780o2_384
  · exact le_trans (by norm_num) psum780o2_385
  · exact le_trans (by norm_num) psum780o2_386
  · exact le_trans (by norm_num) psum780o2_387
  · exact le_trans (by norm_num) psum780o2_388
  · exact le_trans (by norm_num) psum780o2_389
  · exact le_trans (by norm_num) psum780o2_390
  · exact le_trans (by norm_num) psum780o2_391
  · exact le_trans (by norm_num) psum780o2_392
  · exact le_trans (by norm_num) psum780o2_393
  · exact le_trans (by norm_num) psum780o2_394
  · exact le_trans (by norm_num) psum780o2_395
  · exact le_trans (by norm_num) psum780o2_396
  · exact le_trans (by norm_num) psum780o2_397
  · exact le_trans (by norm_num) psum780o2_398
  · exact le_trans (by norm_num) psum780o2_399
  · exact le_trans (by norm_num) psum780o2_400
  · exact le_trans (by norm_num) psum780o2_401
  · exact le_trans (by norm_num) psum780o2_402
  · exact le_trans (by norm_num) psum780o2_403
  · exact le_trans (by norm_num) psum780o2_404
  · exact le_trans (by norm_num) psum780o2_405
  · exact le_trans (by norm_num) psum780o2_406
  · exact le_trans (by norm_num) psum780o2_407
  · exact le_trans (by norm_num) psum780o2_408
  · exact le_trans (by norm_num) psum780o2_409
  · exact le_trans (by norm_num) psum780o2_410
  · exact le_trans (by norm_num) psum780o2_411
  · exact le_trans (by norm_num) psum780o2_412
  · exact le_trans (by norm_num) psum780o2_413
  · exact le_trans (by norm_num) psum780o2_414
  · exact le_trans (by norm_num) psum780o2_415
  · exact le_trans (by norm_num) psum780o2_416
  · exact le_trans (by norm_num) psum780o2_417
  · exact le_trans (by norm_num) psum780o2_418
  · exact le_trans (by norm_num) psum780o2_419
  · exact le_trans (by norm_num) psum780o2_420
  · exact le_trans (by norm_num) psum780o2_421
  · exact le_trans (by norm_num) psum780o2_422
  · exact le_trans (by norm_num) psum780o2_423
  · exact le_trans (by norm_num) psum780o2_424
  · exact le_trans (by norm_num) psum780o2_425
  · exact le_trans (by norm_num) psum780o2_426
  · exact le_trans (by norm_num) psum780o2_427
  · exact le_trans (by norm_num) psum780o2_428
  · exact le_trans (by norm_num) psum780o2_429
  · exact le_trans (by norm_num) psum780o2_430
  · exact le_trans (by norm_num) psum780o2_431
  · exact le_trans (by norm_num) psum780o2_432
  · exact le_trans (by norm_num) psum780o2_433
  · exact le_trans (by norm_num) psum780o2_434
  · exact le_trans (by norm_num) psum780o2_435
  · exact le_trans (by norm_num) psum780o2_436
  · exact le_trans (by norm_num) psum780o2_437
  · exact le_trans (by norm_num) psum780o2_438
  · exact le_trans (by norm_num) psum780o2_439
  · exact le_trans (by norm_num) psum780o2_440
  · exact le_trans (by norm_num) psum780o2_441
  · exact le_trans (by norm_num) psum780o2_442
  · exact le_trans (by norm_num) psum780o2_443
  · exact le_trans (by norm_num) psum780o2_444
  · exact le_trans (by norm_num) psum780o2_445
  · exact le_trans (by norm_num) psum780o2_446
  · exact le_trans (by norm_num) psum780o2_447
  · exact le_trans (by norm_num) psum780o2_448
  · exact le_trans (by norm_num) psum780o2_449
  · exact le_trans (by norm_num) psum780o2_450
  · exact le_trans (by norm_num) psum780o2_451
  · exact le_trans (by norm_num) psum780o2_452
  · exact le_trans (by norm_num) psum780o2_453
  · exact le_trans (by norm_num) psum780o2_454
  · exact le_trans (by norm_num) psum780o2_455
  · exact le_trans (by norm_num) psum780o2_456
  · exact le_trans (by norm_num) psum780o2_457
  · exact le_trans (by norm_num) psum780o2_458
  · exact le_trans (by norm_num) psum780o2_459
  · exact le_trans (by norm_num) psum780o2_460
  · exact le_trans (by norm_num) psum780o2_461
  · exact le_trans (by norm_num) psum780o2_462
  · exact le_trans (by norm_num) psum780o2_463
  · exact le_trans (by norm_num) psum780o2_464
  · exact le_trans (by norm_num) psum780o2_465
  · exact le_trans (by norm_num) psum780o2_466
  · exact le_trans (by norm_num) psum780o2_467
  · exact le_trans (by norm_num) psum780o2_468
  · exact le_trans (by norm_num) psum780o2_469
  · exact le_trans (by norm_num) psum780o2_470
  · exact le_trans (by norm_num) psum780o2_471
  · exact le_trans (by norm_num) psum780o2_472
  · exact le_trans (by norm_num) psum780o2_473
  · exact le_trans (by norm_num) psum780o2_474
  · exact le_trans (by norm_num) psum780o2_475
  · exact le_trans (by norm_num) psum780o2_476
  · exact le_trans (by norm_num) psum780o2_477
  · exact le_trans (by norm_num) psum780o2_478
  · exact le_trans (by norm_num) psum780o2_479
  · exact le_trans (by norm_num) psum780o2_480
  · exact le_trans (by norm_num) psum780o2_481
  · exact le_trans (by norm_num) psum780o2_482
  · exact le_trans (by norm_num) psum780o2_483
  · exact le_trans (by norm_num) psum780o2_484
  · exact le_trans (by norm_num) psum780o2_485
  · exact le_trans (by norm_num) psum780o2_486
  · exact le_trans (by norm_num) psum780o2_487
  · exact le_trans (by norm_num) psum780o2_488
  · exact le_trans (by norm_num) psum780o2_489
  · exact le_trans (by norm_num) psum780o2_490
  · exact le_trans (by norm_num) psum780o2_491
  · exact le_trans (by norm_num) psum780o2_492
  · exact le_trans (by norm_num) psum780o2_493
  · exact le_trans (by norm_num) psum780o2_494
  · exact le_trans (by norm_num) psum780o2_495
  · exact le_trans (by norm_num) psum780o2_496
  · exact le_trans (by norm_num) psum780o2_497
  · exact le_trans (by norm_num) psum780o2_498
  · exact le_trans (by norm_num) psum780o2_499
  · exact le_trans (by norm_num) psum780o2_500

end CriticalLinePhasor.DVP

section AxiomAudit
#print axioms CriticalLinePhasor.DVP.psum780o2_floor
#print axioms CriticalLinePhasor.DVP.psum780o2_500
end AxiomAudit
