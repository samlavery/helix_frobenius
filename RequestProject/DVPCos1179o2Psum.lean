import RequestProject.DVPCos1179o2Table

/-!
# The cosine partial-sum floor, `t = 1179/2` (N = 1000)
-/

open Finset

noncomputable section

namespace CriticalLinePhasor.DVP

/-- The cosine sequence of the `t = 1179/2` segment certificate. -/
def cos1179o2c (n : ℕ) : ℝ := Real.cos (((1179:ℕ):ℝ) * (Real.log n / 2))

theorem psum1179o2_11 : ((617207/625000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 11, cos1179o2c k := by
  rw [Finset.Icc_self, Finset.sum_singleton]
  have h : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 11 - ((1234539/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_11).1
  push_cast at h ⊢
  linarith

theorem psum1179o2_12 : ((16320333/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 12, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 12, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 11, cos1179o2c k) + cos1179o2c 12 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 11) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_11
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 12 - ((6446021/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_12).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_13 : ((1035363/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 13, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 13, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 12, cos1179o2c k) + cos1179o2c 13 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 12) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_12
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 13 - ((-5965703/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_13).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_14 : ((1153759/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 14, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 14, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 13, cos1179o2c k) + cos1179o2c 14 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 13) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_13
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 14 - ((-1005639/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_14).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_15 : ((11237753/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 15, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 15, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 14, cos1179o2c k) + cos1179o2c 15 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 14) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_14
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 15 - ((1786247/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_15).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_16 : ((18110789/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 16, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 16, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 15, cos1179o2c k) + cos1179o2c 16 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 15) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_15
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 16 - ((1718509/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_16).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_17 : ((22212711/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 17, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 17, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 16, cos1179o2c k) + cos1179o2c 17 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 16) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_16
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 17 - ((2051461/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_17).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_18 : ((26469911/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 18, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 18, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 17, cos1179o2c k) + cos1179o2c 18 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 17) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_17
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 18 - ((21291/50000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_18).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_19 : ((328759/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 19, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 19, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 18, cos1179o2c k) + cos1179o2c 19 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 18) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_18
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 19 - ((-168191/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_19).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_20 : ((4434319/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 20, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 20, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 19, cos1179o2c k) + cos1179o2c 20 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 19) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_19
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 20 - ((573427/625000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_20).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_21 : ((7307673/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 21, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 21, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 20, cos1179o2c k) + cos1179o2c 21 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 20) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_20
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 21 - ((-312143/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_21).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_22 : ((9804803/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 22, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 22, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 21, cos1179o2c k) + cos1179o2c 22 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 21) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_21
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 22 - ((124869/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_22).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_23 : ((43598603/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 23, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 23, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 22, cos1179o2c k) + cos1179o2c 23 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 22) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_22
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 23 - ((4380391/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_23).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_24 : ((48367911/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 24, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 24, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 23, cos1179o2c k) + cos1179o2c 24 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 23) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_23
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 24 - ((1192577/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_24).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_25 : ((3647923/625000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 25, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 25, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 24, cos1179o2c k) + cos1179o2c 25 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 24) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_24
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 25 - ((9999857/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_25).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_26 : ((2165707/400000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 26, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 26, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 25, cos1179o2c k) + cos1179o2c 26 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 25) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_25
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 26 - ((-4223093/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_26).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_27 : ((27962213/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 27, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 27, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 26, cos1179o2c k) + cos1179o2c 27 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 26) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_26
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 27 - ((1782751/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_27).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_28 : ((49242647/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 28, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 28, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 27, cos1179o2c k) + cos1179o2c 28 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 27) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_27
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 28 - ((-6680779/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_28).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_29 : ((5817693/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 29, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 29, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 28, cos1179o2c k) + cos1179o2c 29 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 28) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_28
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 29 - ((8935283/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_29).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_30 : ((13203171/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 30, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 30, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 29, cos1179o2c k) + cos1179o2c 30 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 29) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_29
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 30 - ((313597/400000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_30).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_31 : ((35050709/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 31, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 31, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 30, cos1179o2c k) + cos1179o2c 31 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 30) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_30
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 31 - ((4086563/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_31).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_32 : ((942089/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 32, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 32, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 31, cos1179o2c k) + cos1179o2c 32 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 31) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_31
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 32 - ((2633351/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_32).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_33 : ((21225079/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 33, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 33, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 32, cos1179o2c k) + cos1179o2c 33 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 32) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_32
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 33 - ((2383549/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_33).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_34 : ((90758427/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 34, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 34, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 33, cos1179o2c k) + cos1179o2c 34 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 33) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_33
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 34 - ((5859111/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_34).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_35 : ((8169031/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 35, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 35, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 34, cos1179o2c k) + cos1179o2c 35 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 34) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_34
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 35 - ((-9067117/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_35).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_36 : ((10504209/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 36, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 36, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 35, cos1179o2c k) + cos1179o2c 36 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 35) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_35
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 36 - ((1172181/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_36).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_37 : ((17217797/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 37, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 37, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 36, cos1179o2c k) + cos1179o2c 37 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 36) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_36
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 37 - ((2056313/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_37).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_38 : ((83905207/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 38, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 38, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 37, cos1179o2c k) + cos1179o2c 38 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 37) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_37
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 38 - ((-1091389/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_38).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_39 : ((82159613/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 39, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 39, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 38, cos1179o2c k) + cos1179o2c 39 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 38) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_38
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 39 - ((-872297/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_39).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_40 : ((11292723/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 40, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 40, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 39, cos1179o2c k) + cos1179o2c 40 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 39) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_39
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 40 - ((8183171/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_40).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_41 : ((20440097/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 41, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 41, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 40, cos1179o2c k) + cos1179o2c 41 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 40) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_40
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 41 - ((-2145099/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_41).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_42 : ((1930543/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 42, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 42, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 41, cos1179o2c k) + cos1179o2c 42 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 41) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_41
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 42 - ((-1134417/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_42).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_43 : ((16925221/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 43, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 43, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 42, cos1179o2c k) + cos1179o2c 43 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 42) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_42
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 43 - ((1481077/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_43).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_44 : ((47158331/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 44, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 44, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 43, cos1179o2c k) + cos1179o2c 44 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 43) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_43
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 44 - ((9691557/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_44).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_45 : ((100291119/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 45, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 45, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 44, cos1179o2c k) + cos1179o2c 45 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 44) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_44
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 45 - ((5975457/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_45).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_46 : ((5138327/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 46, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 46, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 45, cos1179o2c k) + cos1179o2c 46 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 45) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_45
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 46 - ((2476421/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_46).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_47 : ((104147627/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 47, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 47, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 46, cos1179o2c k) + cos1179o2c 47 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 46) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_46
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 47 - ((1382087/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_47).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_48 : ((26761219/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 48, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 48, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 47, cos1179o2c k) + cos1179o2c 48 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 47) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_47
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 48 - ((2898249/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_48).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_49 : ((11352723/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 49, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 49, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 48, cos1179o2c k) + cos1179o2c 49 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 48) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_48
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 49 - ((3241677/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_49).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_50 : ((123309489/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 50, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 50, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 49, cos1179o2c k) + cos1179o2c 50 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 49) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_49
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 50 - ((9783259/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_50).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_51 : ((65529003/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 51, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 51, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 50, cos1179o2c k) + cos1179o2c 51 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 50) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_50
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 51 - ((7749517/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_51).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_52 : ((128750347/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 52, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 52, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 51, cos1179o2c k) + cos1179o2c 52 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 51) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_51
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 52 - ((-2306659/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_52).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_53 : ((118749349/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 53, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 53, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 52, cos1179o2c k) + cos1179o2c 53 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 52) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_52
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 53 - ((-4999999/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_53).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_54 : ((118508409/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 54, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 54, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 53, cos1179o2c k) + cos1179o2c 54 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 53) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_53
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 54 - ((-11997/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_54).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_55 : ((64193929/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 55, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 55, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 54, cos1179o2c k) + cos1179o2c 55 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 54) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_54
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 55 - ((9880449/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_55).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_56 : ((61672443/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 56, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 56, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 55, cos1179o2c k) + cos1179o2c 56 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 55) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_55
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 56 - ((-1260493/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_56).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_57 : ((118720027/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 57, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 57, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 56, cos1179o2c k) + cos1179o2c 57 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 56) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_56
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 57 - ((-4623859/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_57).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_58 : ((128376667/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 58, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 58, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 57, cos1179o2c k) + cos1179o2c 58 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 57) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_57
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 58 - ((241441/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_58).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_59 : ((59563187/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 59, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 59, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 58, cos1179o2c k) + cos1179o2c 59 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 58) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_58
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 59 - ((-9249293/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_59).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_60 : ((125551031/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 60, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 60, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 59, cos1179o2c k) + cos1179o2c 60 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 59) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_59
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 60 - ((6425657/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_60).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_61 : ((121853853/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 61, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 61, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 60, cos1179o2c k) + cos1179o2c 61 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 60) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_60
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 61 - ((-1848089/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_61).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_62 : ((124013781/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 62, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 62, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 61, cos1179o2c k) + cos1179o2c 62 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 61) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_61
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 62 - ((67529/312500 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_62).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_63 : ((121924729/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 63, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 63, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 62, cos1179o2c k) + cos1179o2c 63 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 62) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_62
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 63 - ((-522013/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_63).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_64 : ((12536687/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 64, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 64, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 63, cos1179o2c k) + cos1179o2c 64 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 63) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_63
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 64 - ((3443141/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_64).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_65 : ((119421541/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 65, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 65, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 64, cos1179o2c k) + cos1179o2c 65 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 64) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_64
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 65 - ((-5944329/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_65).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_66 : ((128149697/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 66, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 66, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 65, cos1179o2c k) + cos1179o2c 66 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 65) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_65
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 66 - ((2182289/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_66).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_67 : ((59080669/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 67, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 67, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 66, cos1179o2c k) + cos1179o2c 67 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 66) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_66
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 67 - ((-9987359/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_67).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_68 : ((5021379/400000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 68, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 68, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 67, cos1179o2c k) + cos1179o2c 68 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 67) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_67
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 68 - ((7374137/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_68).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_69 : ((125428997/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 69, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 69, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 68, cos1179o2c k) + cos1179o2c 69 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 68) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_68
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 69 - ((-52239/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_69).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_70 : ((29349679/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 70, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 70, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 69, cos1179o2c k) + cos1179o2c 70 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 69) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_69
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 70 - ((-8029281/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_70).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_71 : ((15813847/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 71, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 71, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 70, cos1179o2c k) + cos1179o2c 71 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 70) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_70
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 71 - ((455653/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_71).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_72 : ((25368761/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 72, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 72, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 71, cos1179o2c k) + cos1179o2c 72 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 71) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_71
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 72 - ((334029/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_72).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_73 : ((117138431/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 73, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 73, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 72, cos1179o2c k) + cos1179o2c 73 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 72) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_72
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 73 - ((-4852187/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_73).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_74 : ((24225217/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 74, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 74, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 73, cos1179o2c k) + cos1179o2c 74 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 73) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_73
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 74 - ((1994327/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_74).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_75 : ((812777/62500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 75, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 75, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 74, cos1179o2c k) + cos1179o2c 75 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 74) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_74
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 75 - ((1783847/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_75).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_76 : ((125935799/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 76, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 76, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 75, cos1179o2c k) + cos1179o2c 76 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 75) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_75
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 76 - ((-4107521/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_76).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_77 : ((58155681/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 77, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 77, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 76, cos1179o2c k) + cos1179o2c 77 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 76) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_76
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 77 - ((-9623437/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_77).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_78 : ((58294527/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 78, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 78, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 77, cos1179o2c k) + cos1179o2c 78 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 77) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_77
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 78 - ((69673/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_78).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_79 : ((63045729/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 79, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 79, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 78, cos1179o2c k) + cos1179o2c 79 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 78) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_78
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 79 - ((2375851/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_79).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_80 : ((66472573/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 80, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 80, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 79, cos1179o2c k) + cos1179o2c 80 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 79) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_79
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 80 - ((214209/312500 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_80).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_81 : ((130136113/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 81, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 81, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 80, cos1179o2c k) + cos1179o2c 81 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 80) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_80
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 81 - ((-2808033/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_81).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_82 : ((377171/31250 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 82, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 82, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 81, cos1179o2c k) + cos1179o2c 82 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 81) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_81
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 82 - ((-9440393/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_82).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_83 : ((112046769/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 83, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 83, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 82, cos1179o2c k) + cos1179o2c 83 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 82) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_82
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 83 - ((-8646951/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_83).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_84 : ((109399781/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 84, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 84, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 83, cos1179o2c k) + cos1179o2c 84 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 83) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_83
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 84 - ((-661497/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_84).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_85 : ((113525953/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 85, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 85, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 84, cos1179o2c k) + cos1179o2c 85 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 84) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_84
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 85 - ((1031793/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_85).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_86 : ((122133983/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 86, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 86, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 85, cos1179o2c k) + cos1179o2c 86 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 85) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_85
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 86 - ((860903/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_86).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_87 : ((132132967/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 87, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 87, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 86, cos1179o2c k) + cos1179o2c 87 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 86) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_86
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 87 - ((624999/625000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_87).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_88 : ((28225331/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 88, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 88, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 87, cos1179o2c k) + cos1179o2c 88 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 87) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_87
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 88 - ((70271/78125 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_88).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_89 : ((147873571/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 89, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 89, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 88, cos1179o2c k) + cos1179o2c 89 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 88) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_88
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 89 - ((1686979/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_89).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_90 : ((76053341/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 90, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 90, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 89, cos1179o2c k) + cos1179o2c 90 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 89) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_89
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 90 - ((4234111/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_90).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_91 : ((2408689/156250 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 91, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 91, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 90, cos1179o2c k) + cos1179o2c 91 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 90) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_90
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 91 - ((1025207/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_91).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_92 : ((77312543/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 92, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 92, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 91, cos1179o2c k) + cos1179o2c 92 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 91) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_91
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 92 - ((46999/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_92).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_93 : ((77097989/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 93, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 93, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 92, cos1179o2c k) + cos1179o2c 93 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 92) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_92
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 93 - ((-107027/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_93).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_94 : ((76775123/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 94, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 94, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 93, cos1179o2c k) + cos1179o2c 94 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 93) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_93
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 94 - ((-161183/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_94).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_95 : ((38338613/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 95, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 95, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 94, cos1179o2c k) + cos1179o2c 95 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 94) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_94
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 95 - ((-97397/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_95).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_96 : ((30852187/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 96, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 96, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 95, cos1179o2c k) + cos1179o2c 96 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 95) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_95
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 96 - ((907483/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_96).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_97 : ((156880843/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 97, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 97, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 96, cos1179o2c k) + cos1179o2c 97 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 96) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_96
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 97 - ((655227/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_97).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_98 : ((161693101/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 98, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 98, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 97, cos1179o2c k) + cos1179o2c 98 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 97) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_97
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 98 - ((2406629/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_98).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_99 : ((168869229/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 99, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 99, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 98, cos1179o2c k) + cos1179o2c 99 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 98) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_98
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 99 - ((897141/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_99).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_100 : ((35606489/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 100, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 100, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 99, cos1179o2c k) + cos1179o2c 100 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 99) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_99
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 100 - ((1145527/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_100).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_101 : ((47007821/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 101, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 101, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 100, cos1179o2c k) + cos1179o2c 101 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 100) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_100
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 101 - ((9999839/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_101).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_102 : ((196895943/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 102, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 102, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 101, cos1179o2c k) + cos1179o2c 102 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 101) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_101
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 102 - ((8865659/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_102).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_103 : ((202189033/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 103, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 103, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 102, cos1179o2c k) + cos1179o2c 103 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 102) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_102
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 103 - ((529409/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_103).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_104 : ((201892161/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 104, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 104, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 103, cos1179o2c k) + cos1179o2c 104 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 103) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_103
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 104 - ((-4623/156250 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_104).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_105 : ((48917277/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 105, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 105, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 104, cos1179o2c k) + cos1179o2c 105 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 104) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_104
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 105 - ((-6222053/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_105).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_106 : ((185874957/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 106, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 106, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 105, cos1179o2c k) + cos1179o2c 106 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 105) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_105
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 106 - ((-9793151/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_106).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_107 : ((177318281/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 107, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 107, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 106, cos1179o2c k) + cos1179o2c 107 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 106) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_106
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 107 - ((-2138919/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_107).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_108 : ((175064527/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 108, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 108, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 107, cos1179o2c k) + cos1179o2c 108 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 107) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_107
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 108 - ((-1126377/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_108).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_109 : ((180896433/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 109, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 109, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 108, cos1179o2c k) + cos1179o2c 109 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 108) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_108
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 109 - ((2916453/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_109).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_110 : ((1908837/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 110, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 110, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 109, cos1179o2c k) + cos1179o2c 110 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 109) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_109
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 110 - ((9988267/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_110).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_111 : ((197100183/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 111, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 111, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 110, cos1179o2c k) + cos1179o2c 111 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 110) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_110
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 111 - ((6217483/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_111).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_112 : ((38780797/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 112, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 112, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 111, cos1179o2c k) + cos1179o2c 112 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 111) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_111
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 112 - ((-1597599/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_112).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_113 : ((23013403/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 113, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 113, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 112, cos1179o2c k) + cos1179o2c 113 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 112) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_112
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 113 - ((-9795761/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_113).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_114 : ((177787911/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 114, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 114, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 113, cos1179o2c k) + cos1179o2c 114 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 113) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_113
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 114 - ((-6318313/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_114).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_115 : ((182143369/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 115, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 115, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 114, cos1179o2c k) + cos1179o2c 115 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 114) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_114
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 115 - ((2178229/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_115).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_116 : ((192124819/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 116, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 116, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 115, cos1179o2c k) + cos1179o2c 116 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 115) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_115
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 116 - ((199649/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_116).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_117 : ((194969037/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 117, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 117, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 116, cos1179o2c k) + cos1179o2c 117 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 116) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_116
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 117 - ((1422609/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_117).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_118 : ((186676343/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 118, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 118, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 117, cos1179o2c k) + cos1179o2c 118 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 117) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_117
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 118 - ((-4145847/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_118).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_119 : ((179126617/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 119, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 119, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 118, cos1179o2c k) + cos1179o2c 119 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 118) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_118
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 119 - ((-3774363/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_119).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_120 : ((45968131/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 120, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 120, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 119, cos1179o2c k) + cos1179o2c 120 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 119) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_119
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 120 - ((4746907/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_120).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_121 : ((7735197/400000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 121, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 121, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 120, cos1179o2c k) + cos1179o2c 121 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 120) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_120
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 121 - ((9508401/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_121).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_122 : ((95817109/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 122, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 122, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 121, cos1179o2c k) + cos1179o2c 122 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 121) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_121
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 122 - ((-1744707/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_122).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_123 : ((1816617/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 123, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 123, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 122, cos1179o2c k) + cos1179o2c 123 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 122) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_122
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 123 - ((-4985759/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_123).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_124 : ((181806509/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 124, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 124, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 123, cos1179o2c k) + cos1179o2c 124 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 123) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_123
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 124 - ((145809/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_124).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_125 : ((47951297/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 125, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 125, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 124, cos1179o2c k) + cos1179o2c 125 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 124) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_124
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 125 - ((9999679/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_125).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_126 : ((191732953/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 126, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 126, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 125, cos1179o2c k) + cos1179o2c 126 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 125) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_125
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 126 - ((-14247/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_126).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_127 : ((181749623/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 127, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 127, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 126, cos1179o2c k) + cos1179o2c 127 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 126) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_126
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 127 - ((-998233/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_127).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_128 : ((183225983/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 128, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 128, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 127, cos1179o2c k) + cos1179o2c 128 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 127) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_127
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 128 - ((18467/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_128).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_129 : ((192854483/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 129, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 129, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 128, cos1179o2c k) + cos1179o2c 129 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 128) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_128
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 129 - ((19259/20000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_129).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_130 : ((94327261/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 130, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 130, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 129, cos1179o2c k) + cos1179o2c 130 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 129) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_129
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 130 - ((-4198961/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_130).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_131 : ((180564067/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 131, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 131, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 130, cos1179o2c k) + cos1179o2c 131 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 130) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_130
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 131 - ((-1617891/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_131).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_132 : ((188127889/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 132, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 132, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 131, cos1179o2c k) + cos1179o2c 132 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 131) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_131
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 132 - ((3782411/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_132).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_133 : ((9623631/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 133, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 133, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 132, cos1179o2c k) + cos1179o2c 133 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 132) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_132
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 133 - ((4345731/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_133).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_134 : ((36517661/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 134, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 134, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 133, cos1179o2c k) + cos1179o2c 134 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 133) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_133
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 134 - ((-1976663/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_134).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_135 : ((184343869/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 135, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 135, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 134, cos1179o2c k) + cos1179o2c 135 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 134) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_134
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 135 - ((439141/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_135).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_136 : ((192928209/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 136, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 136, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 135, cos1179o2c k) + cos1179o2c 136 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 135) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_135
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 136 - ((429267/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_136).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_137 : ((184898797/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 137, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 137, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 136, cos1179o2c k) + cos1179o2c 137 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 136) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_136
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 137 - ((-2007103/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_137).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_138 : ((91388911/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 138, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 138, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 137, cos1179o2c k) + cos1179o2c 138 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 137) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_137
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 138 - ((-84799/400000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_138).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_139 : ((9624223/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 139, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 139, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 138, cos1179o2c k) + cos1179o2c 139 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 138) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_138
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 139 - ((4853819/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_139).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_140 : ((185822503/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 140, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 140, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 139, cos1179o2c k) + cos1179o2c 140 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 139) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_139
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 140 - ((-6660957/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_140).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_141 : ((22828371/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 141, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 141, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 140, cos1179o2c k) + cos1179o2c 141 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 140) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_140
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 141 - ((-638907/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_141).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_142 : ((24047811/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 142, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 142, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 141, cos1179o2c k) + cos1179o2c 142 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 141) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_141
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 142 - ((243913/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_142).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_143 : ((185231407/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 143, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 143, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 142, cos1179o2c k) + cos1179o2c 143 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 142) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_142
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 143 - ((-7150081/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_143).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_144 : ((36708187/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 144, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 144, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 143, cos1179o2c k) + cos1179o2c 144 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 143) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_143
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 144 - ((-13199/78125 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_144).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_145 : ((192487133/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 145, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 145, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 144, cos1179o2c k) + cos1179o2c 145 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 144) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_144
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 145 - ((4473599/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_145).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_146 : ((91734303/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 146, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 146, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 145, cos1179o2c k) + cos1179o2c 146 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 145) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_145
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 146 - ((-9017527/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_146).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_147 : ((185859509/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 147, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 147, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 146, cos1179o2c k) + cos1179o2c 147 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 146) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_146
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 147 - ((2391903/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_147).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_148 : ((191615907/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 148, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 148, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 147, cos1179o2c k) + cos1179o2c 148 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 147) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_147
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 148 - ((2878699/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_148).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_149 : ((90849081/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 149, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 149, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 148, cos1179o2c k) + cos1179o2c 149 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 148) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_148
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 149 - ((-1983349/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_149).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_150 : ((189520543/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 150, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 150, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 149, cos1179o2c k) + cos1179o2c 150 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 149) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_149
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 150 - ((7823381/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_150).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_151 : ((7531701/400000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 151, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 151, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 150, cos1179o2c k) + cos1179o2c 151 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 150) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_150
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 151 - ((-613509/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_151).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_152 : ((22803541/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 152, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 152, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 151, cos1179o2c k) + cos1179o2c 152 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 151) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_151
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 152 - ((-5863197/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_152).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_153 : ((96092831/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 153, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 153, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 152, cos1179o2c k) + cos1179o2c 153 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 152) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_152
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 153 - ((4879167/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_153).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_154 : ((45826983/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 154, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 154, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 153, cos1179o2c k) + cos1179o2c 154 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 153) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_153
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 154 - ((-887673/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_154).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_155 : ((187369197/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 155, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 155, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 154, cos1179o2c k) + cos1179o2c 155 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 154) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_154
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 155 - ((812453/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_155).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_156 : ((189658703/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 156, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 156, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 155, cos1179o2c k) + cos1179o2c 156 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 155) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_155
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 156 - ((1145253/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_156).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_157 : ((182103491/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 157, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 157, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 156, cos1179o2c k) + cos1179o2c 157 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 156) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_156
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 157 - ((-1888553/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_157).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_158 : ((48009611/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 158, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 158, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 157, cos1179o2c k) + cos1179o2c 158 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 157) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_157
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 158 - ((9935953/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_158).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_159 : ((183096727/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 159, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 159, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 158, cos1179o2c k) + cos1179o2c 159 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 158) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_158
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 159 - ((-8940717/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_159).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_160 : ((11771237/625000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 160, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 160, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 159, cos1179o2c k) + cos1179o2c 160 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 159) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_159
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 160 - ((1048813/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_160).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_161 : ((94065749/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 161, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 161, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 160, cos1179o2c k) + cos1179o2c 161 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 160) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_160
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 161 - ((-103647/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_161).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_162 : ((22930391/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 162, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 162, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 161, cos1179o2c k) + cos1179o2c 162 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 161) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_161
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 162 - ((-468737/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_162).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_163 : ((38342697/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 163, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 163, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 162, cos1179o2c k) + cos1179o2c 163 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 162) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_162
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 163 - ((8271357/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_163).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_164 : ((181800663/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 164, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 164, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 163, cos1179o2c k) + cos1179o2c 164 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 163) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_163
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 164 - ((-4955911/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_164).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_165 : ((191325799/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 165, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 165, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 164, cos1179o2c k) + cos1179o2c 165 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 164) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_164
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 165 - ((1190767/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_165).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_166 : ((91934607/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 166, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 166, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 165, cos1179o2c k) + cos1179o2c 166 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 165) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_165
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 166 - ((-1491117/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_166).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_167 : ((23518629/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 167, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 167, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 166, cos1179o2c k) + cos1179o2c 167 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 166) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_166
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 167 - ((2140409/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_167).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_168 : ((93751301/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 168, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 168, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 167, cos1179o2c k) + cos1179o2c 168 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 167) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_167
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 168 - ((-64543/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_168).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_169 : ((184619243/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 169, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 169, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 168, cos1179o2c k) + cos1179o2c 169 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 168) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_168
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 169 - ((-2882359/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_169).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_170 : ((95249447/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 170, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 170, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 169, cos1179o2c k) + cos1179o2c 170 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 169) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_169
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 170 - ((5880651/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_170).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_171 : ((182395571/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 171, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 171, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 170, cos1179o2c k) + cos1179o2c 171 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 170) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_170
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 171 - ((-8102323/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_171).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_172 : ((47963323/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 172, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 172, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 171, cos1179o2c k) + cos1179o2c 172 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 171) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_171
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 172 - ((9458721/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_172).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_173 : ((1420838/78125 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 173, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 173, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 172, cos1179o2c k) + cos1179o2c 173 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 172) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_172
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 173 - ((-2496257/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_173).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_174 : ((11979011/625000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 174, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 174, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 173, cos1179o2c k) + cos1179o2c 174 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 173) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_173
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 174 - ((1224739/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_174).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_175 : ((11412957/625000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 175, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 175, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 174, cos1179o2c k) + cos1179o2c 175 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 174) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_174
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 175 - ((-1131983/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_175).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_176 : ((38106853/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 176, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 176, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 175, cos1179o2c k) + cos1179o2c 176 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 175) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_175
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 176 - ((7927953/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_176).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_177 : ((1437204/78125 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 177, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 177, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 176, cos1179o2c k) + cos1179o2c 177 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 176) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_176
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 177 - ((-6571153/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_177).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_178 : ((5908769/312500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 178, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 178, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 177, cos1179o2c k) + cos1179o2c 178 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 177) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_177
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 178 - ((639937/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_178).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_179 : ((7416121/400000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 179, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 179, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 178, cos1179o2c k) + cos1179o2c 179 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 178) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_178
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 179 - ((-3676583/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_179).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_180 : ((187720513/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 180, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 180, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 179, cos1179o2c k) + cos1179o2c 180 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 179) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_179
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 180 - ((289811/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_180).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_181 : ((186625481/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 181, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 181, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 180, cos1179o2c k) + cos1179o2c 181 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 180) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_180
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 181 - ((-68377/625000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_181).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_182 : ((186657541/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 182, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 182, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 181, cos1179o2c k) + cos1179o2c 182 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 181) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_181
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 182 - ((1653/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_182).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_183 : ((187508173/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 183, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 183, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 182, cos1179o2c k) + cos1179o2c 183 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 182) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_182
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 183 - ((53227/625000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_183).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_184 : ((46487847/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 184, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 184, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 183, cos1179o2c k) + cos1179o2c 184 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 183) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_183
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 184 - ((-311157/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_184).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_185 : ((188032731/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 185, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 185, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 184, cos1179o2c k) + cos1179o2c 185 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 184) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_184
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 185 - ((2082343/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_185).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_186 : ((185595951/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 186, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 186, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 185, cos1179o2c k) + cos1179o2c 186 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 185) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_185
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 186 - ((-121789/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_186).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_187 : ((37643503/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 187, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 187, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 186, cos1179o2c k) + cos1179o2c 187 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 186) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_186
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 187 - ((655641/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_187).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_188 : ((92785459/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 188, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 188, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 187, cos1179o2c k) + cos1179o2c 188 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 187) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_187
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 188 - ((-2645597/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_188).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_189 : ((94038981/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 189, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 189, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 188, cos1179o2c k) + cos1179o2c 189 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 188) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_188
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 189 - ((627011/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_189).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_190 : ((185868227/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 190, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 190, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 189, cos1179o2c k) + cos1179o2c 190 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 189) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_189
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 190 - ((-441747/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_190).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_191 : ((187614597/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 191, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 191, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 190, cos1179o2c k) + cos1179o2c 191 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 190) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_190
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 191 - ((174737/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_191).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_192 : ((186492399/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 192, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 192, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 191, cos1179o2c k) + cos1179o2c 192 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 191) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_191
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 192 - ((-560599/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_192).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_193 : ((186822319/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 193, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 193, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 192, cos1179o2c k) + cos1179o2c 193 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 192) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_192
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 193 - ((8273/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_193).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_194 : ((187440509/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 194, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 194, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 193, cos1179o2c k) + cos1179o2c 194 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 193) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_193
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 194 - ((61919/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_194).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_195 : ((1160757/62500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 195, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 195, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 194, cos1179o2c k) + cos1179o2c 195 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 194) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_194
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 195 - ((-1718389/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_195).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_196 : ((188665167/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 196, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 196, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 195, cos1179o2c k) + cos1179o2c 196 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 195) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_195
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 196 - ((2945047/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_196).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_197 : ((922001/50000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 197, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 197, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 196, cos1179o2c k) + cos1179o2c 197 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 196) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_196
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 197 - ((-4263967/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_197).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_198 : ((190023177/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 198, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 198, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 197, cos1179o2c k) + cos1179o2c 198 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 197) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_197
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 198 - ((5623977/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_198).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_199 : ((11441709/625000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 199, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 199, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 198, cos1179o2c k) + cos1179o2c 199 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 198) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_198
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 199 - ((-6954833/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_199).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_200 : ((191234193/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 200, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 200, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 199, cos1179o2c k) + cos1179o2c 200 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 199) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_199
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 200 - ((8167849/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_200).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_201 : ((11379769/625000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 201, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 201, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 200, cos1179o2c k) + cos1179o2c 201 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 200) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_200
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 201 - ((-9156889/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_201).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_202 : ((11992557/625000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 202, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 202, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 201, cos1179o2c k) + cos1179o2c 202 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 201) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_201
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 202 - ((1225701/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_202).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_203 : ((90942673/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 203, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 203, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 202, cos1179o2c k) + cos1179o2c 203 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 202) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_202
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 203 - ((-4997283/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_203).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_204 : ((191501073/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 204, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 204, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 203, cos1179o2c k) + cos1179o2c 204 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 203) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_203
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 204 - ((9616727/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_204).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_205 : ((182906043/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 205, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 205, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 204, cos1179o2c k) + cos1179o2c 205 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 204) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_204
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 205 - ((-859403/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_205).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_206 : ((189802467/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 206, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 206, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 205, cos1179o2c k) + cos1179o2c 206 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 205) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_205
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 206 - ((431089/625000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_206).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_207 : ((7409389/400000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 207, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 207, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 206, cos1179o2c k) + cos1179o2c 207 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 206) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_206
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 207 - ((-2283371/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_207).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_208 : ((11685087/625000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 208, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 208, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 207, cos1179o2c k) + cos1179o2c 208 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 207) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_207
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 208 - ((1727667/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_208).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_209 : ((188361713/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 209, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 209, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 208, cos1179o2c k) + cos1179o2c 209 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 208) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_208
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 209 - ((1401321/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_209).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_210 : ((183846771/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 210, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 210, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 209, cos1179o2c k) + cos1179o2c 210 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 209) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_209
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 210 - ((-2256971/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_210).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_211 : ((47771197/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 211, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 211, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 210, cos1179o2c k) + cos1179o2c 211 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 210) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_210
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 211 - ((7239017/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_211).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_212 : ((90950287/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 212, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 212, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 211, cos1179o2c k) + cos1179o2c 212 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 211) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_211
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 212 - ((-4591607/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_212).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_213 : ((191891769/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 213, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 213, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 212, cos1179o2c k) + cos1179o2c 213 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 212) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_212
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 213 - ((1998439/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_213).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_214 : ((182466297/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 214, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 214, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 213, cos1179o2c k) + cos1179o2c 214 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 213) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_213
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 214 - ((-1178059/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_214).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_215 : ((23736067/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 215, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 215, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 214, cos1179o2c k) + cos1179o2c 215 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 214) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_214
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 215 - ((7423239/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_215).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_216 : ((46428673/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 216, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 216, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 215, cos1179o2c k) + cos1179o2c 216 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 215) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_215
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 216 - ((-1043211/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_216).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_217 : ((185830729/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 217, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 217, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 216, cos1179o2c k) + cos1179o2c 217 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 216) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_216
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 217 - ((117037/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_217).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_218 : ((94951587/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 218, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 218, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 217, cos1179o2c k) + cos1179o2c 218 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 217) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_217
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 218 - ((814689/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_218).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_219 : ((11393943/625000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 219, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 219, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 218, cos1179o2c k) + cos1179o2c 219 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 218) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_218
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 219 - ((-3799543/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_219).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_220 : ((95993527/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 220, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 220, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 219, cos1179o2c k) + cos1179o2c 220 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 219) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_219
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 220 - ((4842483/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_220).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_221 : ((182219323/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 221, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 221, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 220, cos1179o2c k) + cos1179o2c 221 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 220) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_220
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 221 - ((-9766731/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_221).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_222 : ((23736033/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 222, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 222, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 221, cos1179o2c k) + cos1179o2c 222 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 221) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_221
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 222 - ((7669941/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_222).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_223 : ((93079749/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 223, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 223, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 222, cos1179o2c k) + cos1179o2c 223 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 222) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_222
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 223 - ((-1863883/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_223).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_224 : ((184941589/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 224, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 224, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 223, cos1179o2c k) + cos1179o2c 224 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 223) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_223
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 224 - ((-1216909/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_224).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_225 : ((190894217/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 225, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 225, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 224, cos1179o2c k) + cos1179o2c 225 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 224) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_224
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 225 - ((1488407/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_225).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_226 : ((181704771/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 226, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 226, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 225, cos1179o2c k) + cos1179o2c 226 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 225) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_225
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 226 - ((-4594223/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_226).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_227 : ((95807551/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 227, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 227, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 226, cos1179o2c k) + cos1179o2c 227 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 226) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_226
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 227 - ((9911331/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_227).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_228 : ((183861399/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 228, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 228, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 227, cos1179o2c k) + cos1179o2c 228 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 227) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_227
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 228 - ((-7752703/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_228).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_229 : ((93528819/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 229, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 229, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 228, cos1179o2c k) + cos1179o2c 229 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 228) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_228
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 229 - ((3197239/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_229).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_230 : ((189506701/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 230, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 230, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 229, cos1179o2c k) + cos1179o2c 230 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 229) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_229
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 230 - ((2450063/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_230).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_231 : ((182115383/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 231, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 231, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 230, cos1179o2c k) + cos1179o2c 231 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 230) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_230
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 231 - ((-3695159/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_231).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_232 : ((192010917/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 232, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 232, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 231, cos1179o2c k) + cos1179o2c 232 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 231) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_231
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 232 - ((4948267/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_232).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_233 : ((1430147/78125 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 233, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 233, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 232, cos1179o2c k) + cos1179o2c 233 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 232) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_232
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 233 - ((-8951101/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_233).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_234 : ((93889697/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 234, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 234, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 233, cos1179o2c k) + cos1179o2c 234 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 233) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_233
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 234 - ((2360789/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_234).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_235 : ((1513073/80000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 235, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 235, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 234, cos1179o2c k) + cos1179o2c 235 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 234) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_234
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 235 - ((1355731/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_235).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_236 : ((182140319/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 236, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 236, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 235, cos1179o2c k) + cos1179o2c 236 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 235) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_235
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 236 - ((-3496403/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_236).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_237 : ((24003861/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 237, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 237, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 236, cos1179o2c k) + cos1179o2c 237 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 236) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_236
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 237 - ((9891569/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_237).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_238 : ((45828187/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 238, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 238, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 237, cos1179o2c k) + cos1179o2c 238 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 237) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_237
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 238 - ((-435857/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_238).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_239 : ((93551317/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 239, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 239, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 238, cos1179o2c k) + cos1179o2c 239 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 238) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_238
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 239 - ((1895443/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_239).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_240 : ((23746801/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 240, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 240, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 239, cos1179o2c k) + cos1179o2c 240 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 239) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_239
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 240 - ((1436387/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_240).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_241 : ((45414557/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 241, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 241, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 240, cos1179o2c k) + cos1179o2c 241 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 240) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_240
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 241 - ((-415759/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_241).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_242 : ((191594987/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 242, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 242, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 241, cos1179o2c k) + cos1179o2c 242 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 241) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_241
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 242 - ((9937759/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_242).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_243 : ((184788617/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 243, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 243, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 242, cos1179o2c k) + cos1179o2c 243 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 242) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_242
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 243 - ((-680537/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_243).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_244 : ((185066193/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 244, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 244, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 243, cos1179o2c k) + cos1179o2c 244 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 243) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_243
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 244 - ((17411/625000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_244).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_245 : ((95764021/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 245, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 245, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 244, cos1179o2c k) + cos1179o2c 245 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 244) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_244
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 245 - ((6462849/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_245).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_246 : ((45402129/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 246, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 246, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 245, cos1179o2c k) + cos1179o2c 246 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 245) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_245
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 246 - ((-4959263/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_246).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_247 : ((189732499/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 247, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 247, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 246, cos1179o2c k) + cos1179o2c 247 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 246) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_246
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 247 - ((8124983/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_247).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_248 : ((187856189/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 248, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 248, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 247, cos1179o2c k) + cos1179o2c 248 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 247) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_247
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 248 - ((-187531/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_248).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_249 : ((9118439/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 249, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 249, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 248, cos1179o2c k) + cos1179o2c 249 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 248) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_248
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 249 - ((-5486409/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_249).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_250 : ((38429099/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 250, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 250, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 249, cos1179o2c k) + cos1179o2c 250 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 249) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_249
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 250 - ((1955543/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_250).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_251 : ((36752767/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 251, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 251, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 250, cos1179o2c k) + cos1179o2c 251 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 250) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_250
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 251 - ((-419033/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_251).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_252 : ((18571077/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 252, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 252, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 251, cos1179o2c k) + cos1179o2c 252 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 251) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_251
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 252 - ((389587/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_252).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_253 : ((191445737/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 253, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 253, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 252, cos1179o2c k) + cos1179o2c 253 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 252) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_252
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 253 - ((5735967/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_253).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_254 : ((181547913/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 254, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 254, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 253, cos1179o2c k) + cos1179o2c 254 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 253) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_253
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 254 - ((-1237103/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_254).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_255 : ((94656609/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 255, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 255, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 254, cos1179o2c k) + cos1179o2c 255 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 254) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_254
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 255 - ((1553261/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_255).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_256 : ((188762987/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 256, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 256, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 255, cos1179o2c k) + cos1179o2c 256 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 255) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_255
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 256 - ((-549231/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_256).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_257 : ((181669603/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 257, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 257, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 256, cos1179o2c k) + cos1179o2c 257 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 256) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_256
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 257 - ((-221637/312500 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_257).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_258 : ((19164419/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 258, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 258, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 257, cos1179o2c k) + cos1179o2c 258 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 257) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_257
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 258 - ((9975587/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_258).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_259 : ((185672887/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 259, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 259, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 258, cos1179o2c k) + cos1179o2c 259 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 258) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_258
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 259 - ((-5970303/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_259).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_260 : ((1467129/80000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 260, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 260, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 259, cos1179o2c k) + cos1179o2c 260 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 259) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_259
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 260 - ((-1140381/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_260).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_261 : ((192341419/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 261, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 261, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 260, cos1179o2c k) + cos1179o2c 261 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 260) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_260
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 261 - ((4475647/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_261).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_262 : ((183230901/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 262, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 262, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 261, cos1179o2c k) + cos1179o2c 262 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 261) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_261
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 262 - ((-4554759/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_262).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_263 : ((23212621/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 263, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 263, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 262, cos1179o2c k) + cos1179o2c 263 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 262) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_262
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 263 - ((2471067/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_263).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_264 : ((95894543/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 264, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 264, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 263, cos1179o2c k) + cos1179o2c 264 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 263) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_263
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 264 - ((3044559/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_264).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_265 : ((90894069/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 265, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 265, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 264, cos1179o2c k) + cos1179o2c 265 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 264) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_264
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 265 - ((-2499987/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_265).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_266 : ((93930609/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 266, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 266, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 265, cos1179o2c k) + cos1179o2c 266 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 265) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_265
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 266 - ((37963/62500 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_266).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_267 : ((190593181/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 267, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 267, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 266, cos1179o2c k) + cos1179o2c 267 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 266) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_266
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 267 - ((2732963/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_267).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_268 : ((22652449/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 268, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 268, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 267, cos1179o2c k) + cos1179o2c 268 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 267) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_267
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 268 - ((-9372589/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_268).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_269 : ((94764151/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 269, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 269, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 268, cos1179o2c k) + cos1179o2c 269 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 268) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_268
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 269 - ((830971/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_269).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_270 : ((47315191/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 270, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 270, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 269, cos1179o2c k) + cos1179o2c 270 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 269) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_269
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 270 - ((-133269/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_270).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_271 : ((181210133/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 271, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 271, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 270, cos1179o2c k) + cos1179o2c 271 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 270) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_270
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 271 - ((-8049631/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_271).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_272 : ((1906527/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 272, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 272, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 271, cos1179o2c k) + cos1179o2c 272 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 271) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_271
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 272 - ((9443567/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_272).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_273 : ((188106719/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 273, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 273, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 272, cos1179o2c k) + cos1179o2c 273 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 272) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_272
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 273 - ((-2544981/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_273).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_274 : ((181445849/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 274, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 274, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 273, cos1179o2c k) + cos1179o2c 274 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 273) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_273
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 274 - ((-665987/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_274).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_275 : ((38265873/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 275, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 275, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 274, cos1179o2c k) + cos1179o2c 275 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 274) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_274
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 275 - ((2471129/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_275).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_276 : ((93639781/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 276, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 276, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 275, cos1179o2c k) + cos1179o2c 276 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 275) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_275
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 276 - ((-4048803/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_276).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_277 : ((36338507/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 277, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 277, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 276, cos1179o2c k) + cos1179o2c 277 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 276) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_276
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 277 - ((-5586027/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_277).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_278 : ((191683863/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 278, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 278, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 277, cos1179o2c k) + cos1179o2c 278 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 277) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_277
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 278 - ((1249041/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_278).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_279 : ((93415011/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 279, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 279, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 278, cos1179o2c k) + cos1179o2c 279 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 278) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_278
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 279 - ((-4852841/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_279).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_280 : ((36362111/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 280, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 280, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 279, cos1179o2c k) + cos1179o2c 280 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 279) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_279
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 280 - ((-5018467/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_280).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_281 : ((47952357/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 281, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 281, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 280, cos1179o2c k) + cos1179o2c 281 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 280) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_280
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 281 - ((9999873/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_281).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_282 : ((9338353/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 282, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 282, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 281, cos1179o2c k) + cos1179o2c 282 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 281) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_281
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 282 - ((-630171/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_282).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_283 : ((18174097/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 283, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 283, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 282, cos1179o2c k) + cos1179o2c 283 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 282) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_282
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 283 - ((-502509/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_283).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_284 : ((191738369/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 284, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 284, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 283, cos1179o2c k) + cos1179o2c 284 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 283) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_283
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 284 - ((9998399/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_284).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_285 : ((37417987/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 285, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 285, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 284, cos1179o2c k) + cos1179o2c 285 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 284) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_284
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 285 - ((-2323717/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_285).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_286 : ((90748527/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 286, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 286, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 285, cos1179o2c k) + cos1179o2c 286 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 285) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_285
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 286 - ((-5591881/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_286).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_287 : ((95719639/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 287, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 287, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 286, cos1179o2c k) + cos1179o2c 287 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 286) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_286
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 287 - ((1242903/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_287).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_288 : ((11737141/625000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 288, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 288, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 287, cos1179o2c k) + cos1179o2c 288 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 287) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_287
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 288 - ((-1822011/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_288).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_289 : ((181159829/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 289, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 289, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 288, cos1179o2c k) + cos1179o2c 289 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 288) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_288
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 289 - ((-6633427/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_289).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_290 : ((190823337/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 290, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 290, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 289, cos1179o2c k) + cos1179o2c 290 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 289) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_289
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 290 - ((2416127/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_290).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_291 : ((9442431/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 291, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 291, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 290, cos1179o2c k) + cos1179o2c 291 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 290) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_290
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 291 - ((-1973717/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_291).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_292 : ((22611013/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 292, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 292, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 291, cos1179o2c k) + cos1179o2c 292 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 291) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_291
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 292 - ((-1989879/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_292).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_293 : ((47443873/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 293, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 293, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 292, cos1179o2c k) + cos1179o2c 293 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 292) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_292
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 293 - ((2222097/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_293).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_294 : ((190157423/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 294, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 294, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 293, cos1179o2c k) + cos1179o2c 294 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 293) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_293
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 294 - ((382931/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_294).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_295 : ((180917277/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 295, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 295, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 294, cos1179o2c k) + cos1179o2c 295 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 294) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_294
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 295 - ((-4619573/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_295).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_296 : ((188205443/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 296, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 296, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 295, cos1179o2c k) + cos1179o2c 296 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 295) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_295
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 296 - ((3644583/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_296).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_297 : ((191507693/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 297, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 297, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 296, cos1179o2c k) + cos1179o2c 297 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 296) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_296
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 297 - ((13213/40000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_297).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_298 : ((45383523/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 298, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 298, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 297, cos1179o2c k) + cos1179o2c 298 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 297) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_297
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 298 - ((-9972601/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_298).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_299 : ((93067143/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 299, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 299, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 298, cos1179o2c k) + cos1179o2c 299 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 298) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_298
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 299 - ((2300597/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_299).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_300 : ((96269267/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 300, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 300, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 299, cos1179o2c k) + cos1179o2c 300 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 299) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_299
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 300 - ((50041/78125 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_300).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_301 : ((11437299/625000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 301, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 301, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 300, cos1179o2c k) + cos1179o2c 301 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 300) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_300
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 301 - ((-38163/40000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_301).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_302 : ((1837971/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 302, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 302, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 301, cos1179o2c k) + cos1179o2c 302 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 301) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_301
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 302 - ((200329/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_302).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_303 : ((48191161/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 303, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 303, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 302, cos1179o2c k) + cos1179o2c 303 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 302) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_302
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 303 - ((280267/312500 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_303).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_304 : ((185386101/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 304, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 304, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 303, cos1179o2c k) + cos1179o2c 304 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 303) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_303
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 304 - ((-7377543/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_304).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_305 : ((181713659/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 305, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 305, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 304, cos1179o2c k) + cos1179o2c 305 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 304) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_304
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 305 - ((-1835721/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_305).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_306 : ((191711203/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 306, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 306, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 305, cos1179o2c k) + cos1179o2c 306 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 305) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_305
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 306 - ((624909/625000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_306).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_307 : ((94209167/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 307, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 307, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 306, cos1179o2c k) + cos1179o2c 307 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 306) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_306
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 307 - ((-3291869/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_307).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_308 : ((45163077/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 308, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 308, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 307, cos1179o2c k) + cos1179o2c 308 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 307) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_307
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 308 - ((-3882513/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_308).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_309 : ((47295407/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 309, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 309, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 308, cos1179o2c k) + cos1179o2c 309 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 308) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_308
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 309 - ((106629/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_309).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_310 : ((19131557/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 310, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 310, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 309, cos1179o2c k) + cos1179o2c 310 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 309) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_309
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 310 - ((1067471/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_310).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_311 : ((4534449/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 311, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 311, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 310, cos1179o2c k) + cos1179o2c 311 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 310) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_310
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 311 - ((-993661/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_311).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_312 : ((185584467/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 312, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 312, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 311, cos1179o2c k) + cos1179o2c 312 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 311) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_311
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 312 - ((4207507/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_312).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_313 : ((96450599/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 313, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 313, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 312, cos1179o2c k) + cos1179o2c 313 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 312) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_312
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 313 - ((7317731/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_313).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_314 : ((736717/40000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 314, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 314, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 313, cos1179o2c k) + cos1179o2c 314 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 313) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_313
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 314 - ((-2180237/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_314).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_315 : ((91058113/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 315, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 315, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 314, cos1179o2c k) + cos1179o2c 315 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 314) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_314
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 315 - ((-257753/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_315).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_316 : ((96037381/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 316, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 316, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 315, cos1179o2c k) + cos1179o2c 316 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 315) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_315
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 316 - ((622471/625000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_316).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_317 : ((37669719/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 317, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 317, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 316, cos1179o2c k) + cos1179o2c 317 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 316) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_316
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 317 - ((-3725167/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_317).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_318 : ((180494573/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 318, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 318, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 317, cos1179o2c k) + cos1179o2c 318 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 317) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_317
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 318 - ((-3926511/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_318).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_319 : ((47153623/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 319, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 319, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 318, cos1179o2c k) + cos1179o2c 319 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 318) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_318
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 319 - ((8120919/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_319).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_320 : ((192031641/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 320, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 320, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 319, cos1179o2c k) + cos1179o2c 320 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 319) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_319
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 320 - ((3418149/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_320).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_321 : ((182062853/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 321, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 321, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 320, cos1179o2c k) + cos1179o2c 321 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 320) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_320
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 321 - ((-2491947/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_321).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_322 : ((7355069/400000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 322, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 322, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 321, cos1179o2c k) + cos1179o2c 322 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 321) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_321
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 322 - ((226859/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_322).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_323 : ((192924843/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 323, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 323, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 322, cos1179o2c k) + cos1179o2c 323 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 322) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_322
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 323 - ((4524559/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_323).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_324 : ((186550069/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 324, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 324, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 323, cos1179o2c k) + cos1179o2c 324 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 323) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_323
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 324 - ((-3186887/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_324).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_325 : ((180626157/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 325, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 325, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 324, cos1179o2c k) + cos1179o2c 325 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 324) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_324
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 325 - ((-185091/312500 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_325).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_326 : ((189860371/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 326, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 326, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 325, cos1179o2c k) + cos1179o2c 326 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 325) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_325
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 326 - ((4617607/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_326).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_327 : ((47860447/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 327, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 327, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 326, cos1179o2c k) + cos1179o2c 327 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 326) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_326
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 327 - ((1582417/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_327).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_328 : ((181465511/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 328, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 328, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 327, cos1179o2c k) + cos1179o2c 328 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 327) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_327
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 328 - ((-9975277/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_328).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_329 : ((92181327/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 329, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 329, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 328, cos1179o2c k) + cos1179o2c 329 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 328) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_328
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 329 - ((2898143/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_329).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_330 : ((193077799/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 330, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 330, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 329, cos1179o2c k) + cos1179o2c 330 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 329) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_329
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 330 - ((1743229/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_330).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_331 : ((93222109/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 331, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 331, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 330, cos1179o2c k) + cos1179o2c 331 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 330) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_330
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 331 - ((-6632581/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_331).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_332 : ((22560771/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 332, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 332, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 331, cos1179o2c k) + cos1179o2c 332 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 331) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_331
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 332 - ((-119141/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_332).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_333 : ((189549573/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 333, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 333, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 332, cos1179o2c k) + cos1179o2c 333 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 332) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_332
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 333 - ((1812881/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_333).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_334 : ((38383563/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 334, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 334, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 333, cos1179o2c k) + cos1179o2c 334 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 333) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_333
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 334 - ((1184621/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_334).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_335 : ((90964077/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 335, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 335, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 334, cos1179o2c k) + cos1179o2c 335 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 334) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_334
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 335 - ((-9988661/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_335).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_336 : ((45827283/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 336, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 336, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 335, cos1179o2c k) + cos1179o2c 336 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 335) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_335
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 336 - ((690989/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_336).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_337 : ((96400681/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 337, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 337, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 336, cos1179o2c k) + cos1179o2c 337 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 336) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_336
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 337 - ((949323/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_337).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_338 : ((188045167/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 338, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 338, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 337, cos1179o2c k) + cos1179o2c 338 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 337) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_337
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 338 - ((-951039/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_338).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_339 : ((180183139/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 339, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 339, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 338, cos1179o2c k) + cos1179o2c 339 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 338) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_338
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 339 - ((-1965257/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_339).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_340 : ((187574221/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 340, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 340, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 339, cos1179o2c k) + cos1179o2c 340 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 339) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_339
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 340 - ((3696041/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_340).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_341 : ((193040531/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 341, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 341, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 340, cos1179o2c k) + cos1179o2c 341 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 340) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_340
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 341 - ((546731/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_341).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_342 : ((5747531/312500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 342, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 342, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 341, cos1179o2c k) + cos1179o2c 342 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 341) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_341
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 342 - ((-9118539/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_342).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_343 : ((181227131/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 343, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 343, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 342, cos1179o2c k) + cos1179o2c 343 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 342) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_342
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 343 - ((-2692861/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_343).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_344 : ((191145219/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 344, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 344, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 343, cos1179o2c k) + cos1179o2c 344 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 343) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_343
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 344 - ((619943/625000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_344).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_345 : ((11938321/625000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 345, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 345, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 344, cos1179o2c k) + cos1179o2c 345 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 344) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_344
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 345 - ((-131083/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_345).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_346 : ((90561099/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 346, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 346, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 345, cos1179o2c k) + cos1179o2c 346 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 345) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_345
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 346 - ((-4944969/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_346).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_347 : ((18387517/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 347, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 347, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 346, cos1179o2c k) + cos1179o2c 347 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 346) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_346
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 347 - ((688493/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_347).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_348 : ((193066727/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 348, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 348, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 347, cos1179o2c k) + cos1179o2c 348 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 347) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_347
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 348 - ((9192557/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_348).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_349 : ((18805027/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 349, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 349, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 348, cos1179o2c k) + cos1179o2c 349 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 348) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_348
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 349 - ((-5015457/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_349).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_350 : ((180035877/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 350, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 350, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 349, cos1179o2c k) + cos1179o2c 350 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 349) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_349
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 350 - ((-8013393/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_350).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_351 : ((186868599/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 351, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 351, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 350, cos1179o2c k) + cos1179o2c 351 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 350) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_350
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 351 - ((3416861/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_351).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_352 : ((48350561/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 352, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 352, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 351, cos1179o2c k) + cos1179o2c 352 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 351) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_351
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 352 - ((1306929/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_352).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_353 : ((9260409/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 353, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 353, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 352, cos1179o2c k) + cos1179o2c 353 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 352) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_352
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 353 - ((-1024133/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_353).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_354 : ((180292663/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 354, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 354, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 353, cos1179o2c k) + cos1179o2c 354 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 353) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_353
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 354 - ((-4914517/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_354).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_355 : ((94707823/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 355, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 355, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 354, cos1179o2c k) + cos1179o2c 355 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 354) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_354
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 355 - ((9123983/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_355).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_356 : ((192695003/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 356, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 356, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 355, cos1179o2c k) + cos1179o2c 356 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 355) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_355
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 356 - ((3280357/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_356).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_357 : ((45752133/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 357, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 357, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 356, cos1179o2c k) + cos1179o2c 357 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 356) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_356
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 357 - ((-9685471/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_357).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_358 : ((45320751/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 358, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 358, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 357, cos1179o2c k) + cos1179o2c 358 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 357) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_357
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 358 - ((-107783/625000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_358).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_359 : ((191232281/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 359, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 359, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 358, cos1179o2c k) + cos1179o2c 359 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 358) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_358
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 359 - ((9950277/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_359).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_360 : ((191538717/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 360, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 360, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 359, cos1179o2c k) + cos1179o2c 360 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 359) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_359
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 360 - ((76859/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_360).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_361 : ((36308677/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 361, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 361, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 360, cos1179o2c k) + cos1179o2c 361 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 360) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_360
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 361 - ((-2498583/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_361).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_362 : ((182477087/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 362, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 362, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 361, cos1179o2c k) + cos1179o2c 362 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 361) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_361
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 362 - ((467351/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_362).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_363 : ((192365279/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 363, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 363, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 362, cos1179o2c k) + cos1179o2c 363 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 362) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_362
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 363 - ((1236149/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_363).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_364 : ((5949323/312500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 364, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 364, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 363, cos1179o2c k) + cos1179o2c 364 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 363) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_363
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 364 - ((-1985943/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_364).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_365 : ((90339709/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 365, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 365, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 364, cos1179o2c k) + cos1179o2c 365 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 364) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_364
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 365 - ((-4848959/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_365).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_366 : ((7340941/400000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 366, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 366, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 365, cos1179o2c k) + cos1179o2c 366 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 365) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_365
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 366 - ((2845107/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_366).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_367 : ((192995353/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 367, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 367, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 366, cos1179o2c k) + cos1179o2c 367 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 366) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_366
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 367 - ((2368207/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_367).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_368 : ((189476829/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 368, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 368, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 367, cos1179o2c k) + cos1179o2c 368 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 367) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_367
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 368 - ((-879381/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_368).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_369 : ((90110281/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 369, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 369, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 368, cos1179o2c k) + cos1179o2c 369 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 368) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_368
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 369 - ((-9255267/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_369).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_370 : ((9211657/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 370, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 370, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 369, cos1179o2c k) + cos1179o2c 370 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 369) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_369
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 370 - ((2006789/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_370).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_371 : ((193308147/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 371, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 371, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 370, cos1179o2c k) + cos1179o2c 371 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 370) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_370
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 371 - ((9076007/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_371).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_372 : ((188963951/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 372, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 372, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 371, cos1179o2c k) + cos1179o2c 372 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 371) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_371
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 372 - ((-1085799/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_372).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_373 : ((180007129/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 373, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 373, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 372, cos1179o2c k) + cos1179o2c 373 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 372) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_372
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 373 - ((-4477911/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_373).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_374 : ((92260941/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 374, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 374, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 373, cos1179o2c k) + cos1179o2c 374 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 373) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_373
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 374 - ((4515753/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_374).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_375 : ((38685611/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 375, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 375, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 374, cos1179o2c k) + cos1179o2c 375 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 374) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_374
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 375 - ((8907173/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_375).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_376 : ((94444743/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 376, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 376, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 375, cos1179o2c k) + cos1179o2c 376 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 375) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_375
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 376 - ((-4537569/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_376).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_377 : ((44988569/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 377, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 377, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 376, cos1179o2c k) + cos1179o2c 377 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 376) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_376
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 377 - ((-893421/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_377).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_378 : ((92181499/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 378, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 378, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 377, cos1179o2c k) + cos1179o2c 378 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 377) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_377
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 378 - ((2204861/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_378).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_379 : ((96697483/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 379, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 379, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 378, cos1179o2c k) + cos1179o2c 379 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 378) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_378
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 379 - ((1129121/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_379).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_380 : ((189262201/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 380, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 380, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 379, cos1179o2c k) + cos1179o2c 380 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 379) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_379
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 380 - ((-826353/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_380).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_381 : ((90033923/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 381, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 381, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 380, cos1179o2c k) + cos1179o2c 381 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 380) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_380
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 381 - ((-1838671/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_381).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_382 : ((183765537/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 382, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 382, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 381, cos1179o2c k) + cos1179o2c 382 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 381) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_381
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 382 - ((3698691/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_382).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_383 : ((193160999/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 383, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 383, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 382, cos1179o2c k) + cos1179o2c 383 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 382) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_382
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 383 - ((4698231/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_383).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_384 : ((47514067/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 384, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 384, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 383, cos1179o2c k) + cos1179o2c 384 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 383) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_383
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 384 - ((-3103731/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_384).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_385 : ((90219549/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 385, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 385, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 384, cos1179o2c k) + cos1179o2c 385 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 384) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_384
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 385 - ((-961617/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_385).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_386 : ((36555887/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 386, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 386, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 385, cos1179o2c k) + cos1179o2c 386 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 385) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_385
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 386 - ((2341337/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_386).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_387 : ((192597069/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 387, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 387, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 386, cos1179o2c k) + cos1179o2c 387 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 386) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_386
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 387 - ((4909317/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_387).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_388 : ((38237611/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 388, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 388, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 387, cos1179o2c k) + cos1179o2c 388 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 387) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_387
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 388 - ((-704007/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_388).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_389 : ((11326601/625000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 389, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 389, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 388, cos1179o2c k) + cos1179o2c 389 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 388) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_388
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 389 - ((-9961439/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_389).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_390 : ((181529903/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 390, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 390, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 389, cos1179o2c k) + cos1179o2c 390 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 389) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_389
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 390 - ((305287/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_390).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_391 : ((957621/50000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 391, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 391, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 390, cos1179o2c k) + cos1179o2c 391 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 390) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_390
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 391 - ((9995297/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_391).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_392 : ((192478817/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 392, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 392, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 391, cos1179o2c k) + cos1179o2c 392 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 391) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_391
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 392 - ((955617/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_392).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_393 : ((91306469/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 393, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 393, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 392, cos1179o2c k) + cos1179o2c 393 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 392) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_392
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 393 - ((-9864879/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_393).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_394 : ((9013069/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 394, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 394, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 393, cos1179o2c k) + cos1179o2c 394 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 393) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_393
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 394 - ((-1175279/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_394).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_395 : ((189772031/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 395, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 395, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 394, cos1179o2c k) + cos1179o2c 395 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 394) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_394
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 395 - ((9511651/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_395).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_396 : ((193610373/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 396, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 396, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 395, cos1179o2c k) + cos1179o2c 396 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 395) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_395
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 396 - ((1919671/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_396).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_397 : ((184730807/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 397, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 397, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 396, cos1179o2c k) + cos1179o2c 397 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 396) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_396
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 397 - ((-4439283/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_397).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_398 : ((179368363/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 398, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 398, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 397, cos1179o2c k) + cos1179o2c 398 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 397) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_397
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 398 - ((-1340361/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_398).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_399 : ((46820849/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 399, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 399, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 398, cos1179o2c k) + cos1179o2c 399 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 398) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_398
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 399 - ((7916033/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_399).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_400 : ((24264711/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 400, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 400, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 399, cos1179o2c k) + cos1179o2c 400 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 399) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_399
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 400 - ((1708823/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_400).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_401 : ((46881959/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 401, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 401, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 400, cos1179o2c k) + cos1179o2c 401 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 400) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_400
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 401 - ((-1647213/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_401).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_402 : ((448423/25000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 402, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 402, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 401, cos1179o2c k) + cos1179o2c 402 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 401) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_401
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 402 - ((-2039409/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_402).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_403 : ((184254899/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 403, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 403, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 402, cos1179o2c k) + cos1179o2c 403 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 402) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_402
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 403 - ((4886699/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_403).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_404 : ((193461679/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 404, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 404, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 403, cos1179o2c k) + cos1179o2c 404 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 403) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_403
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 404 - ((460389/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_404).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_405 : ((190627119/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 405, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 405, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 404, cos1179o2c k) + cos1179o2c 405 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 404) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_404
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 405 - ((-70839/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_405).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_406 : ((90385357/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 406, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 406, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 405, cos1179o2c k) + cos1179o2c 406 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 405) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_405
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 406 - ((-1971081/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_406).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_407 : ((9063293/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 407, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 407, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 406, cos1179o2c k) + cos1179o2c 407 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 406) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_406
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 407 - ((248073/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_407).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_408 : ((191237101/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 408, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 408, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 407, cos1179o2c k) + cos1179o2c 408 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 407) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_407
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 408 - ((9972241/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_408).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_409 : ((24155579/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 409, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 409, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 408, cos1179o2c k) + cos1179o2c 409 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 408) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_408
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 409 - ((2008531/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_409).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_410 : ((183794497/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 410, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 410, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 409, cos1179o2c k) + cos1179o2c 410 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 409) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_409
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 410 - ((-1889827/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_410).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_411 : ((22410107/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 411, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 411, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 410, cos1179o2c k) + cos1179o2c 411 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 410) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_410
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 411 - ((-4512641/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_411).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_412 : ((93748357/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 412, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 412, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 411, cos1179o2c k) + cos1179o2c 412 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 411) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_411
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 412 - ((4108429/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_412).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_413 : ((97149329/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 413, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 413, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 412, cos1179o2c k) + cos1179o2c 413 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 412) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_412
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 413 - ((53148/78125 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_413).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_414 : ((94014661/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 414, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 414, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 413, cos1179o2c k) + cos1179o2c 414 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 413) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_413
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 414 - ((-391771/625000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_414).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_415 : ((89697383/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 415, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 415, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 414, cos1179o2c k) + cos1179o2c 415 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 414) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_414
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 415 - ((-2158389/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_415).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_416 : ((183073861/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 416, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 416, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 415, cos1179o2c k) + cos1179o2c 416 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 415) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_415
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 416 - ((736019/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_416).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_417 : ((96414319/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 417, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 417, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 416, cos1179o2c k) + cos1179o2c 417 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 416) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_416
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 417 - ((9755777/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_417).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_418 : ((96100851/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 418, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 418, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 417, cos1179o2c k) + cos1179o2c 418 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 417) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_417
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 418 - ((-39121/625000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_418).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_419 : ((91125107/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 419, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 419, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 418, cos1179o2c k) + cos1179o2c 419 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 418) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_418
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 419 - ((-1243811/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_419).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_420 : ((89814589/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 420, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 420, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 419, cos1179o2c k) + cos1179o2c 420 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 419) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_419
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 420 - ((-655009/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_420).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_421 : ((188701071/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 421, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 421, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 420, cos1179o2c k) + cos1179o2c 421 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 420) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_420
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 421 - ((9072893/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_421).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_422 : ((97198827/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 422, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 422, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 421, cos1179o2c k) + cos1179o2c 422 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 421) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_421
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 422 - ((5697583/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_422).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_423 : ((46825011/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 423, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 423, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 422, cos1179o2c k) + cos1179o2c 423 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 422) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_422
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 423 - ((-709661/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_423).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_424 : ((179103749/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 424, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 424, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 423, cos1179o2c k) + cos1179o2c 424 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 423) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_423
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 424 - ((-1639059/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_424).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_425 : ((183254141/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 425, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 425, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 424, cos1179o2c k) + cos1179o2c 425 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 424) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_424
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 425 - ((129731/312500 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_425).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_426 : ((96479983/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 426, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 426, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 425, cos1179o2c k) + cos1179o2c 426 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 425) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_425
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 426 - ((388273/400000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_426).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_427 : ((48104441/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 427, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 427, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 426, cos1179o2c k) + cos1179o2c 427 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 426) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_426
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 427 - ((-270601/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_427).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_428 : ((18251149/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 428, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 428, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 427, cos1179o2c k) + cos1179o2c 428 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 427) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_427
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 428 - ((-4952637/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_428).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_429 : ((179243853/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 429, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 429, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 428, cos1179o2c k) + cos1179o2c 429 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 428) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_428
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 429 - ((-3266637/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_429).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_430 : ((187865687/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 430, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 430, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 429, cos1179o2c k) + cos1179o2c 430 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 429) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_429
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 430 - ((4311417/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_430).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_431 : ((97276147/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 431, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 431, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 430, cos1179o2c k) + cos1179o2c 431 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 430) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_430
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 431 - ((6687607/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_431).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_432 : ((188630589/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 432, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 432, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 431, cos1179o2c k) + cos1179o2c 432 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 431) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_431
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 432 - ((-1184141/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_432).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_433 : ((179522797/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 433, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 433, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 432, cos1179o2c k) + cos1179o2c 433 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 432) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_432
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 433 - ((-1138349/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_433).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_434 : ((181654621/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 434, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 434, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 433, cos1179o2c k) + cos1179o2c 434 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 433) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_433
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 434 - ((266603/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_434).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_435 : ((191653617/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 435, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 435, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 434, cos1179o2c k) + cos1179o2c 435 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 434) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_434
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 435 - ((2499999/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_435).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_436 : ((193798937/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 436, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 436, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 435, cos1179o2c k) + cos1179o2c 436 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 435) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_435
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 436 - ((26829/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_436).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_437 : ((1847361/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 437, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 437, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 436, cos1179o2c k) + cos1179o2c 437 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 436) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_436
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 437 - ((-9061837/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_437).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_438 : ((89302191/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 438, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 438, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 437, cos1179o2c k) + cos1179o2c 438 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 437) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_437
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 438 - ((-3065359/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_438).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_439 : ((36985111/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 439, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 439, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 438, cos1179o2c k) + cos1179o2c 439 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 438) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_438
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 439 - ((6322173/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_439).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_440 : ((1514903/78125 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 440, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 440, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 439, cos1179o2c k) + cos1179o2c 440 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 439) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_439
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 440 - ((8983029/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_440).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_441 : ((47925383/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 441, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 441, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 440, cos1179o2c k) + cos1179o2c 441 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 440) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_440
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 441 - ((-551263/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_441).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_442 : ((181701409/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 442, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 442, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 441, cos1179o2c k) + cos1179o2c 442 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 441) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_441
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 442 - ((-9999123/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_442).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_443 : ((1433669/80000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 443, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 443, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 442, cos1179o2c k) + cos1179o2c 443 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 442) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_442
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 443 - ((-311473/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_443).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_444 : ((18801479/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 444, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 444, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 443, cos1179o2c k) + cos1179o2c 444 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 443) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_443
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 444 - ((1761433/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_444).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_445 : ((97371023/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 445, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 445, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 444, cos1179o2c k) + cos1179o2c 445 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 444) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_444
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 445 - ((105129/156250 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_445).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_446 : ((189217143/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 446, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 446, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 445, cos1179o2c k) + cos1179o2c 446 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 445) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_445
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 446 - ((-5523903/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_446).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_447 : ((89885489/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 447, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 447, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 446, cos1179o2c k) + cos1179o2c 447 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 446) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_446
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 447 - ((-1889033/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_447).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_448 : ((180581447/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 448, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 448, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 447, cos1179o2c k) + cos1179o2c 448 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 447) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_447
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 448 - ((811469/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_448).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_449 : ((38085469/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 449, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 449, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 448, cos1179o2c k) + cos1179o2c 449 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 448) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_448
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 449 - ((4923449/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_449).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_450 : ((194636337/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 450, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 450, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 449, cos1179o2c k) + cos1179o2c 450 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 449) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_449
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 450 - ((526249/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_450).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_451 : ((23370769/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 451, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 451, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 450, cos1179o2c k) + cos1179o2c 451 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 450) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_450
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 451 - ((-1533837/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_451).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_452 : ((178762111/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 452, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 452, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 451, cos1179o2c k) + cos1179o2c 452 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 451) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_451
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 452 - ((-8203041/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_452).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_453 : ((182104017/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 453, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 453, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 452, cos1179o2c k) + cos1179o2c 453 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 452) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_452
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 453 - ((1671453/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_453).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_454 : ((96039297/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 454, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 454, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 453, cos1179o2c k) + cos1179o2c 454 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 453) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_453
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 454 - ((9975577/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_454).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_455 : ((194101671/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 455, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 455, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 454, cos1179o2c k) + cos1179o2c 455 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 454) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_454
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 455 - ((2024077/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_455).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_456 : ((4630817/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 456, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 456, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 455, cos1179o2c k) + cos1179o2c 456 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 455) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_455
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 456 - ((-8867991/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_456).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_457 : ((89171521/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 457, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 457, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 456, cos1179o2c k) + cos1179o2c 457 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 456) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_456
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 457 - ((-3444319/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_457).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_458 : ((36677073/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 458, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 458, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 457, cos1179o2c k) + cos1179o2c 458 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 457) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_457
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 458 - ((5043323/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_458).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_459 : ((38617839/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 459, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 459, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 458, cos1179o2c k) + cos1179o2c 459 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 458) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_458
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 459 - ((970483/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_459).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_460 : ((96765803/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 460, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 460, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 459, cos1179o2c k) + cos1179o2c 460 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 459) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_459
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 460 - ((443411/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_460).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_461 : ((184086483/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 461, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 461, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 460, cos1179o2c k) + cos1179o2c 461 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 460) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_460
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 461 - ((-9444123/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_461).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_462 : ((178206473/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 462, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 462, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 461, cos1179o2c k) + cos1179o2c 462 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 461) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_461
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 462 - ((-587901/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_462).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_463 : ((92113343/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 463, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 463, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 462, cos1179o2c k) + cos1179o2c 463 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 462) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_462
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 463 - ((6021213/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_463).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_464 : ((193628959/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 464, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 464, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 463, cos1179o2c k) + cos1179o2c 464 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 463) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_463
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 464 - ((9403273/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_464).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_465 : ((193172681/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 465, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 465, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 464, cos1179o2c k) + cos1179o2c 465 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 464) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_464
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 465 - ((-227639/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_465).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_466 : ((183504931/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 466, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 466, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 465, cos1179o2c k) + cos1179o2c 466 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 465) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_465
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 466 - ((-38667/40000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_466).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_467 : ((178141051/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 467, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 467, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 466, cos1179o2c k) + cos1179o2c 467 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 466) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_466
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 467 - ((-16759/31250 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_467).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_468 : ((36908639/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 468, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 468, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 467, cos1179o2c k) + cos1179o2c 468 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 467) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_467
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 468 - ((800393/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_468).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_469 : ((193819917/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 469, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 469, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 468, cos1179o2c k) + cos1179o2c 469 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 468) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_468
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 469 - ((4638861/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_469).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_470 : ((48286909/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 470, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 470, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 469, cos1179o2c k) + cos1179o2c 470 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 469) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_469
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 470 - ((-671281/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_470).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_471 : ((5733101/312500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 471, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 471, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 470, cos1179o2c k) + cos1179o2c 471 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 470) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_470
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 471 - ((-2421851/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_471).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_472 : ((178051643/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 472, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 472, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 471, cos1179o2c k) + cos1179o2c 472 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 471) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_471
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 472 - ((-5406589/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_472).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_473 : ((184310521/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 473, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 473, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 472, cos1179o2c k) + cos1179o2c 473 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 472) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_472
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 473 - ((3129939/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_473).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_474 : ((96850551/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 474, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 474, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 473, cos1179o2c k) + cos1179o2c 474 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 473) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_473
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 474 - ((9391581/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_474).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_475 : ((96739059/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 475, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 475, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 474, cos1179o2c k) + cos1179o2c 475 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 474) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_474
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 475 - ((-6937/312500 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_475).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_476 : ((45987591/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 476, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 476, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 475, cos1179o2c k) + cos1179o2c 476 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 475) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_475
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 476 - ((-4763377/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_476).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_477 : ((177956981/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 477, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 477, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 476, cos1179o2c k) + cos1179o2c 477 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 476) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_476
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 477 - ((-5992383/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_477).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_478 : ((22942067/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 478, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 478, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 477, cos1179o2c k) + cos1179o2c 478 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 477) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_477
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 478 - ((1116111/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_478).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_479 : ((9660837/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 479, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 479, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 478, cos1179o2c k) + cos1179o2c 479 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 478) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_478
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 479 - ((2420301/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_479).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_480 : ((24262017/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 480, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 480, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 479, cos1179o2c k) + cos1179o2c 480 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 479) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_479
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 480 - ((220099/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_480).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_481 : ((185014427/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 481, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 481, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 480, cos1179o2c k) + cos1179o2c 481 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 480) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_480
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 481 - ((-9080709/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_481).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_482 : ((88995277/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 482, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 482, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 481, cos1179o2c k) + cos1179o2c 482 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 481) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_481
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 482 - ((-7022873/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_482).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_483 : ((182277277/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 483, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 483, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 482, cos1179o2c k) + cos1179o2c 483 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 482) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_482
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 483 - ((4287723/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_483).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_484 : ((96117177/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 484, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 484, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 483, cos1179o2c k) + cos1179o2c 484 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 483) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_483
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 484 - ((9958077/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_484).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_485 : ((6088393/312500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 485, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 485, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 484, cos1179o2c k) + cos1179o2c 485 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 484) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_484
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 485 - ((1297611/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_485).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_486 : ((186683401/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 486, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 486, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 485, cos1179o2c k) + cos1179o2c 486 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 485) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_485
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 486 - ((-325767/400000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_486).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_487 : ((89193871/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 487, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 487, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 486, cos1179o2c k) + cos1179o2c 487 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 486) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_486
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 487 - ((-8294659/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_487).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_488 : ((36135427/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 488, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 488, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 487, cos1179o2c k) + cos1179o2c 488 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 487) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_487
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 488 - ((2290393/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_488).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_489 : ((190587821/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 489, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 489, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 488, cos1179o2c k) + cos1179o2c 489 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 488) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_488
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 489 - ((4955843/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_489).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_490 : ((9768837/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 490, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 490, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 489, cos1179o2c k) + cos1179o2c 490 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 489) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_489
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 490 - ((4789919/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_490).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_491 : ((4722887/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 491, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 491, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 490, cos1179o2c k) + cos1179o2c 491 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 490) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_490
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 491 - ((-323013/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_491).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_492 : ((35891439/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 492, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 492, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 491, cos1179o2c k) + cos1179o2c 492 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 491) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_491
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 492 - ((-1891457/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_492).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_493 : ((89513621/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 493, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 493, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 492, cos1179o2c k) + cos1179o2c 493 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 492) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_492
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 493 - ((-428953/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_493).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_494 : ((94080313/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 494, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 494, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 493, cos1179o2c k) + cos1179o2c 494 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 493) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_493
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 494 - ((570899/625000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_494).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_495 : ((97659101/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 495, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 495, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 494, cos1179o2c k) + cos1179o2c 495 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 494) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_494
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 495 - ((447411/625000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_495).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_496 : ((4787449/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 496, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 496, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 495, cos1179o2c k) + cos1179o2c 496 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 495) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_495
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 496 - ((-1909621/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_496).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_497 : ((5671791/312500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 497, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 497, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 496, cos1179o2c k) + cos1179o2c 497 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 496) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_496
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 497 - ((-312489/312500 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_497).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_498 : ((177810259/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 498, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 498, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 497, cos1179o2c k) + cos1179o2c 498 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 497) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_497
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 498 - ((-3686053/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_498).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_499 : ((37003553/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 499, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 499, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 498, cos1179o2c k) + cos1179o2c 499 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 498) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_498
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 499 - ((3604253/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_499).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_500 : ((1941703/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 500, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 500, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 499, cos1179o2c k) + cos1179o2c 500 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 499) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_499
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 500 - ((1830707/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_500).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_501 : ((193954367/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 501, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 501, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 500, cos1179o2c k) + cos1179o2c 501 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 500) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_500
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 501 - ((-214933/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_501).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_502 : ((92322021/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 502, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 502, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 501, cos1179o2c k) + cos1179o2c 502 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 501) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_501
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 502 - ((-372373/400000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_502).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_503 : ((44417679/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 503, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 503, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 502, cos1179o2c k) + cos1179o2c 503 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 502) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_502
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 503 - ((-3486163/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_503).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_504 : ((181557233/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 504, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 504, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 503, cos1179o2c k) + cos1179o2c 504 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 503) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_503
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 504 - ((3887517/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_504).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_505 : ((47889047/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 505, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 505, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 504, cos1179o2c k) + cos1179o2c 505 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 504) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_504
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 505 - ((1999991/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_505).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_506 : ((39103963/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 506, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 506, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 505, cos1179o2c k) + cos1179o2c 506 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 505) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_505
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 506 - ((3964627/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_506).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_507 : ((188656843/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 507, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 507, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 506, cos1179o2c k) + cos1179o2c 507 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 506) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_506
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 507 - ((-1715493/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_507).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_508 : ((179251881/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 508, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 508, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 507, cos1179o2c k) + cos1179o2c 508 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 507) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_507
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 508 - ((-4701981/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_508).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_509 : ((178606499/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 509, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 509, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 508, cos1179o2c k) + cos1179o2c 509 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 508) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_508
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 509 - ((-322191/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_509).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_510 : ((37496687/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 510, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 510, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 509, cos1179o2c k) + cos1179o2c 510 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 509) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_509
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 510 - ((554871/625000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_510).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_511 : ((97640233/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 511, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 511, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 510, cos1179o2c k) + cos1179o2c 511 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 510) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_510
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 511 - ((7798031/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_511).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_512 : ((48181563/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 512, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 512, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 511, cos1179o2c k) + cos1179o2c 512 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 511) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_511
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 512 - ((-1276607/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_512).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_513 : ((36571361/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 513, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 513, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 512, cos1179o2c k) + cos1179o2c 513 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 512) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_512
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 513 - ((-9868447/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_513).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_514 : ((88666123/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 514, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 514, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 513, cos1179o2c k) + cos1179o2c 514 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 513) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_513
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 514 - ((-5523559/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_514).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_515 : ((45662097/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 515, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 515, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 514, cos1179o2c k) + cos1179o2c 515 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 514) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_514
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 515 - ((2658571/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_515).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_516 : ((192558623/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 516, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 516, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 515, cos1179o2c k) + cos1179o2c 516 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 515) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_515
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 516 - ((1982247/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_516).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_517 : ((48868949/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 517, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 517, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 516, cos1179o2c k) + cos1179o2c 517 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 516) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_516
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 517 - ((2918173/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_517).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_518 : ((94004109/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 518, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 518, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 517, cos1179o2c k) + cos1179o2c 518 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 517) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_517
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 518 - ((-3733289/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_518).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_519 : ((178832573/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 519, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 519, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 518, cos1179o2c k) + cos1179o2c 519 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 518) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_518
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 519 - ((-1834929/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_519).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_520 : ((89281443/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 520, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 520, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 519, cos1179o2c k) + cos1179o2c 520 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 519) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_519
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 520 - ((-268687/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_520).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_521 : ((4687489/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 521, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 521, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 520, cos1179o2c k) + cos1179o2c 521 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 520) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_520
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 521 - ((4468837/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_521).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_522 : ((195366213/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 522, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 522, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 521, cos1179o2c k) + cos1179o2c 522 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 521) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_521
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 522 - ((7867653/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_522).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_523 : ((96578321/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 523, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 523, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 522, cos1179o2c k) + cos1179o2c 523 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 522) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_522
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 523 - ((-2208571/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_523).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_524 : ((9170057/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 524, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 524, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 523, cos1179o2c k) + cos1179o2c 524 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 523) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_523
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 524 - ((-4877251/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_524).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_525 : ((88599469/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 525, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 525, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 524, cos1179o2c k) + cos1179o2c 525 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 524) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_524
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 525 - ((-3100601/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_525).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_526 : ((181573891/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 526, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 526, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 525, cos1179o2c k) + cos1179o2c 526 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 525) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_525
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 526 - ((4375953/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_526).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_527 : ((1532583/80000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 527, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 527, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 526, cos1179o2c k) + cos1179o2c 527 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 526) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_526
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 527 - ((624999/625000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_527).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_528 : ((19593519/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 528, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 528, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 527, cos1179o2c k) + cos1179o2c 528 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 527) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_527
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 528 - ((872663/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_528).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_529 : ((47442997/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 529, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 529, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 528, cos1179o2c k) + cos1179o2c 529 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 528) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_528
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 529 - ((-3081101/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_529).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_530 : ((11248961/625000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 530, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 530, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 529, cos1179o2c k) + cos1179o2c 530 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 529) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_529
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 530 - ((-2446903/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_530).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_531 : ((44369527/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 531, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 531, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 530, cos1179o2c k) + cos1179o2c 531 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 530) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_530
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 531 - ((-626067/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_531).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_532 : ((185029141/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 532, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 532, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 531, cos1179o2c k) + cos1179o2c 532 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 531) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_531
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 532 - ((7552033/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_532).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_533 : ((97134329/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 533, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 533, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 532, cos1179o2c k) + cos1179o2c 533 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 532) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_532
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 533 - ((9240517/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_533).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_534 : ((195002881/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 534, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 534, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 533, cos1179o2c k) + cos1179o2c 534 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 533) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_533
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 534 - ((735223/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_534).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_535 : ((93216231/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 535, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 535, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 534, cos1179o2c k) + cos1179o2c 535 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 534) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_534
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 535 - ((-8569419/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_535).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_536 : ((88977711/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 536, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 536, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 535, cos1179o2c k) + cos1179o2c 536 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 535) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_535
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 536 - ((-211901/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_536).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_537 : ((178826469/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 537, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 537, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 536, cos1179o2c k) + cos1179o2c 537 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 536) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_536
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 537 - ((872047/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_537).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_538 : ((37617399/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 538, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 538, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 537, cos1179o2c k) + cos1179o2c 538 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 537) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_537
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 538 - ((4630763/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_538).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_539 : ((19568273/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 539, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 539, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 538, cos1179o2c k) + cos1179o2c 539 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 538) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_538
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 539 - ((1519347/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_539).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_540 : ((193403061/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 540, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 540, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 539, cos1179o2c k) + cos1179o2c 540 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 539) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_539
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 540 - ((-2278669/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_540).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_541 : ((9185681/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 541, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 541, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 540, cos1179o2c k) + cos1179o2c 541 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 540) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_540
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 541 - ((-9688441/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_541).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_542 : ((177026179/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 542, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 542, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 541, cos1179o2c k) + cos1179o2c 542 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 541) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_541
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 542 - ((-6686441/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_542).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_543 : ((180493971/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 543, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 543, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 542, cos1179o2c k) + cos1179o2c 543 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 542) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_542
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 543 - ((433599/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_543).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_544 : ((38081213/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 544, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 544, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 543, cos1179o2c k) + cos1179o2c 544 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 543) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_543
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 544 - ((4956547/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_544).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_545 : ((98108169/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 545, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 545, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 544, cos1179o2c k) + cos1179o2c 545 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 544) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_544
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 545 - ((5811273/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_545).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_546 : ((23971357/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 546, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 546, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 545, cos1179o2c k) + cos1179o2c 546 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 545) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_545
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 546 - ((-2222241/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_546).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_547 : ((181774821/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 547, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 547, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 546, cos1179o2c k) + cos1179o2c 547 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 546) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_546
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 547 - ((-1999007/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_547).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_548 : ((35351221/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 548, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 548, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 547, cos1179o2c k) + cos1179o2c 548 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 547) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_547
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 548 - ((-1254429/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_548).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_549 : ((36394913/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 549, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 549, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 548, cos1179o2c k) + cos1179o2c 549 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 548) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_548
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 549 - ((260973/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_549).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_550 : ((47990127/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 550, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 550, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 549, cos1179o2c k) + cos1179o2c 550 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 549) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_549
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 550 - ((9986943/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_550).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_551 : ((24537299/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 551, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 551, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 550, cos1179o2c k) + cos1179o2c 551 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 550) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_550
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 551 - ((1084721/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_551).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_552 : ((190486411/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 552, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 552, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 551, cos1179o2c k) + cos1179o2c 552 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 551) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_551
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 552 - ((-5810981/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_552).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_553 : ((36110587/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 553, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 553, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 552, cos1179o2c k) + cos1179o2c 553 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 552) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_552
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 553 - ((-2483119/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_553).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_554 : ((176754401/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 554, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 554, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 553, cos1179o2c k) + cos1179o2c 554 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 553) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_553
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 554 - ((-1898767/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_554).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_555 : ((182991701/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 555, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 555, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 554, cos1179o2c k) + cos1179o2c 555 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 554) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_554
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 555 - ((62383/100000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_555).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_556 : ((12053533/625000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 556, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 556, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 555, cos1179o2c k) + cos1179o2c 556 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 555) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_555
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 556 - ((9865827/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_556).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_557 : ((49065179/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 557, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 557, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 556, cos1179o2c k) + cos1179o2c 557 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 556) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_556
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 557 - ((851297/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_557).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_558 : ((47435501/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 558, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 558, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 557, cos1179o2c k) + cos1179o2c 558 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 557) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_557
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 558 - ((-407357/625000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_558).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_559 : ((89964897/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 559, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 559, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 558, cos1179o2c k) + cos1179o2c 559 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 558) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_558
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 559 - ((-981121/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_559).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_560 : ((176758819/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 560, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 560, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 559, cos1179o2c k) + cos1179o2c 560 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 559) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_559
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 560 - ((-126799/400000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_560).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_561 : ((18342073/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 561, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 561, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 560, cos1179o2c k) + cos1179o2c 561 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 560) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_560
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 561 - ((6662911/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_561).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_562 : ((38640727/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 562, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 562, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 561, cos1179o2c k) + cos1179o2c 562 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 561) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_561
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 562 - ((1956781/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_562).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_563 : ((196296189/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 563, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 563, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 562, cos1179o2c k) + cos1179o2c 563 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 562) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_562
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 563 - ((1546777/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_563).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_564 : ((47403623/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 564, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 564, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 563, cos1179o2c k) + cos1179o2c 564 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 563) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_563
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 564 - ((-6680697/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_564).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_565 : ((35964623/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 565, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 565, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 564, cos1179o2c k) + cos1179o2c 565 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 564) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_564
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 565 - ((-9790377/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_565).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_566 : ((44161359/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 566, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 566, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 565, cos1179o2c k) + cos1179o2c 566 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 565) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_565
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 566 - ((-3176679/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_566).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_567 : ((5725579/312500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 567, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 567, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 566, cos1179o2c k) + cos1179o2c 567 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 566) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_566
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 567 - ((1643523/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_567).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_568 : ((19304627/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 568, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 568, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 567, cos1179o2c k) + cos1179o2c 568 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 567) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_567
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 568 - ((4914371/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_568).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_569 : ((24557553/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 569, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 569, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 568, cos1179o2c k) + cos1179o2c 569 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 568) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_568
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 569 - ((1707577/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_569).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_570 : ((190120511/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 570, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 570, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 569, cos1179o2c k) + cos1179o2c 570 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 569) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_569
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 570 - ((-6338913/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_570).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_571 : ((90115239/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 571, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 571, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 570, cos1179o2c k) + cos1179o2c 571 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 570) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_570
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 571 - ((-9889033/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_571).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_572 : ((88212707/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 572, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 572, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 571, cos1179o2c k) + cos1179o2c 572 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 571) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_571
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 572 - ((-118877/312500 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_572).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_573 : ((9119619/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 573, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 573, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 572, cos1179o2c k) + cos1179o2c 573 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 572) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_572
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 573 - ((2983983/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_573).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_574 : ((96172399/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 574, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 574, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 573, cos1179o2c k) + cos1179o2c 574 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 573) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_573
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 574 - ((4976709/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_574).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_575 : ((196676291/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 575, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 575, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 574, cos1179o2c k) + cos1179o2c 575 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 574) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_574
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 575 - ((4332493/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_575).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_576 : ((191226707/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 576, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 576, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 575, cos1179o2c k) + cos1179o2c 576 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 575) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_575
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 576 - ((-681073/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_576).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_577 : ((181229619/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 577, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 577, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 576, cos1179o2c k) + cos1179o2c 577 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 576) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_576
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 577 - ((-1249511/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_577).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_578 : ((8812103/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 578, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 578, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 577, cos1179o2c k) + cos1179o2c 578 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 577) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_577
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 578 - ((-4986559/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_578).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_579 : ((90504317/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 579, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 579, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 578, cos1179o2c k) + cos1179o2c 579 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 578) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_578
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 579 - ((2383787/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_579).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_580 : ((95495829/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 580, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 580, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 579, cos1179o2c k) + cos1179o2c 580 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 579) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_579
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 580 - ((1248003/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_580).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_581 : ((196734549/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 581, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 581, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 580, cos1179o2c k) + cos1179o2c 581 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 580) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_580
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 581 - ((5743891/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_581).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_582 : ((192821821/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 582, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 582, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 581, cos1179o2c k) + cos1179o2c 582 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 581) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_581
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 582 - ((-244483/625000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_582).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_583 : ((182943651/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 583, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 583, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 582, cos1179o2c k) + cos1179o2c 583 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 582) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_582
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 583 - ((-987717/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_583).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_584 : ((88184159/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 584, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 584, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 583, cos1179o2c k) + cos1179o2c 584 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 583) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_583
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 584 - ((-6574333/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_584).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_585 : ((179238033/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 585, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 585, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 584, cos1179o2c k) + cos1179o2c 585 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 584) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_584
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 585 - ((574143/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_585).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_586 : ((188867179/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 586, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 586, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 585, cos1179o2c k) + cos1179o2c 586 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 585) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_585
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 586 - ((4815073/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_586).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_587 : ((196302329/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 587, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 587, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 586, cos1179o2c k) + cos1179o2c 587 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 586) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_586
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 587 - ((148723/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_587).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_588 : ((97329763/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 588, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 588, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 587, cos1179o2c k) + cos1179o2c 588 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 587) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_587
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 588 - ((-1641803/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_588).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_589 : ((185464317/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 589, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 589, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 588, cos1179o2c k) + cos1179o2c 589 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 588) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_588
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 589 - ((-9194209/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_589).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_590 : ((88593263/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 590, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 590, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 589, cos1179o2c k) + cos1179o2c 590 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 589) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_589
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 590 - ((-8276791/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_590).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_591 : ((177419093/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 591, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 591, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 590, cos1179o2c k) + cos1179o2c 591 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 590) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_590
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 591 - ((233567/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_591).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_592 : ((185939003/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 592, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 592, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 591, cos1179o2c k) + cos1179o2c 592 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 591) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_591
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 592 - ((852091/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_592).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_593 : ((48742027/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 593, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 593, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 592, cos1179o2c k) + cos1179o2c 593 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 592) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_592
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 593 - ((1806021/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_593).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_594 : ((98148669/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 594, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 594, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 593, cos1179o2c k) + cos1179o2c 594 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 593) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_593
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 594 - ((133023/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_594).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_595 : ((188729803/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 595, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 595, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 594, cos1179o2c k) + cos1179o2c 595 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 594) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_594
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 595 - ((-1513307/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_595).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_596 : ((22388843/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 596, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 596, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 595, cos1179o2c k) + cos1179o2c 596 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 595) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_595
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 596 - ((-9618059/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_596).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_597 : ((176104637/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 597, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 597, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 596, cos1179o2c k) + cos1179o2c 597 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 596) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_596
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 597 - ((-3005107/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_597).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_598 : ((18240213/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 598, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 598, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 597, cos1179o2c k) + cos1179o2c 598 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 597) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_597
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 598 - ((6298493/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_598).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_599 : ((48088891/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 599, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 599, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 598, cos1179o2c k) + cos1179o2c 599 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 598) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_598
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 599 - ((4977217/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_599).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_600 : ((197078037/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 600, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 600, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 599, cos1179o2c k) + cos1179o2c 600 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 599) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_599
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 600 - ((4723473/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_600).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_601 : ((192373051/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 601, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 601, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 600, cos1179o2c k) + cos1179o2c 601 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 600) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_600
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 601 - ((-2351993/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_601).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_602 : ((182423023/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 602, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 602, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 601, cos1179o2c k) + cos1179o2c 602 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 601) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_601
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 602 - ((-2487257/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_602).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_603 : ((176030363/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 603, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 603, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 602, cos1179o2c k) + cos1179o2c 603 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 602) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_602
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 603 - ((-319583/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_603).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_604 : ((35765093/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 604, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 604, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 603, cos1179o2c k) + cos1179o2c 604 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 603) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_603
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 604 - ((1398051/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_604).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_605 : ((11771317/625000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 605, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 605, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 604, cos1179o2c k) + cos1179o2c 605 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 604) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_604
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 605 - ((9516607/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_605).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_606 : ((196231643/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 606, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 606, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 605, cos1179o2c k) + cos1179o2c 606 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 605) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_605
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 606 - ((7891571/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_606).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_607 : ((195605729/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 607, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 607, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 606, cos1179o2c k) + cos1179o2c 607 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 606) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_606
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 607 - ((-312457/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_607).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_608 : ((46754201/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 608, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 608, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 607, cos1179o2c k) + cos1179o2c 608 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 607) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_607
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 608 - ((-343517/400000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_608).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_609 : ((88964943/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 609, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 609, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 608, cos1179o2c k) + cos1179o2c 609 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 608) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_608
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 609 - ((-4542959/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_609).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_610 : ((11013149/625000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 610, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 610, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 609, cos1179o2c k) + cos1179o2c 610 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 609) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_609
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 610 - ((-859251/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_610).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_611 : ((45833313/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 611, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 611, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 610, cos1179o2c k) + cos1179o2c 611 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 610) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_610
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 611 - ((1780967/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_611).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_612 : ((193159573/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 612, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 612, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 611, cos1179o2c k) + cos1179o2c 612 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 611) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_611
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 612 - ((9827321/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_612).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_613 : ((24657047/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 613, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 613, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 612, cos1179o2c k) + cos1179o2c 613 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 612) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_612
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 613 - ((4097803/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_613).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_614 : ((192125413/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 614, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 614, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 613, cos1179o2c k) + cos1179o2c 614 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 613) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_613
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 614 - ((-5129963/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_614).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_615 : ((182150923/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 615, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 615, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 614, cos1179o2c k) + cos1179o2c 615 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 614) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_614
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 615 - ((-997349/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_615).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_616 : ((87908241/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 616, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 616, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 615, cos1179o2c k) + cos1179o2c 616 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 615) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_615
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 616 - ((-6333441/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_616).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_617 : ((44621569/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 617, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 617, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 616, cos1179o2c k) + cos1179o2c 617 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 616) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_616
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 617 - ((1335397/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_617).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_618 : ((7515733/400000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 618, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 618, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 617, cos1179o2c k) + cos1179o2c 618 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 617) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_617
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 618 - ((9408049/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_618).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_619 : ((24513027/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 619, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 619, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 618, cos1179o2c k) + cos1179o2c 619 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 618) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_618
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 619 - ((8211891/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_619).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_620 : ((196222421/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 620, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 620, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 619, cos1179o2c k) + cos1179o2c 620 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 619) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_619
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 620 - ((23841/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_620).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_621 : ((188156957/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 621, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 621, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 620, cos1179o2c k) + cos1179o2c 621 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 620) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_620
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 621 - ((-504029/625000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_621).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_622 : ((178650557/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 622, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 622, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 621, cos1179o2c k) + cos1179o2c 622 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 621) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_621
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 622 - ((-47527/50000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_622).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_623 : ((87809307/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 623, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 623, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 622, cos1179o2c k) + cos1179o2c 623 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 622) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_622
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 623 - ((-3030943/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_623).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_624 : ((90784757/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 624, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 624, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 623, cos1179o2c k) + cos1179o2c 624 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 623) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_623
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 624 - ((59519/100000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_624).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_625 : ((38313589/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 625, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 625, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 624, cos1179o2c k) + cos1179o2c 625 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 624) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_624
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 625 - ((9999431/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_625).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_626 : ((39471697/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 626, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 626, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 625, cos1179o2c k) + cos1179o2c 626 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 625) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_625
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 626 - ((289577/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_626).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_627 : ((97090401/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 627, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 627, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 626, cos1179o2c k) + cos1179o2c 627 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 626) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_626
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 627 - ((-3176683/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_627).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_628 : ((184650687/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 628, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 628, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 627, cos1179o2c k) + cos1179o2c 628 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 627) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_627
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 628 - ((-1905823/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_628).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_629 : ((3531371/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 629, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 629, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 628, cos1179o2c k) + cos1179o2c 629 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 628) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_628
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 629 - ((-8081137/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_629).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_630 : ((176522921/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 630, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 630, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 629, cos1179o2c k) + cos1179o2c 630 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 629) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_629
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 630 - ((-44629/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_630).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_631 : ((184541013/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 631, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 631, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 630, cos1179o2c k) + cos1179o2c 631 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 630) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_630
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 631 - ((2004773/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_631).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_632 : ((38822673/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 632, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 632, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 631, cos1179o2c k) + cos1179o2c 632 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 631) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_631
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 632 - ((1196669/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_632).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_633 : ((2468747/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 633, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 633, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 632, cos1179o2c k) + cos1179o2c 633 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 632) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_632
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 633 - ((677479/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_633).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_634 : ((23997149/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 634, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 634, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 633, cos1179o2c k) + cos1179o2c 634 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 633) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_633
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 634 - ((-172549/312500 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_634).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_635 : ((45498079/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 635, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 635, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 634, cos1179o2c k) + cos1179o2c 635 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 634) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_634
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 635 - ((-2495969/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_635).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_636 : ((87774743/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 636, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 636, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 635, cos1179o2c k) + cos1179o2c 636 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 635) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_635
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 636 - ((-644183/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_636).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_637 : ((44447833/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 637, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 637, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 636, cos1179o2c k) + cos1179o2c 637 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 636) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_636
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 637 - ((1121423/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_637).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_638 : ((93460819/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 638, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 638, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 637, cos1179o2c k) + cos1179o2c 638 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 637) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_637
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 638 - ((4565653/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_638).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_639 : ((195680223/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 639, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 639, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 638, cos1179o2c k) + cos1179o2c 639 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 638) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_638
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 639 - ((1751917/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_639).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_640 : ((197130263/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 640, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 640, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 639, cos1179o2c k) + cos1179o2c 640 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 639) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_639
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 640 - ((9069/62500 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_640).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_641 : ((95066879/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 641, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 641, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 640, cos1179o2c k) + cos1179o2c 641 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 640) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_640
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 641 - ((-1399101/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_641).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_642 : ((90104119/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 642, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 642, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 641, cos1179o2c k) + cos1179o2c 642 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 641) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_641
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 642 - ((-248113/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_642).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_643 : ((87574421/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 643, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 643, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 642, cos1179o2c k) + cos1179o2c 643 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 642) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_642
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 643 - ((-1264599/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_643).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_644 : ((8945509/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 644, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 644, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 643, cos1179o2c k) + cos1179o2c 644 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 643) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_643
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 644 - ((1881169/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_644).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_645 : ((188545821/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 645, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 645, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 644, cos1179o2c k) + cos1179o2c 645 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 644) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_644
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 645 - ((9636641/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_645).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_646 : ((98274353/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 646, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 646, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 645, cos1179o2c k) + cos1179o2c 646 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 645) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_645
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 646 - ((1600777/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_646).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_647 : ((196709333/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 647, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 647, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 646, cos1179o2c k) + cos1179o2c 647 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 646) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_646
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 647 - ((161627/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_647).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_648 : ((188910871/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 648, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 648, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 647, cos1179o2c k) + cos1179o2c 648 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 647) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_647
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 648 - ((-3898731/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_648).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_649 : ((179179011/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 649, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 649, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 648, cos1179o2c k) + cos1179o2c 649 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 648) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_648
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 649 - ((-486543/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_649).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_650 : ((175003213/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 650, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 650, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 649, cos1179o2c k) + cos1179o2c 650 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 649) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_649
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 650 - ((-2087399/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_650).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_651 : ((3591613/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 651, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 651, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 650, cos1179o2c k) + cos1179o2c 651 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 650) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_650
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 651 - ((4578437/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_651).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_652 : ((11837433/625000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 652, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 652, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 651, cos1179o2c k) + cos1179o2c 652 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 651) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_651
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 652 - ((4909639/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_652).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_653 : ((39392309/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 653, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 653, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 652, cos1179o2c k) + cos1179o2c 653 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 652) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_652
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 653 - ((7563617/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_653).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_654 : ((196517493/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 654, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 654, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 653, cos1179o2c k) + cos1179o2c 654 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 653) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_653
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 654 - ((-110763/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_654).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_655 : ((7536457/400000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 655, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 655, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 654, cos1179o2c k) + cos1179o2c 655 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 654) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_654
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 655 - ((-2026267/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_655).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_656 : ((89391059/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 656, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 656, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 655, cos1179o2c k) + cos1179o2c 656 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 655) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_655
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 656 - ((-9628307/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_656).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_657 : ((174893307/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 657, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 657, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 656, cos1179o2c k) + cos1179o2c 657 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 656) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_656
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 657 - ((-3887811/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_657).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_658 : ((179662519/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 658, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 658, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 657, cos1179o2c k) + cos1179o2c 658 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 657) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_657
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 658 - ((1192553/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_658).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_659 : ((189502951/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 659, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 659, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 658, cos1179o2c k) + cos1179o2c 659 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 658) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_658
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 659 - ((1230179/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_659).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_660 : ((39409869/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 660, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 660, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 659, cos1179o2c k) + cos1179o2c 660 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 659) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_659
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 660 - ((3773697/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_660).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_661 : ((196675969/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 661, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 661, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 660, cos1179o2c k) + cos1179o2c 661 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 660) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_660
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 661 - ((-46547/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_661).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_662 : ((37733677/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 662, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 662, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 661, cos1179o2c k) + cos1179o2c 662 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 661) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_661
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 662 - ((-1000823/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_662).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_663 : ((22371479/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 663, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 663, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 662, cos1179o2c k) + cos1179o2c 663 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 662) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_662
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 663 - ((-9695553/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_663).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_664 : ((174757511/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 664, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 664, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 663, cos1179o2c k) + cos1179o2c 664 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 663) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_663
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 664 - ((-4213321/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_664).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_665 : ((17912619/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 665, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 665, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 664, cos1179o2c k) + cos1179o2c 665 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 664) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_664
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 665 - ((4369679/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_665).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_666 : ((94427729/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 666, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 666, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 665, cos1179o2c k) + cos1179o2c 666 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 665) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_665
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 666 - ((2432567/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_666).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_667 : ((98402507/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 667, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 667, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 666, cos1179o2c k) + cos1179o2c 667 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 666) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_666
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 667 - ((1987639/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_667).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_668 : ((197163629/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 668, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 668, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 667, cos1179o2c k) + cos1179o2c 668 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 667) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_667
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 668 - ((71923/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_668).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_669 : ((47419297/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 669, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 669, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 668, cos1179o2c k) + cos1179o2c 669 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 668) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_668
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 669 - ((-7485441/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_669).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_670 : ((89898503/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 670, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 670, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 669, cos1179o2c k) + cos1179o2c 670 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 669) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_669
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 670 - ((-4939591/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_670).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_671 : ((174688889/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 671, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 671, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 670, cos1179o2c k) + cos1179o2c 671 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 670) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_670
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 671 - ((-5107117/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_671).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_672 : ((178040393/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 672, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 672, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 671, cos1179o2c k) + cos1179o2c 672 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 671) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_671
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 672 - ((419063/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_672).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_673 : ((93712537/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 673, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 673, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 672, cos1179o2c k) + cos1179o2c 673 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 672) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_672
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 673 - ((9385681/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_673).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_674 : ((98043783/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 674, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 674, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 673, cos1179o2c k) + cos1179o2c 674 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 673) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_673
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 674 - ((2165873/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_674).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_675 : ((197816931/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 675, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 675, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 674, cos1179o2c k) + cos1179o2c 675 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 674) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_674
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 675 - ((346073/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_675).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_676 : ((9569153/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 676, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 676, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 675, cos1179o2c k) + cos1179o2c 676 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 675) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_675
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 676 - ((-6432871/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_676).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_677 : ((90691031/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 677, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 677, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 676, cos1179o2c k) + cos1179o2c 677 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 676) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_676
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 677 - ((-4999999/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_677).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_678 : ((21866111/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 678, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 678, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 677, cos1179o2c k) + cos1179o2c 678 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 677) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_677
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 678 - ((-3226087/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_678).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_679 : ((176595621/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 679, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 679, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 678, cos1179o2c k) + cos1179o2c 679 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 678) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_678
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 679 - ((1667733/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_679).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_680 : ((92596787/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 680, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 680, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 679, cos1179o2c k) + cos1179o2c 680 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 679) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_679
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 680 - ((8598953/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_680).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_681 : ((9732553/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 681, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 681, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 680, cos1179o2c k) + cos1179o2c 681 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 680) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_680
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 681 - ((4729243/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_681).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_682 : ((39662977/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 682, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 682, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 681, cos1179o2c k) + cos1179o2c 682 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 681) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_681
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 682 - ((146593/400000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_682).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_683 : ((9681039/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 683, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 683, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 682, cos1179o2c k) + cos1179o2c 683 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 682) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_682
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 683 - ((-938621/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_683).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_684 : ((91930173/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 684, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 684, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 683, cos1179o2c k) + cos1179o2c 684 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 683) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_683
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 684 - ((-4879717/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_684).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_685 : ((7033873/400000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 685, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 685, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 684, cos1179o2c k) + cos1179o2c 685 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 684) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_684
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 685 - ((-8012521/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_685).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_686 : ((175152159/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 686, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 686, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 685, cos1179o2c k) + cos1179o2c 686 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 685) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_685
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 686 - ((-346833/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_686).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_687 : ((45562341/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 687, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 687, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 686, cos1179o2c k) + cos1179o2c 687 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 686) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_686
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 687 - ((1419641/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_687).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_688 : ((48054887/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 688, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 688, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 687, cos1179o2c k) + cos1179o2c 688 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 687) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_687
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 688 - ((623199/625000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_688).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_689 : ((198179851/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 689, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 689, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 688, cos1179o2c k) + cos1179o2c 689 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 688) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_688
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 689 - ((5961303/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_689).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_690 : ((98016441/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 690, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 690, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 689, cos1179o2c k) + cos1179o2c 690 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 689) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_689
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 690 - ((-2145969/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_690).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_691 : ((46814907/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 691, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 691, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 690, cos1179o2c k) + cos1179o2c 691 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 690) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_690
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 691 - ((-4386127/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_691).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_692 : ((44467713/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 692, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 692, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 691, cos1179o2c k) + cos1179o2c 692 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 691) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_691
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 692 - ((-73342/78125 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_692).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_693 : ((10892123/625000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 693, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 693, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 692, cos1179o2c k) + cos1179o2c 693 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 692) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_692
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 693 - ((-898971/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_693).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_694 : ((44727637/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 694, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 694, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 693, cos1179o2c k) + cos1179o2c 694 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 693) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_693
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 694 - ((231879/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_694).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_695 : ((94311769/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 695, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 695, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 694, cos1179o2c k) + cos1179o2c 695 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 694) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_694
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 695 - ((971399/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_695).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_696 : ((196831373/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 696, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 696, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 695, cos1179o2c k) + cos1179o2c 696 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 695) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_695
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 696 - ((1641767/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_696).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_697 : ((98996629/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 697, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 697, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 696, cos1179o2c k) + cos1179o2c 697 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 696) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_696
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 697 - ((232577/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_697).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_698 : ((23916737/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 698, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 698, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 697, cos1179o2c k) + cos1179o2c 698 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 697) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_697
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 698 - ((-3329181/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_698).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_699 : ((181332911/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 699, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 699, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 698, cos1179o2c k) + cos1179o2c 699 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 698) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_698
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 699 - ((-1999997/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_699).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_700 : ((87345411/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 700, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 700, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 699, cos1179o2c k) + cos1179o2c 700 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 699) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_699
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 700 - ((-6641089/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_700).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_701 : ((281343/16000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 701, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 701, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 700, cos1179o2c k) + cos1179o2c 701 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 700) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_700
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 701 - ((1149553/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_701).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_702 : ((184004983/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 702, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 702, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 701, cos1179o2c k) + cos1179o2c 702 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 701) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_701
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 702 - ((510413/625000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_702).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_703 : ((96877187/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 703, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 703, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 702, cos1179o2c k) + cos1179o2c 703 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 702) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_702
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 703 - ((9750391/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_703).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_704 : ((12414109/625000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 704, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 704, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 703, cos1179o2c k) + cos1179o2c 704 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 703) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_703
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 704 - ((487237/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_704).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_705 : ((3908089/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 705, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 705, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 704, cos1179o2c k) + cos1179o2c 705 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 704) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_704
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 705 - ((-1610147/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_705).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_706 : ((186221777/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 706, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 706, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 705, cos1179o2c k) + cos1179o2c 706 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 705) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_705
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 706 - ((-9181673/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_706).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_707 : ((88559351/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 707, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 707, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 706, cos1179o2c k) + cos1179o2c 707 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 706) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_706
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 707 - ((-364083/400000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_707).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_708 : ((174061541/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 708, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 708, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 707, cos1179o2c k) + cos1179o2c 708 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 707) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_707
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 708 - ((-3056161/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_708).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_709 : ((179042301/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 709, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 709, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 708, cos1179o2c k) + cos1179o2c 709 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 708) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_708
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 709 - ((7784/15625 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_709).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_710 : ((94401811/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 710, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 710, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 709, cos1179o2c k) + cos1179o2c 710 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 709) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_709
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 710 - ((9762321/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_710).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_711 : ((196991877/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 711, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 711, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 710, cos1179o2c k) + cos1179o2c 711 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 710) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_710
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 711 - ((1637851/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_711).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_712 : ((99148537/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 712, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 712, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 711, cos1179o2c k) + cos1179o2c 712 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 711) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_711
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 712 - ((1306197/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_712).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_713 : ((191881709/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 713, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 713, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 712, cos1179o2c k) + cos1179o2c 713 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 712) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_712
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 713 - ((-1282873/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_713).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_714 : ((22736543/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 714, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 714, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 713, cos1179o2c k) + cos1179o2c 714 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 713) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_713
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 714 - ((-1997673/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_714).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_715 : ((17475989/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 715, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 715, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 714, cos1179o2c k) + cos1179o2c 715 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 714) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_714
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 715 - ((-3565727/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_715).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_716 : ((175057947/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 716, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 716, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 715, cos1179o2c k) + cos1179o2c 716 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 715) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_715
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 716 - ((299057/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_716).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_717 : ((182587381/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 717, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 717, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 716, cos1179o2c k) + cos1179o2c 717 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 716) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_716
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 717 - ((3765217/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_717).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_718 : ((192532903/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 718, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 718, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 717, cos1179o2c k) + cos1179o2c 718 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 717) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_717
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 718 - ((4973261/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_718).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_719 : ((198558781/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 719, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 719, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 718, cos1179o2c k) + cos1179o2c 719 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 718) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_718
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 719 - ((3013439/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_719).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_720 : ((19684151/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 720, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 720, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 719, cos1179o2c k) + cos1179o2c 720 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 719) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_719
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 720 - ((-1716271/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_720).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_721 : ((23559587/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 721, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 721, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 720, cos1179o2c k) + cos1179o2c 721 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 720) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_720
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 721 - ((-4181907/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_721).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_722 : ((178754991/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 722, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 722, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 721, cos1179o2c k) + cos1179o2c 722 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 721) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_721
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 722 - ((-1944141/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_722).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_723 : ((173802811/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 723, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 723, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 722, cos1179o2c k) + cos1179o2c 723 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 722) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_722
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 723 - ((-247559/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_723).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_724 : ((17672621/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 724, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 724, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 723, cos1179o2c k) + cos1179o2c 724 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 723) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_723
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 724 - ((2924399/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_724).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_725 : ((9284213/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 725, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 725, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 724, cos1179o2c k) + cos1179o2c 725 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 724) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_724
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 725 - ((179181/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_725).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_726 : ((195069301/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 726, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 726, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 725, cos1179o2c k) + cos1179o2c 726 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 725) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_725
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 726 - ((9386041/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_726).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_727 : ((9951423/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 727, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 727, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 726, cos1179o2c k) + cos1179o2c 727 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 726) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_726
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 727 - ((3960159/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_727).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_728 : ((195104257/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 728, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 728, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 727, cos1179o2c k) + cos1179o2c 728 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 727) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_727
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 728 - ((-3923203/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_728).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_729 : ((92869397/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 729, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 729, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 728, cos1179o2c k) + cos1179o2c 729 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 728) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_728
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 729 - ((-9364463/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_729).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_730 : ((883659/50000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 730, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 730, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 729, cos1179o2c k) + cos1179o2c 730 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 729) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_729
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 730 - ((-4502997/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_730).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_731 : ((173640433/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 731, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 731, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 730, cos1179o2c k) + cos1179o2c 731 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 730) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_730
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 731 - ((-3090367/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_731).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_732 : ((178360909/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 732, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 732, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 731, cos1179o2c k) + cos1179o2c 732 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 731) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_731
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 732 - ((1180369/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_732).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_733 : ((187986099/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 733, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 733, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 732, cos1179o2c k) + cos1179o2c 733 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 732) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_732
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 733 - ((962619/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_733).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_734 : ((196616303/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 734, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 734, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 733, cos1179o2c k) + cos1179o2c 734 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 733) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_733
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 734 - ((2157801/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_734).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_735 : ((198981363/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 735, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 735, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 734, cos1179o2c k) + cos1179o2c 735 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 734) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_734
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 735 - ((118303/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_735).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_736 : ((96822941/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 736, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 736, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 735, cos1179o2c k) + cos1179o2c 736 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 735) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_735
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 736 - ((-5334481/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_736).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_737 : ((22982491/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 737, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 737, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 736, cos1179o2c k) + cos1179o2c 737 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 736) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_736
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 737 - ((-4892477/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_737).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_738 : ((43889611/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 738, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 738, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 737, cos1179o2c k) + cos1179o2c 738 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 737) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_737
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 738 - ((-2075121/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_738).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_739 : ((173757777/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 739, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 739, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 738, cos1179o2c k) + cos1179o2c 739 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 738) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_738
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 739 - ((-1799667/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_739).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_740 : ((179535909/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 740, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 740, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 739, cos1179o2c k) + cos1179o2c 740 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 739) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_739
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 740 - ((1444783/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_740).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_741 : ((189409549/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 741, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 741, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 740, cos1179o2c k) + cos1179o2c 741 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 740) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_740
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 741 - ((123433/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_741).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_742 : ((49362601/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 742, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 742, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 741, cos1179o2c k) + cos1179o2c 742 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 741) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_741
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 742 - ((1608371/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_742).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_743 : ((49712113/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 743, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 743, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 742, cos1179o2c k) + cos1179o2c 743 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 742) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_742
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 743 - ((174881/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_743).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_744 : ((24096951/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 744, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 744, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 743, cos1179o2c k) + cos1179o2c 744 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 743) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_743
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 744 - ((-1517961/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_744).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_745 : ((22856809/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 745, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 745, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 744, cos1179o2c k) + cos1179o2c 745 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 744) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_744
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 745 - ((-1240017/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_745).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_746 : ((17497991/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 746, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 746, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 745, cos1179o2c k) + cos1179o2c 746 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 745) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_745
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 746 - ((-3936781/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_746).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_747 : ((86906417/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 747, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 747, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 746, cos1179o2c k) + cos1179o2c 747 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 746) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_746
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 747 - ((-291519/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_747).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_748 : ((45008869/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 748, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 748, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 747, cos1179o2c k) + cos1179o2c 748 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 747) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_747
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 748 - ((3111821/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_748).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_749 : ((94986209/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 749, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 749, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 748, cos1179o2c k) + cos1179o2c 749 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 748) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_748
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 749 - ((4968971/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_749).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_750 : ((197777831/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 750, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 750, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 749, cos1179o2c k) + cos1179o2c 750 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 749) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_749
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 750 - ((7806413/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_750).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_751 : ((198877013/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 751, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 751, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 750, cos1179o2c k) + cos1179o2c 751 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 750) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_750
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 751 - ((550091/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_751).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_752 : ((192633239/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 752, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 752, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 751, cos1179o2c k) + cos1179o2c 752 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 751) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_751
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 752 - ((-3121387/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_752).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_753 : ((91348123/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 753, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 753, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 752, cos1179o2c k) + cos1179o2c 753 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 752) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_752
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 753 - ((-9935993/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_753).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_754 : ((174851579/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 754, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 754, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 753, cos1179o2c k) + cos1179o2c 754 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 753) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_753
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 754 - ((-7843667/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_754).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_755 : ((173649971/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 755, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 755, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 754, cos1179o2c k) + cos1179o2c 755 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 754) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_754
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 755 - ((-37519/312500 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_755).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_756 : ((179779437/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 756, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 756, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 755, cos1179o2c k) + cos1179o2c 756 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 755) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_755
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 756 - ((3065233/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_756).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_757 : ((5927873/312500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 757, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 757, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 756, cos1179o2c k) + cos1179o2c 757 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 756) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_756
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 757 - ((9913499/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_757).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_758 : ((98836231/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 758, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 758, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 757, cos1179o2c k) + cos1179o2c 758 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 757) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_757
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 758 - ((3990763/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_758).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_759 : ((49784107/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 759, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 759, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 758, cos1179o2c k) + cos1179o2c 759 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 758) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_758
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 759 - ((732483/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_759).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_760 : ((96625349/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 760, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 760, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 759, cos1179o2c k) + cos1179o2c 760 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 759) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_759
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 760 - ((-588473/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_760).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_761 : ((183387979/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 761, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 761, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 760, cos1179o2c k) + cos1179o2c 761 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 760) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_760
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 761 - ((-9861719/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_761).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_762 : ((43794247/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 762, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 762, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 761, cos1179o2c k) + cos1179o2c 762 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 761) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_761
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 762 - ((-8209991/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_762).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_763 : ((173287109/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 763, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 763, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 762, cos1179o2c k) + cos1179o2c 763 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 762) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_762
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 763 - ((-1888879/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_763).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_764 : ((178783389/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 764, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 764, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 763, cos1179o2c k) + cos1179o2c 764 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 763) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_763
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 764 - ((17179/31250 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_764).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_765 : ((94273251/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 765, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 765, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 764, cos1179o2c k) + cos1179o2c 765 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 764) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_764
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 765 - ((9764113/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_765).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_766 : ((39411603/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 766, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 766, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 765, cos1179o2c k) + cos1179o2c 766 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 765) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_765
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 766 - ((8512513/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_766).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_767 : ((39904747/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 767, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 767, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 766, cos1179o2c k) + cos1179o2c 767 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 766) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_766
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 767 - ((15417/62500 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_767).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_768 : ((97282111/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 768, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 768, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 767, cos1179o2c k) + cos1179o2c 768 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 767) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_767
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 768 - ((-4958513/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_768).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_769 : ((23120799/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 769, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 769, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 768, cos1179o2c k) + cos1179o2c 769 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 768) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_768
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 769 - ((-959683/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_769).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_770 : ((35220189/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 770, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 770, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 769, cos1179o2c k) + cos1179o2c 770 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 769) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_769
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 770 - ((-8864447/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_770).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_771 : ((172911093/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 771, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 771, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 770, cos1179o2c k) + cos1179o2c 771 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 770) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_770
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 771 - ((-797213/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_771).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_772 : ((88582739/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 772, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 772, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 771, cos1179o2c k) + cos1179o2c 772 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 771) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_771
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 772 - ((851077/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_772).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_773 : ((186494491/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 773, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 773, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 772, cos1179o2c k) + cos1179o2c 773 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 772) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_772
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 773 - ((9330013/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_773).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_774 : ((978637/50000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 774, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 774, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 773, cos1179o2c k) + cos1179o2c 774 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 773) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_773
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 774 - ((9233909/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_774).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_775 : ((199764339/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 775, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 775, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 774, cos1179o2c k) + cos1179o2c 775 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 774) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_774
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 775 - ((4037939/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_775).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_776 : ((49096519/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 776, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 776, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 775, cos1179o2c k) + cos1179o2c 776 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 775) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_775
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 776 - ((-3377263/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_776).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_777 : ((46864117/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 777, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 777, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 776, cos1179o2c k) + cos1179o2c 777 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 776) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_776
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 777 - ((-279019/312500 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_777).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_778 : ((88938057/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 778, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 778, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 777, cos1179o2c k) + cos1179o2c 778 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 777) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_777
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 778 - ((-4789677/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_778).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_779 : ((6915383/400000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 779, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 779, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 778, cos1179o2c k) + cos1179o2c 779 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 778) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_778
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 779 - ((-4990539/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_779).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_780 : ((43799993/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 780, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 780, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 779, cos1179o2c k) + cos1179o2c 780 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 779) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_779
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 780 - ((2316397/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_780).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_781 : ((183553907/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 781, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 781, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 780, cos1179o2c k) + cos1179o2c 781 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 780) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_780
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 781 - ((1670987/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_781).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_782 : ((38680879/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 782, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 782, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 781, cos1179o2c k) + cos1179o2c 782 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 781) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_781
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 782 - ((307859/312500 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_782).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_783 : ((199414709/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 783, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 783, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 782, cos1179o2c k) + cos1179o2c 783 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 782) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_782
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 783 - ((3005657/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_783).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_784 : ((198340563/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 784, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 784, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 783, cos1179o2c k) + cos1179o2c 784 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 783) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_783
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 784 - ((-536573/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_784).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_785 : ((23845993/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 785, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 785, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 784, cos1179o2c k) + cos1179o2c 785 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 784) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_784
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 785 - ((-7571619/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_785).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_786 : ((180774391/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 786, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 786, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 785, cos1179o2c k) + cos1179o2c 786 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 785) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_785
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 786 - ((-9992553/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_786).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_787 : ((43430441/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 787, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 787, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 786, cos1179o2c k) + cos1179o2c 787 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 786) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_786
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 787 - ((-7051627/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_787).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_788 : ((6935191/400000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 788, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 788, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 787, cos1179o2c k) + cos1179o2c 788 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 787) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_787
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 788 - ((-340989/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_788).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_789 : ((179924049/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 789, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 789, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 788, cos1179o2c k) + cos1179o2c 789 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 788) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_788
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 789 - ((3272637/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_789).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_790 : ((189861973/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 790, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 790, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 789, cos1179o2c k) + cos1179o2c 790 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 789) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_789
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 790 - ((2484731/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_790).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_791 : ((12369429/625000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 791, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 791, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 790, cos1179o2c k) + cos1179o2c 791 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 790) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_790
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 791 - ((8049891/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_791).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_792 : ((199807121/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 792, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 792, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 791, cos1179o2c k) + cos1179o2c 792 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 791) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_791
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 792 - ((1897257/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_792).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_793 : ((38910727/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 793, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 793, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 792, cos1179o2c k) + cos1179o2c 793 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 792) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_792
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 793 - ((-2626243/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_793).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_794 : ((36985623/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 794, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 794, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 793, cos1179o2c k) + cos1179o2c 794 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 793) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_793
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 794 - ((-240613/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_794).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_795 : ((175998347/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 795, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 795, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 794, cos1179o2c k) + cos1179o2c 795 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 794) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_794
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 795 - ((-69756/78125 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_795).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_796 : ((8622471/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 796, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 796, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 795, cos1179o2c k) + cos1179o2c 796 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 795) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_795
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 796 - ((-3547927/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_796).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_797 : ((88066849/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 797, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 797, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 796, cos1179o2c k) + cos1179o2c 797 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 796) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_796
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 797 - ((1842639/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_797).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_798 : ((185118833/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 798, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 798, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 797, cos1179o2c k) + cos1179o2c 798 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 797) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_797
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 798 - ((1797227/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_798).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_799 : ((194716997/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 799, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 799, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 798, cos1179o2c k) + cos1179o2c 799 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 798) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_798
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 799 - ((2399791/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_799).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_800 : ((199937389/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 800, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 800, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 799, cos1179o2c k) + cos1179o2c 800 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 799) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_799
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 800 - ((326337/625000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_800).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_801 : ((12379801/625000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 801, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 801, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 800, cos1179o2c k) + cos1179o2c 801 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 800) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_800
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 801 - ((-1859573/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_801).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_802 : ((38020857/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 802, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 802, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 801, cos1179o2c k) + cos1179o2c 802 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 801) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_801
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 802 - ((-7971531/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_802).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_803 : ((180140539/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 803, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 803, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 802, cos1179o2c k) + cos1179o2c 803 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 802) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_802
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 803 - ((-4981373/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_803).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_804 : ((173317163/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 804, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 804, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 803, cos1179o2c k) + cos1179o2c 804 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 803) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_803
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 804 - ((-852797/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_804).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_805 : ((173135471/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 805, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 805, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 804, cos1179o2c k) + cos1179o2c 805 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 804) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_804
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 805 - ((-45173/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_805).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_806 : ((89840767/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 806, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 806, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 805, cos1179o2c k) + cos1179o2c 806 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 805) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_805
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 806 - ((6547063/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_806).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_807 : ((189601157/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 807, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 807, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 806, cos1179o2c k) + cos1179o2c 807 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 806) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_806
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 807 - ((9920623/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_807).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_808 : ((98915557/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 808, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 808, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 807, cos1179o2c k) + cos1179o2c 808 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 807) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_807
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 808 - ((8230957/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_808).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_809 : ((200184679/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 809, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 809, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 808, cos1179o2c k) + cos1179o2c 809 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 808) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_808
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 809 - ((470913/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_809).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_810 : ((97736411/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 810, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 810, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 809, cos1179o2c k) + cos1179o2c 810 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 809) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_809
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 810 - ((-4710857/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_810).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_811 : ((46522063/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 811, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 811, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 810, cos1179o2c k) + cos1179o2c 811 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 810) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_810
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 811 - ((-938357/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_811).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_812 : ((88388329/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 812, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 812, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 811, cos1179o2c k) + cos1179o2c 812 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 811) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_811
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 812 - ((-4655297/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_812).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_813 : ((172231209/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 813, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 813, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 812, cos1179o2c k) + cos1179o2c 813 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 812) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_812
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 813 - ((-4544449/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_813).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_814 : ((21841499/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 814, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 814, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 813, cos1179o2c k) + cos1179o2c 814 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 813) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_813
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 814 - ((2501783/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_814).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_815 : ((183017273/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 815, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 815, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 814, cos1179o2c k) + cos1179o2c 815 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 814) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_814
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 815 - ((8286281/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_815).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_816 : ((192933567/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 816, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 816, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 815, cos1179o2c k) + cos1179o2c 816 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 815) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_815
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 816 - ((4958647/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_816).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_817 : ((7981097/400000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 817, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 817, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 816, cos1179o2c k) + cos1179o2c 817 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 816) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_816
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 817 - ((3297429/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_817).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_818 : ((199516417/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 818, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 818, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 817, cos1179o2c k) + cos1179o2c 818 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 817) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_817
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 818 - ((-1251/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_818).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_819 : ((192912607/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 819, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 819, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 818, cos1179o2c k) + cos1179o2c 819 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 818) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_818
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 819 - ((-660281/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_819).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_820 : ((36599259/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 820, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 820, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 819, cos1179o2c k) + cos1179o2c 820 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 819) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_819
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 820 - ((-619707/625000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_820).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_821 : ((174676143/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 821, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 821, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 820, cos1179o2c k) + cos1179o2c 821 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 820) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_820
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 821 - ((-519947/625000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_821).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_822 : ((34411189/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 822, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 822, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 821, cos1179o2c k) + cos1179o2c 822 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 821) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_821
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 822 - ((-1309599/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_822).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_823 : ((176420461/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 823, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 823, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 822, cos1179o2c k) + cos1179o2c 823 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 822) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_822
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 823 - ((1091379/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_823).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_824 : ((92808773/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 824, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 824, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 823, cos1179o2c k) + cos1179o2c 824 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 823) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_823
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 824 - ((1839617/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_824).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_825 : ((39026911/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 825, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 825, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 824, cos1179o2c k) + cos1179o2c 825 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 824) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_824
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 825 - ((9518009/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_825).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_826 : ((100158589/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 826, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 826, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 825, cos1179o2c k) + cos1179o2c 826 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 825) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_825
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 826 - ((5183623/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_826).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_827 : ((198641099/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 827, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 827, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 826, cos1179o2c k) + cos1179o2c 827 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 826) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_826
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 827 - ((-1675079/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_827).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_828 : ((7637127/400000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 828, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 828, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 827, cos1179o2c k) + cos1179o2c 828 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 827) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_827
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 828 - ((-1927981/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_828).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_829 : ((90464737/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 829, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 829, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 828, cos1179o2c k) + cos1179o2c 829 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 828) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_828
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 829 - ((-9997701/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_829).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_830 : ((173491041/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 830, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 830, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 829, cos1179o2c k) + cos1179o2c 830 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 829) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_829
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 830 - ((-7437433/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_830).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_831 : ((86102329/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 831, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 831, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 830, cos1179o2c k) + cos1179o2c 831 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 830) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_830
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 831 - ((-1285383/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_831).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_832 : ((177684707/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 832, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 832, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 831, cos1179o2c k) + cos1179o2c 832 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 831) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_831
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 832 - ((5481049/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_832).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_833 : ((93643533/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 833, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 833, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 832, cos1179o2c k) + cos1179o2c 833 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 832) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_832
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 833 - ((9603359/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_833).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_834 : ((196397731/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 834, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 834, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 833, cos1179o2c k) + cos1179o2c 834 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 833) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_833
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 834 - ((1822333/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_834).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_835 : ((12540843/625000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 835, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 835, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 834, cos1179o2c k) + cos1179o2c 835 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 834) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_834
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 835 - ((4256757/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_835).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_836 : ((99012529/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 836, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 836, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 835, cos1179o2c k) + cos1179o2c 836 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 835) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_835
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 836 - ((-262743/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_836).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_837 : ((2372151/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 837, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 837, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 836, cos1179o2c k) + cos1179o2c 837 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 836) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_836
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 837 - ((-4125989/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_837).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_838 : ((179824777/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 838, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 838, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 837, cos1179o2c k) + cos1179o2c 838 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 837) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_837
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 838 - ((-9946303/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_838).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_839 : ((86452521/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 839, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 839, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 838, cos1179o2c k) + cos1179o2c 839 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 838) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_838
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 839 - ((-1383747/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_839).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_840 : ((34457033/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 840, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 840, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 839, cos1179o2c k) + cos1179o2c 840 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 839) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_839
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 840 - ((-618877/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_840).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_841 : ((89125893/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 841, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 841, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 840, cos1179o2c k) + cos1179o2c 841 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 840) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_840
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 841 - ((5967621/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_841).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_842 : ((187985681/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 842, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 842, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 841, cos1179o2c k) + cos1179o2c 842 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 841) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_841
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 842 - ((1946979/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_842).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_843 : ((196905327/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 843, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 843, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 842, cos1179o2c k) + cos1179o2c 843 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 842) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_842
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 843 - ((4460323/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_843).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_844 : ((25103313/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 844, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 844, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 843, cos1179o2c k) + cos1179o2c 844 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 843) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_843
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 844 - ((3922177/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_844).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_845 : ((98958839/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 845, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 845, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 844, cos1179o2c k) + cos1179o2c 845 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 844) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_844
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 845 - ((-1453913/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_845).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_846 : ((94772057/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 846, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 846, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 845, cos1179o2c k) + cos1179o2c 846 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 845) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_845
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 846 - ((-2093141/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_846).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_847 : ((179612449/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 847, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 847, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 846, cos1179o2c k) + cos1179o2c 847 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 846) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_846
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 847 - ((-1986133/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_847).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_848 : ((34548279/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 848, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 848, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 847, cos1179o2c k) + cos1179o2c 848 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 847) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_847
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 848 - ((-3435027/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_848).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_849 : ((172114463/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 849, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 849, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 848, cos1179o2c k) + cos1179o2c 849 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 848) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_848
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 849 - ((-156483/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_849).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_850 : ((178015613/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 850, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 850, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 849, cos1179o2c k) + cos1179o2c 850 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 849) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_849
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 850 - ((118043/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_850).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_851 : ((37542547/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 851, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 851, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 850, cos1179o2c k) + cos1179o2c 851 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 850) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_850
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 851 - ((4849061/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_851).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_852 : ((98366827/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 852, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 852, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 851, cos1179o2c k) + cos1179o2c 852 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 851) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_851
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 852 - ((9021919/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_852).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_853 : ((50232927/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 853, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 853, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 852, cos1179o2c k) + cos1179o2c 853 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 852) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_852
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 853 - ((2099527/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_853).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_854 : ((99192919/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 854, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 854, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 853, cos1179o2c k) + cos1179o2c 854 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 853) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_853
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 854 - ((-254487/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_854).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_855 : ((190266949/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 855, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 855, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 854, cos1179o2c k) + cos1179o2c 855 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 854) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_854
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 855 - ((-8117889/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_855).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_856 : ((180287379/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 856, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 856, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 855, cos1179o2c k) + cos1179o2c 856 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 855) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_855
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 856 - ((-997857/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_856).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_857 : ((21624413/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 857, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 857, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 856, cos1179o2c k) + cos1179o2c 857 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 856) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_856
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 857 - ((-291643/400000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_857).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_858 : ((171701919/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 858, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 858, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 857, cos1179o2c k) + cos1179o2c 858 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 857) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_857
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 858 - ((-258477/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_858).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_859 : ((176988253/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 859, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 859, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 858, cos1179o2c k) + cos1179o2c 859 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 858) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_858
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 859 - ((2643667/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_859).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_860 : ((7458183/400000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 860, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 860, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 859, cos1179o2c k) + cos1179o2c 860 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 859) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_859
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 860 - ((4733661/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_860).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_861 : ((195822187/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 861, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 861, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 860, cos1179o2c k) + cos1179o2c 861 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 860) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_860
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 861 - ((2342153/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_861).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_862 : ((12554411/625000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 862, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 862, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 861, cos1179o2c k) + cos1179o2c 862 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 861) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_861
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 862 - ((5049389/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_862).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_863 : ((199334123/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 863, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 863, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 862, cos1179o2c k) + cos1179o2c 863 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 862) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_862
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 863 - ((-1535453/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_863).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_864 : ((4797693/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 864, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 864, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 863, cos1179o2c k) + cos1179o2c 864 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 863) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_863
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 864 - ((-7425403/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_864).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_865 : ((181920241/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 865, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 865, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 864, cos1179o2c k) + cos1179o2c 865 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 864) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_864
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 865 - ((-9986479/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_865).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_866 : ((17383367/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 866, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 866, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 865, cos1179o2c k) + cos1179o2c 866 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 865) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_865
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 866 - ((-8085571/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_866).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_867 : ((34249643/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 867, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 867, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 866, cos1179o2c k) + cos1179o2c 867 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 866) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_866
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 867 - ((-516891/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_867).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_868 : ((87654019/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 868, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 868, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 867, cos1179o2c k) + cos1179o2c 868 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 867) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_867
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 868 - ((4060823/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_868).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_869 : ((46051267/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 869, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 869, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 868, cos1179o2c k) + cos1179o2c 869 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 868) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_868
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 869 - ((889803/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_869).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_870 : ((24249563/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 870, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 870, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 869, cos1179o2c k) + cos1179o2c 870 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 869) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_869
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 870 - ((2448109/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_870).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_871 : ((200357303/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 871, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 871, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 870, cos1179o2c k) + cos1179o2c 871 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 870) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_870
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 871 - ((6361799/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_871).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_872 : ((40097431/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 872, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 872, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 871, cos1179o2c k) + cos1179o2c 872 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 871) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_871
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 872 - ((32713/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_872).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_873 : ((97167469/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 873, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 873, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 872, cos1179o2c k) + cos1179o2c 873 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 872) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_872
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 873 - ((-6151217/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_873).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_874 : ((184605073/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 874, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 874, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 873, cos1179o2c k) + cos1179o2c 874 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 873) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_873
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 874 - ((-1945773/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_874).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_875 : ((175559527/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 875, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 875, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 874, cos1179o2c k) + cos1179o2c 875 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 874) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_874
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 875 - ((-4522273/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_875).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_876 : ((171147989/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 876, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 876, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 875, cos1179o2c k) + cos1179o2c 876 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 875) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_875
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 876 - ((-2205269/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_876).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_877 : ((173288161/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 877, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 877, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 876, cos1179o2c k) + cos1179o2c 877 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 876) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_876
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 877 - ((535293/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_877).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_878 : ((90521319/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 878, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 878, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 877, cos1179o2c k) + cos1179o2c 878 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 877) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_877
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 878 - ((7755477/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_878).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_879 : ((38208179/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 879, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 879, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 878, cos1179o2c k) + cos1179o2c 879 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 878) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_878
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 879 - ((9999257/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_879).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_880 : ((198951243/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 880, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 880, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 879, cos1179o2c k) + cos1179o2c 880 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 879) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_879
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 880 - ((1977837/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_880).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_881 : ((10067901/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 881, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 881, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 880, cos1179o2c k) + cos1179o2c 881 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 880) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_880
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 881 - ((2407777/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_881).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_882 : ((39445739/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 882, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 882, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 881, cos1179o2c k) + cos1179o2c 882 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 881) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_881
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 882 - ((-165133/400000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_882).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_883 : ((188344911/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 883, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 883, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 882, cos1179o2c k) + cos1179o2c 883 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 882) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_882
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 883 - ((-277587/312500 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_883).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_884 : ((44630959/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 884, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 884, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 883, cos1179o2c k) + cos1179o2c 884 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 883) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_883
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 884 - ((-392803/400000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_884).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_885 : ((171971763/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 885, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 885, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 884, cos1179o2c k) + cos1179o2c 885 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 884) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_884
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 885 - ((-6551073/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_885).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_886 : ((171484931/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 886, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 886, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 885, cos1179o2c k) + cos1179o2c 886 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 885) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_885
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 886 - ((-60729/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_886).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_887 : ((177264567/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 887, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 887, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 886, cos1179o2c k) + cos1179o2c 887 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 886) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_886
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 887 - ((1445159/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_887).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_888 : ((186845451/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 888, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 888, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 887, cos1179o2c k) + cos1179o2c 888 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 887) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_887
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 888 - ((2395471/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_888).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_889 : ((196155783/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 889, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 889, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 888, cos1179o2c k) + cos1179o2c 889 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 888) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_888
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 889 - ((2327833/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_889).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_890 : ((100625703/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 890, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 890, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 889, cos1179o2c k) + cos1179o2c 890 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 889) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_889
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 890 - ((5096623/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_890).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_891 : ((24997709/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 891, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 891, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 890, cos1179o2c k) + cos1179o2c 891 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 890) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_890
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 891 - ((-634367/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_891).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_892 : ((96443999/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 892, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 892, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 891, cos1179o2c k) + cos1179o2c 892 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 891) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_891
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 892 - ((-3546337/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_892).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_893 : ((91480579/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 893, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 893, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 892, cos1179o2c k) + cos1179o2c 893 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 892) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_892
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 893 - ((-124073/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_893).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_894 : ((6974893/400000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 894, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 894, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 893, cos1179o2c k) + cos1179o2c 894 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 893) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_893
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 894 - ((-8587833/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_894).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_895 : ((85359749/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 895, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 895, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 894, cos1179o2c k) + cos1179o2c 895 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 894) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_894
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 895 - ((-3651827/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_895).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_896 : ((10845309/625000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 896, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 896, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 895, cos1179o2c k) + cos1179o2c 896 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 895) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_895
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 896 - ((1403223/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_896).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_897 : ((181611269/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 897, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 897, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 896, cos1179o2c k) + cos1179o2c 897 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 896) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_896
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 897 - ((323493/400000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_897).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_898 : ((23950793/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 898, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 898, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 897, cos1179o2c k) + cos1179o2c 898 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 897) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_897
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 898 - ((399843/400000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_898).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_899 : ((199355023/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 899, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 899, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 898, cos1179o2c k) + cos1179o2c 899 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 898) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_898
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 899 - ((7749679/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_899).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_900 : ((201646621/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 900, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 900, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 899, cos1179o2c k) + cos1179o2c 900 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 899) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_899
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 900 - ((1146299/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_900).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_901 : ((197537701/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 901, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 901, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 900, cos1179o2c k) + cos1179o2c 901 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 900) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_900
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 901 - ((-51349/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_901).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_902 : ((37746019/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 902, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 902, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 901, cos1179o2c k) + cos1179o2c 902 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 901) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_901
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 902 - ((-4403303/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_902).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_903 : ((7154249/400000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 903, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 903, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 902, cos1179o2c k) + cos1179o2c 903 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 902) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_902
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 903 - ((-987287/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_903).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_904 : ((10748459/625000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 904, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 904, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 903, cos1179o2c k) + cos1179o2c 904 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 903) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_903
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 904 - ((-6879881/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_904).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_905 : ((170906763/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 905, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 905, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 904, cos1179o2c k) + cos1179o2c 905 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 904) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_904
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 905 - ((-1067581/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_905).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_906 : ((17608209/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 906, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 906, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 905, cos1179o2c k) + cos1179o2c 906 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 905) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_905
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 906 - ((5176327/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_906).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_907 : ((185380893/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 907, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 907, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 906, cos1179o2c k) + cos1179o2c 907 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 906) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_906
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 907 - ((9299803/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_907).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_908 : ((97504599/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 908, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 908, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 907, cos1179o2c k) + cos1179o2c 908 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 907) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_907
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 908 - ((1925861/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_908).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_909 : ((20105051/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 909, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 909, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 908, cos1179o2c k) + cos1179o2c 909 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 908) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_908
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 909 - ((755289/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_909).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_910 : ((50263991/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 910, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 910, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 909, cos1179o2c k) + cos1179o2c 910 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 909) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_909
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 910 - ((3227/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_910).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_911 : ((97514293/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 911, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 911, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 910, cos1179o2c k) + cos1179o2c 911 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 910) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_910
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 911 - ((-3013189/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_911).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_912 : ((92704739/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 912, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 912, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 911, cos1179o2c k) + cos1179o2c 912 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 911) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_911
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 912 - ((-2404527/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_912).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_913 : ((176080799/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 913, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 913, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 912, cos1179o2c k) + cos1179o2c 913 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 912) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_912
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 913 - ((-9327679/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_913).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_914 : ((170796001/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 914, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 914, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 913, cos1179o2c k) + cos1179o2c 914 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 913) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_913
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 914 - ((-2641899/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_914).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_915 : ((171673141/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 915, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 915, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 914, cos1179o2c k) + cos1179o2c 915 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 914) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_914
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 915 - ((43907/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_915).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_916 : ((178354523/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 916, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 916, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 915, cos1179o2c k) + cos1179o2c 916 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 915) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_915
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 916 - ((3341191/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_916).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_917 : ((94081267/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 917, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 917, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 916, cos1179o2c k) + cos1179o2c 917 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 916) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_916
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 917 - ((9809011/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_917).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_918 : ((49295033/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 918, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 918, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 917, cos1179o2c k) + cos1179o2c 918 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 917) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_917
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 918 - ((4509299/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_918).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_919 : ((201816493/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 919, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 919, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 918, cos1179o2c k) + cos1179o2c 919 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 918) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_918
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 919 - ((4637361/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_919).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_920 : ((200233431/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 920, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 920, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 919, cos1179o2c k) + cos1179o2c 920 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 919) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_919
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 920 - ((-791031/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_920).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_921 : ((193063703/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 921, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 921, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 920, cos1179o2c k) + cos1179o2c 921 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 920) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_920
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 921 - ((-896091/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_921).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_922 : ((183149387/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 922, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 922, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 921, cos1179o2c k) + cos1179o2c 922 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 921) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_921
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 922 - ((-2478329/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_922).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_923 : ((10900473/625000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 923, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 923, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 922, cos1179o2c k) + cos1179o2c 923 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 922) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_922
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 923 - ((-8740819/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_923).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_924 : ((85140623/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 924, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 924, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 923, cos1179o2c k) + cos1179o2c 924 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 923) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_923
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 924 - ((-2062661/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_924).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_925 : ((34477721/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 925, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 925, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 924, cos1179o2c k) + cos1179o2c 925 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 924) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_924
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 925 - ((2108359/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_925).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_926 : ((179896347/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 926, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 926, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 925, cos1179o2c k) + cos1179o2c 926 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 925) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_925
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 926 - ((3754371/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_926).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_927 : ((5933097/312500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 927, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 927, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 926, cos1179o2c k) + cos1179o2c 927 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 926) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_926
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 927 - ((9963757/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_927).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_928 : ((49595269/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 928, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 928, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 927, cos1179o2c k) + cos1179o2c 928 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 927) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_927
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 928 - ((2130743/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_928).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_929 : ((25267503/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 929, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 929, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 928, cos1179o2c k) + cos1179o2c 929 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 928) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_928
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 929 - ((939987/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_929).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_930 : ((199677447/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 930, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 930, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 929, cos1179o2c k) + cos1179o2c 930 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 929) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_929
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 930 - ((-2461577/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_930).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_931 : ((23994343/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 931, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 931, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 930, cos1179o2c k) + cos1179o2c 931 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 930) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_930
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 931 - ((-7721703/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_931).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_932 : ((18196923/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 932, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 932, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 931, cos1179o2c k) + cos1179o2c 932 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 931) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_931
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 932 - ((-4992257/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_932).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_933 : ((34716917/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 933, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 933, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 932, cos1179o2c k) + cos1179o2c 933 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 932) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_932
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 933 - ((-1676729/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_933).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_934 : ((85017309/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 934, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 934, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 933, cos1179o2c k) + cos1179o2c 934 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 933) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_933
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 934 - ((-3548967/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_934).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_935 : ((21585231/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 935, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 935, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 934, cos1179o2c k) + cos1179o2c 935 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 934) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_934
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 935 - ((264823/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_935).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_936 : ((90251261/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 936, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 936, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 935, cos1179o2c k) + cos1179o2c 936 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 935) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_935
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 936 - ((3910837/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_936).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_937 : ((47623049/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 937, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 937, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 936, cos1179o2c k) + cos1179o2c 937 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 936) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_936
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 937 - ((4995337/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_937).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_938 : ((99412423/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 938, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 938, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 937, cos1179o2c k) + cos1179o2c 938 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 937) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_937
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 938 - ((166673/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_938).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_939 : ((101159509/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 939, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 939, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 938, cos1179o2c k) + cos1179o2c 939 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 938) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_938
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 939 - ((873793/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_939).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_940 : ((199646771/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 940, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 940, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 939, cos1179o2c k) + cos1179o2c 940 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 939) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_939
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 940 - ((-2671247/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_940).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_941 : ((5994681/312500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 941, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 941, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 940, cos1179o2c k) + cos1179o2c 941 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 940) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_940
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 941 - ((-7815979/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_941).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_942 : ((90920027/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 942, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 942, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 941, cos1179o2c k) + cos1179o2c 942 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 941) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_941
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 942 - ((-4994369/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_942).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_943 : ((86731727/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 943, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 943, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 942, cos1179o2c k) + cos1179o2c 943 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 942) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_942
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 943 - ((-20939/25000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_943).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_944 : ((2123313/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 944, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 944, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 943, cos1179o2c k) + cos1179o2c 944 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 943) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_943
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 944 - ((-1798707/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_944).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_945 : ((21549729/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 945, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 945, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 944, cos1179o2c k) + cos1179o2c 945 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 944) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_944
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 945 - ((79181/312500 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_945).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_946 : ((45025461/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 946, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 946, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 945, cos1179o2c k) + cos1179o2c 946 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 945) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_945
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 946 - ((1926253/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_946).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_947 : ((95038743/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 947, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 947, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 946, cos1179o2c k) + cos1179o2c 947 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 946) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_946
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 947 - ((4988321/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_947).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_948 : ((2482269/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 948, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 948, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 947, cos1179o2c k) + cos1179o2c 948 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 947) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_947
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 948 - ((4252517/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_948).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_949 : ((202433131/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 949, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 949, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 948, cos1179o2c k) + cos1179o2c 949 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 948) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_948
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 949 - ((3852611/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_949).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_950 : ((100098727/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 950, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 950, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 949, cos1179o2c k) + cos1179o2c 950 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 949) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_949
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 950 - ((-2234677/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_950).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_951 : ((19271287/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 951, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 951, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 950, cos1179o2c k) + cos1179o2c 951 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 950) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_950
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 951 - ((-116931/156250 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_951).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_952 : ((91383813/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 952, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 952, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 951, cos1179o2c k) + cos1179o2c 952 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 951) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_951
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 952 - ((-2486061/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_952).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_953 : ((8702759/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 953, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 953, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 952, cos1179o2c k) + cos1179o2c 953 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 952) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_952
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 953 - ((-4355723/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_953).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_954 : ((8490047/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 954, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 954, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 953, cos1179o2c k) + cos1179o2c 954 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 953) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_953
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 954 - ((-106331/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_954).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_955 : ((171573501/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 955, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 955, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 954, cos1179o2c k) + cos1179o2c 955 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 954) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_954
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 955 - ((1773561/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_955).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_956 : ((44678257/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 956, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 956, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 955, cos1179o2c k) + cos1179o2c 956 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 955) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_955
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 956 - ((7140527/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_956).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_957 : ((1473324/78125 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 957, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 957, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 956, cos1179o2c k) + cos1179o2c 957 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 956) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_956
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 957 - ((2468361/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_957).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_958 : ((197560873/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 958, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 958, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 957, cos1179o2c k) + cos1179o2c 958 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 957) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_957
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 958 - ((8976401/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_958).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_959 : ((6323391/312500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 959, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 959, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 958, cos1179o2c k) + cos1179o2c 959 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 958) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_958
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 959 - ((4788639/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_959).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_960 : ((201199879/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 960, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 960, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 959, cos1179o2c k) + cos1179o2c 960 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 959) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_959
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 960 - ((-1147633/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_960).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_961 : ((194539099/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 961, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 961, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 960, cos1179o2c k) + cos1179o2c 961 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 960) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_960
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 961 - ((-332989/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_961).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_962 : ((184798961/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 962, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 962, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 961, cos1179o2c k) + cos1179o2c 962 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 961) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_961
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 962 - ((-4869569/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_962).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_963 : ((175524647/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 963, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 963, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 962, cos1179o2c k) + cos1179o2c 963 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 962) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_962
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 963 - ((-4636657/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_963).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_964 : ((3401633/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 964, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 964, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 963, cos1179o2c k) + cos1179o2c 964 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 963) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_963
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 964 - ((-5441997/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_964).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_965 : ((170438749/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 965, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 965, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 964, cos1179o2c k) + cos1179o2c 965 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 964) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_964
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 965 - ((358099/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_965).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_966 : ((88230309/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 966, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 966, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 965, cos1179o2c k) + cos1179o2c 966 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 965) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_965
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 966 - ((6022869/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_966).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_967 : ((23246127/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 967, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 967, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 966, cos1179o2c k) + cos1179o2c 967 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 966) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_966
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 967 - ((4754699/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_967).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_968 : ((39107341/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 968, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 968, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 967, cos1179o2c k) + cos1179o2c 968 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 967) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_967
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 968 - ((9568689/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_968).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_969 : ((50431111/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 969, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 969, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 968, cos1179o2c k) + cos1179o2c 969 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 968) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_968
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 969 - ((6188739/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_969).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_970 : ((50579019/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 970, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 970, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 969, cos1179o2c k) + cos1179o2c 970 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 969) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_969
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 970 - ((74079/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_970).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_971 : ((24638027/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 971, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 971, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 970, cos1179o2c k) + cos1179o2c 971 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 970) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_970
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 971 - ((-260543/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_971).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_972 : ((46988863/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 972, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 972, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 971, cos1179o2c k) + cos1179o2c 972 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 971) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_971
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 972 - ((-2286941/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_972).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_973 : ((89067471/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 973, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 973, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 972, cos1179o2c k) + cos1179o2c 973 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 972) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_972
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 973 - ((-981951/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_973).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_974 : ((2674021/156250 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 974, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 974, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 973, cos1179o2c k) + cos1179o2c 974 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 973) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_973
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 974 - ((-3498299/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_974).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_975 : ((42361043/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 975, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 975, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 974, cos1179o2c k) + cos1179o2c 975 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 974) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_974
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 975 - ((-423043/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_975).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_976 : ((86825287/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 976, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 976, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 975, cos1179o2c k) + cos1179o2c 976 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 975) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_975
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 976 - ((2103701/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_976).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_977 : ((11391457/625000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 977, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 977, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 976, cos1179o2c k) + cos1179o2c 977 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 976) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_976
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 977 - ((4306869/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_977).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_978 : ((192237661/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 978, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 978, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 977, cos1179o2c k) + cos1179o2c 978 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 977) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_977
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 978 - ((9975349/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_978).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_979 : ((200058087/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 979, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 979, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 978, cos1179o2c k) + cos1179o2c 979 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 978) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_978
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 979 - ((3910713/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_979).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_980 : ((202976697/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 980, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 980, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 979, cos1179o2c k) + cos1179o2c 980 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 979) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_979
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 980 - ((291961/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_980).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_981 : ((199973199/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 981, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 981, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 980, cos1179o2c k) + cos1179o2c 981 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 980) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_980
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 981 - ((-1501249/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_981).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_982 : ((192104267/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 982, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 982, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 981, cos1179o2c k) + cos1179o2c 982 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 981) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_981
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 982 - ((-1966983/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_982).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_983 : ((182124519/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 983, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 983, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 982, cos1179o2c k) + cos1179o2c 983 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 982) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_982
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 983 - ((-2494687/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_983).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_984 : ((86758219/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 984, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 984, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 983, cos1179o2c k) + cos1179o2c 984 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 983) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_983
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 984 - ((-8607081/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_984).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_985 : ((169275553/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 985, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 985, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 984, cos1179o2c k) + cos1179o2c 985 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 984) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_984
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 985 - ((-847977/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_985).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_986 : ((170870903/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 986, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 986, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 985, cos1179o2c k) + cos1179o2c 986 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 985) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_985
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 986 - ((31927/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_986).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_987 : ((177743859/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 987, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 987, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 986, cos1179o2c k) + cos1179o2c 987 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 986) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_986
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 987 - ((1718489/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_987).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_988 : ((93755273/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 988, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 988, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 987, cos1179o2c k) + cos1179o2c 988 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 987) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_987
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 988 - ((9767687/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_988).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_989 : ((196794613/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 989, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 989, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 988, cos1179o2c k) + cos1179o2c 989 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 988) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_988
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 989 - ((9285067/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_989).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_990 : ((20239557/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 990, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 990, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 989, cos1179o2c k) + cos1179o2c 990 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 989) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_989
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 990 - ((5601957/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_990).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_991 : ((101194599/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 991, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 991, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 990, cos1179o2c k) + cos1179o2c 991 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 990) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_990
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 991 - ((-1343/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_991).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_992 : ((98391113/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 992, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 992, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 991, cos1179o2c k) + cos1179o2c 992 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 991) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_991
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 992 - ((-1401493/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_992).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_993 : ((187501153/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 993, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 993, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 992, cos1179o2c k) + cos1179o2c 993 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 992) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_992
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 993 - ((-9280073/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_993).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_994 : ((177723239/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 994, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 994, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 993, cos1179o2c k) + cos1179o2c 994 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 993) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_993
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 994 - ((-4888457/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_994).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_995 : ((170786549/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 995, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 995, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 994, cos1179o2c k) + cos1179o2c 995 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 994) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_994
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 995 - ((-693569/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_995).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_996 : ((16905157/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 996, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 996, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 995, cos1179o2c k) + cos1179o2c 996 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 995) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_995
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 996 - ((-1733979/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_996).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_997 : ((43275841/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 997, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 997, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 996, cos1179o2c k) + cos1179o2c 997 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 996) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_996
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 997 - ((2026397/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_997).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_998 : ((36312281/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 998, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 998, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 997, cos1179o2c k) + cos1179o2c 998 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 997) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_997
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 998 - ((8459041/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_998).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_999 : ((11972283/625000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 999, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 999, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 998, cos1179o2c k) + cos1179o2c 999 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 998) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_998
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 999 - ((9996123/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_999).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1179o2_1000 : ((199707997/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 1000, cos1179o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 1000, cos1179o2c k)
      = (∑ k ∈ Finset.Icc 11 999, cos1179o2c k) + cos1179o2c 1000 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 999) (by norm_num) cos1179o2c
    simpa using h
  have hprev := psum1179o2_999
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1179o2c 1000 - ((8152469/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1179o2_br_1000).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

set_option maxHeartbeats 6400000 in
set_option maxRecDepth 32768 in
theorem psum1179o2_floor : ∀ j : ℕ, 11 ≤ j → j ≤ 1000 →
    ((0 : ℚ) : ℝ) ≤ ∑ k ∈ Finset.Icc 11 j, cos1179o2c k := by
  intro j hj1 hj2
  interval_cases j
  · exact le_trans (by norm_num) psum1179o2_11
  · exact le_trans (by norm_num) psum1179o2_12
  · exact le_trans (by norm_num) psum1179o2_13
  · exact le_trans (by norm_num) psum1179o2_14
  · exact le_trans (by norm_num) psum1179o2_15
  · exact le_trans (by norm_num) psum1179o2_16
  · exact le_trans (by norm_num) psum1179o2_17
  · exact le_trans (by norm_num) psum1179o2_18
  · exact le_trans (by norm_num) psum1179o2_19
  · exact le_trans (by norm_num) psum1179o2_20
  · exact le_trans (by norm_num) psum1179o2_21
  · exact le_trans (by norm_num) psum1179o2_22
  · exact le_trans (by norm_num) psum1179o2_23
  · exact le_trans (by norm_num) psum1179o2_24
  · exact le_trans (by norm_num) psum1179o2_25
  · exact le_trans (by norm_num) psum1179o2_26
  · exact le_trans (by norm_num) psum1179o2_27
  · exact le_trans (by norm_num) psum1179o2_28
  · exact le_trans (by norm_num) psum1179o2_29
  · exact le_trans (by norm_num) psum1179o2_30
  · exact le_trans (by norm_num) psum1179o2_31
  · exact le_trans (by norm_num) psum1179o2_32
  · exact le_trans (by norm_num) psum1179o2_33
  · exact le_trans (by norm_num) psum1179o2_34
  · exact le_trans (by norm_num) psum1179o2_35
  · exact le_trans (by norm_num) psum1179o2_36
  · exact le_trans (by norm_num) psum1179o2_37
  · exact le_trans (by norm_num) psum1179o2_38
  · exact le_trans (by norm_num) psum1179o2_39
  · exact le_trans (by norm_num) psum1179o2_40
  · exact le_trans (by norm_num) psum1179o2_41
  · exact le_trans (by norm_num) psum1179o2_42
  · exact le_trans (by norm_num) psum1179o2_43
  · exact le_trans (by norm_num) psum1179o2_44
  · exact le_trans (by norm_num) psum1179o2_45
  · exact le_trans (by norm_num) psum1179o2_46
  · exact le_trans (by norm_num) psum1179o2_47
  · exact le_trans (by norm_num) psum1179o2_48
  · exact le_trans (by norm_num) psum1179o2_49
  · exact le_trans (by norm_num) psum1179o2_50
  · exact le_trans (by norm_num) psum1179o2_51
  · exact le_trans (by norm_num) psum1179o2_52
  · exact le_trans (by norm_num) psum1179o2_53
  · exact le_trans (by norm_num) psum1179o2_54
  · exact le_trans (by norm_num) psum1179o2_55
  · exact le_trans (by norm_num) psum1179o2_56
  · exact le_trans (by norm_num) psum1179o2_57
  · exact le_trans (by norm_num) psum1179o2_58
  · exact le_trans (by norm_num) psum1179o2_59
  · exact le_trans (by norm_num) psum1179o2_60
  · exact le_trans (by norm_num) psum1179o2_61
  · exact le_trans (by norm_num) psum1179o2_62
  · exact le_trans (by norm_num) psum1179o2_63
  · exact le_trans (by norm_num) psum1179o2_64
  · exact le_trans (by norm_num) psum1179o2_65
  · exact le_trans (by norm_num) psum1179o2_66
  · exact le_trans (by norm_num) psum1179o2_67
  · exact le_trans (by norm_num) psum1179o2_68
  · exact le_trans (by norm_num) psum1179o2_69
  · exact le_trans (by norm_num) psum1179o2_70
  · exact le_trans (by norm_num) psum1179o2_71
  · exact le_trans (by norm_num) psum1179o2_72
  · exact le_trans (by norm_num) psum1179o2_73
  · exact le_trans (by norm_num) psum1179o2_74
  · exact le_trans (by norm_num) psum1179o2_75
  · exact le_trans (by norm_num) psum1179o2_76
  · exact le_trans (by norm_num) psum1179o2_77
  · exact le_trans (by norm_num) psum1179o2_78
  · exact le_trans (by norm_num) psum1179o2_79
  · exact le_trans (by norm_num) psum1179o2_80
  · exact le_trans (by norm_num) psum1179o2_81
  · exact le_trans (by norm_num) psum1179o2_82
  · exact le_trans (by norm_num) psum1179o2_83
  · exact le_trans (by norm_num) psum1179o2_84
  · exact le_trans (by norm_num) psum1179o2_85
  · exact le_trans (by norm_num) psum1179o2_86
  · exact le_trans (by norm_num) psum1179o2_87
  · exact le_trans (by norm_num) psum1179o2_88
  · exact le_trans (by norm_num) psum1179o2_89
  · exact le_trans (by norm_num) psum1179o2_90
  · exact le_trans (by norm_num) psum1179o2_91
  · exact le_trans (by norm_num) psum1179o2_92
  · exact le_trans (by norm_num) psum1179o2_93
  · exact le_trans (by norm_num) psum1179o2_94
  · exact le_trans (by norm_num) psum1179o2_95
  · exact le_trans (by norm_num) psum1179o2_96
  · exact le_trans (by norm_num) psum1179o2_97
  · exact le_trans (by norm_num) psum1179o2_98
  · exact le_trans (by norm_num) psum1179o2_99
  · exact le_trans (by norm_num) psum1179o2_100
  · exact le_trans (by norm_num) psum1179o2_101
  · exact le_trans (by norm_num) psum1179o2_102
  · exact le_trans (by norm_num) psum1179o2_103
  · exact le_trans (by norm_num) psum1179o2_104
  · exact le_trans (by norm_num) psum1179o2_105
  · exact le_trans (by norm_num) psum1179o2_106
  · exact le_trans (by norm_num) psum1179o2_107
  · exact le_trans (by norm_num) psum1179o2_108
  · exact le_trans (by norm_num) psum1179o2_109
  · exact le_trans (by norm_num) psum1179o2_110
  · exact le_trans (by norm_num) psum1179o2_111
  · exact le_trans (by norm_num) psum1179o2_112
  · exact le_trans (by norm_num) psum1179o2_113
  · exact le_trans (by norm_num) psum1179o2_114
  · exact le_trans (by norm_num) psum1179o2_115
  · exact le_trans (by norm_num) psum1179o2_116
  · exact le_trans (by norm_num) psum1179o2_117
  · exact le_trans (by norm_num) psum1179o2_118
  · exact le_trans (by norm_num) psum1179o2_119
  · exact le_trans (by norm_num) psum1179o2_120
  · exact le_trans (by norm_num) psum1179o2_121
  · exact le_trans (by norm_num) psum1179o2_122
  · exact le_trans (by norm_num) psum1179o2_123
  · exact le_trans (by norm_num) psum1179o2_124
  · exact le_trans (by norm_num) psum1179o2_125
  · exact le_trans (by norm_num) psum1179o2_126
  · exact le_trans (by norm_num) psum1179o2_127
  · exact le_trans (by norm_num) psum1179o2_128
  · exact le_trans (by norm_num) psum1179o2_129
  · exact le_trans (by norm_num) psum1179o2_130
  · exact le_trans (by norm_num) psum1179o2_131
  · exact le_trans (by norm_num) psum1179o2_132
  · exact le_trans (by norm_num) psum1179o2_133
  · exact le_trans (by norm_num) psum1179o2_134
  · exact le_trans (by norm_num) psum1179o2_135
  · exact le_trans (by norm_num) psum1179o2_136
  · exact le_trans (by norm_num) psum1179o2_137
  · exact le_trans (by norm_num) psum1179o2_138
  · exact le_trans (by norm_num) psum1179o2_139
  · exact le_trans (by norm_num) psum1179o2_140
  · exact le_trans (by norm_num) psum1179o2_141
  · exact le_trans (by norm_num) psum1179o2_142
  · exact le_trans (by norm_num) psum1179o2_143
  · exact le_trans (by norm_num) psum1179o2_144
  · exact le_trans (by norm_num) psum1179o2_145
  · exact le_trans (by norm_num) psum1179o2_146
  · exact le_trans (by norm_num) psum1179o2_147
  · exact le_trans (by norm_num) psum1179o2_148
  · exact le_trans (by norm_num) psum1179o2_149
  · exact le_trans (by norm_num) psum1179o2_150
  · exact le_trans (by norm_num) psum1179o2_151
  · exact le_trans (by norm_num) psum1179o2_152
  · exact le_trans (by norm_num) psum1179o2_153
  · exact le_trans (by norm_num) psum1179o2_154
  · exact le_trans (by norm_num) psum1179o2_155
  · exact le_trans (by norm_num) psum1179o2_156
  · exact le_trans (by norm_num) psum1179o2_157
  · exact le_trans (by norm_num) psum1179o2_158
  · exact le_trans (by norm_num) psum1179o2_159
  · exact le_trans (by norm_num) psum1179o2_160
  · exact le_trans (by norm_num) psum1179o2_161
  · exact le_trans (by norm_num) psum1179o2_162
  · exact le_trans (by norm_num) psum1179o2_163
  · exact le_trans (by norm_num) psum1179o2_164
  · exact le_trans (by norm_num) psum1179o2_165
  · exact le_trans (by norm_num) psum1179o2_166
  · exact le_trans (by norm_num) psum1179o2_167
  · exact le_trans (by norm_num) psum1179o2_168
  · exact le_trans (by norm_num) psum1179o2_169
  · exact le_trans (by norm_num) psum1179o2_170
  · exact le_trans (by norm_num) psum1179o2_171
  · exact le_trans (by norm_num) psum1179o2_172
  · exact le_trans (by norm_num) psum1179o2_173
  · exact le_trans (by norm_num) psum1179o2_174
  · exact le_trans (by norm_num) psum1179o2_175
  · exact le_trans (by norm_num) psum1179o2_176
  · exact le_trans (by norm_num) psum1179o2_177
  · exact le_trans (by norm_num) psum1179o2_178
  · exact le_trans (by norm_num) psum1179o2_179
  · exact le_trans (by norm_num) psum1179o2_180
  · exact le_trans (by norm_num) psum1179o2_181
  · exact le_trans (by norm_num) psum1179o2_182
  · exact le_trans (by norm_num) psum1179o2_183
  · exact le_trans (by norm_num) psum1179o2_184
  · exact le_trans (by norm_num) psum1179o2_185
  · exact le_trans (by norm_num) psum1179o2_186
  · exact le_trans (by norm_num) psum1179o2_187
  · exact le_trans (by norm_num) psum1179o2_188
  · exact le_trans (by norm_num) psum1179o2_189
  · exact le_trans (by norm_num) psum1179o2_190
  · exact le_trans (by norm_num) psum1179o2_191
  · exact le_trans (by norm_num) psum1179o2_192
  · exact le_trans (by norm_num) psum1179o2_193
  · exact le_trans (by norm_num) psum1179o2_194
  · exact le_trans (by norm_num) psum1179o2_195
  · exact le_trans (by norm_num) psum1179o2_196
  · exact le_trans (by norm_num) psum1179o2_197
  · exact le_trans (by norm_num) psum1179o2_198
  · exact le_trans (by norm_num) psum1179o2_199
  · exact le_trans (by norm_num) psum1179o2_200
  · exact le_trans (by norm_num) psum1179o2_201
  · exact le_trans (by norm_num) psum1179o2_202
  · exact le_trans (by norm_num) psum1179o2_203
  · exact le_trans (by norm_num) psum1179o2_204
  · exact le_trans (by norm_num) psum1179o2_205
  · exact le_trans (by norm_num) psum1179o2_206
  · exact le_trans (by norm_num) psum1179o2_207
  · exact le_trans (by norm_num) psum1179o2_208
  · exact le_trans (by norm_num) psum1179o2_209
  · exact le_trans (by norm_num) psum1179o2_210
  · exact le_trans (by norm_num) psum1179o2_211
  · exact le_trans (by norm_num) psum1179o2_212
  · exact le_trans (by norm_num) psum1179o2_213
  · exact le_trans (by norm_num) psum1179o2_214
  · exact le_trans (by norm_num) psum1179o2_215
  · exact le_trans (by norm_num) psum1179o2_216
  · exact le_trans (by norm_num) psum1179o2_217
  · exact le_trans (by norm_num) psum1179o2_218
  · exact le_trans (by norm_num) psum1179o2_219
  · exact le_trans (by norm_num) psum1179o2_220
  · exact le_trans (by norm_num) psum1179o2_221
  · exact le_trans (by norm_num) psum1179o2_222
  · exact le_trans (by norm_num) psum1179o2_223
  · exact le_trans (by norm_num) psum1179o2_224
  · exact le_trans (by norm_num) psum1179o2_225
  · exact le_trans (by norm_num) psum1179o2_226
  · exact le_trans (by norm_num) psum1179o2_227
  · exact le_trans (by norm_num) psum1179o2_228
  · exact le_trans (by norm_num) psum1179o2_229
  · exact le_trans (by norm_num) psum1179o2_230
  · exact le_trans (by norm_num) psum1179o2_231
  · exact le_trans (by norm_num) psum1179o2_232
  · exact le_trans (by norm_num) psum1179o2_233
  · exact le_trans (by norm_num) psum1179o2_234
  · exact le_trans (by norm_num) psum1179o2_235
  · exact le_trans (by norm_num) psum1179o2_236
  · exact le_trans (by norm_num) psum1179o2_237
  · exact le_trans (by norm_num) psum1179o2_238
  · exact le_trans (by norm_num) psum1179o2_239
  · exact le_trans (by norm_num) psum1179o2_240
  · exact le_trans (by norm_num) psum1179o2_241
  · exact le_trans (by norm_num) psum1179o2_242
  · exact le_trans (by norm_num) psum1179o2_243
  · exact le_trans (by norm_num) psum1179o2_244
  · exact le_trans (by norm_num) psum1179o2_245
  · exact le_trans (by norm_num) psum1179o2_246
  · exact le_trans (by norm_num) psum1179o2_247
  · exact le_trans (by norm_num) psum1179o2_248
  · exact le_trans (by norm_num) psum1179o2_249
  · exact le_trans (by norm_num) psum1179o2_250
  · exact le_trans (by norm_num) psum1179o2_251
  · exact le_trans (by norm_num) psum1179o2_252
  · exact le_trans (by norm_num) psum1179o2_253
  · exact le_trans (by norm_num) psum1179o2_254
  · exact le_trans (by norm_num) psum1179o2_255
  · exact le_trans (by norm_num) psum1179o2_256
  · exact le_trans (by norm_num) psum1179o2_257
  · exact le_trans (by norm_num) psum1179o2_258
  · exact le_trans (by norm_num) psum1179o2_259
  · exact le_trans (by norm_num) psum1179o2_260
  · exact le_trans (by norm_num) psum1179o2_261
  · exact le_trans (by norm_num) psum1179o2_262
  · exact le_trans (by norm_num) psum1179o2_263
  · exact le_trans (by norm_num) psum1179o2_264
  · exact le_trans (by norm_num) psum1179o2_265
  · exact le_trans (by norm_num) psum1179o2_266
  · exact le_trans (by norm_num) psum1179o2_267
  · exact le_trans (by norm_num) psum1179o2_268
  · exact le_trans (by norm_num) psum1179o2_269
  · exact le_trans (by norm_num) psum1179o2_270
  · exact le_trans (by norm_num) psum1179o2_271
  · exact le_trans (by norm_num) psum1179o2_272
  · exact le_trans (by norm_num) psum1179o2_273
  · exact le_trans (by norm_num) psum1179o2_274
  · exact le_trans (by norm_num) psum1179o2_275
  · exact le_trans (by norm_num) psum1179o2_276
  · exact le_trans (by norm_num) psum1179o2_277
  · exact le_trans (by norm_num) psum1179o2_278
  · exact le_trans (by norm_num) psum1179o2_279
  · exact le_trans (by norm_num) psum1179o2_280
  · exact le_trans (by norm_num) psum1179o2_281
  · exact le_trans (by norm_num) psum1179o2_282
  · exact le_trans (by norm_num) psum1179o2_283
  · exact le_trans (by norm_num) psum1179o2_284
  · exact le_trans (by norm_num) psum1179o2_285
  · exact le_trans (by norm_num) psum1179o2_286
  · exact le_trans (by norm_num) psum1179o2_287
  · exact le_trans (by norm_num) psum1179o2_288
  · exact le_trans (by norm_num) psum1179o2_289
  · exact le_trans (by norm_num) psum1179o2_290
  · exact le_trans (by norm_num) psum1179o2_291
  · exact le_trans (by norm_num) psum1179o2_292
  · exact le_trans (by norm_num) psum1179o2_293
  · exact le_trans (by norm_num) psum1179o2_294
  · exact le_trans (by norm_num) psum1179o2_295
  · exact le_trans (by norm_num) psum1179o2_296
  · exact le_trans (by norm_num) psum1179o2_297
  · exact le_trans (by norm_num) psum1179o2_298
  · exact le_trans (by norm_num) psum1179o2_299
  · exact le_trans (by norm_num) psum1179o2_300
  · exact le_trans (by norm_num) psum1179o2_301
  · exact le_trans (by norm_num) psum1179o2_302
  · exact le_trans (by norm_num) psum1179o2_303
  · exact le_trans (by norm_num) psum1179o2_304
  · exact le_trans (by norm_num) psum1179o2_305
  · exact le_trans (by norm_num) psum1179o2_306
  · exact le_trans (by norm_num) psum1179o2_307
  · exact le_trans (by norm_num) psum1179o2_308
  · exact le_trans (by norm_num) psum1179o2_309
  · exact le_trans (by norm_num) psum1179o2_310
  · exact le_trans (by norm_num) psum1179o2_311
  · exact le_trans (by norm_num) psum1179o2_312
  · exact le_trans (by norm_num) psum1179o2_313
  · exact le_trans (by norm_num) psum1179o2_314
  · exact le_trans (by norm_num) psum1179o2_315
  · exact le_trans (by norm_num) psum1179o2_316
  · exact le_trans (by norm_num) psum1179o2_317
  · exact le_trans (by norm_num) psum1179o2_318
  · exact le_trans (by norm_num) psum1179o2_319
  · exact le_trans (by norm_num) psum1179o2_320
  · exact le_trans (by norm_num) psum1179o2_321
  · exact le_trans (by norm_num) psum1179o2_322
  · exact le_trans (by norm_num) psum1179o2_323
  · exact le_trans (by norm_num) psum1179o2_324
  · exact le_trans (by norm_num) psum1179o2_325
  · exact le_trans (by norm_num) psum1179o2_326
  · exact le_trans (by norm_num) psum1179o2_327
  · exact le_trans (by norm_num) psum1179o2_328
  · exact le_trans (by norm_num) psum1179o2_329
  · exact le_trans (by norm_num) psum1179o2_330
  · exact le_trans (by norm_num) psum1179o2_331
  · exact le_trans (by norm_num) psum1179o2_332
  · exact le_trans (by norm_num) psum1179o2_333
  · exact le_trans (by norm_num) psum1179o2_334
  · exact le_trans (by norm_num) psum1179o2_335
  · exact le_trans (by norm_num) psum1179o2_336
  · exact le_trans (by norm_num) psum1179o2_337
  · exact le_trans (by norm_num) psum1179o2_338
  · exact le_trans (by norm_num) psum1179o2_339
  · exact le_trans (by norm_num) psum1179o2_340
  · exact le_trans (by norm_num) psum1179o2_341
  · exact le_trans (by norm_num) psum1179o2_342
  · exact le_trans (by norm_num) psum1179o2_343
  · exact le_trans (by norm_num) psum1179o2_344
  · exact le_trans (by norm_num) psum1179o2_345
  · exact le_trans (by norm_num) psum1179o2_346
  · exact le_trans (by norm_num) psum1179o2_347
  · exact le_trans (by norm_num) psum1179o2_348
  · exact le_trans (by norm_num) psum1179o2_349
  · exact le_trans (by norm_num) psum1179o2_350
  · exact le_trans (by norm_num) psum1179o2_351
  · exact le_trans (by norm_num) psum1179o2_352
  · exact le_trans (by norm_num) psum1179o2_353
  · exact le_trans (by norm_num) psum1179o2_354
  · exact le_trans (by norm_num) psum1179o2_355
  · exact le_trans (by norm_num) psum1179o2_356
  · exact le_trans (by norm_num) psum1179o2_357
  · exact le_trans (by norm_num) psum1179o2_358
  · exact le_trans (by norm_num) psum1179o2_359
  · exact le_trans (by norm_num) psum1179o2_360
  · exact le_trans (by norm_num) psum1179o2_361
  · exact le_trans (by norm_num) psum1179o2_362
  · exact le_trans (by norm_num) psum1179o2_363
  · exact le_trans (by norm_num) psum1179o2_364
  · exact le_trans (by norm_num) psum1179o2_365
  · exact le_trans (by norm_num) psum1179o2_366
  · exact le_trans (by norm_num) psum1179o2_367
  · exact le_trans (by norm_num) psum1179o2_368
  · exact le_trans (by norm_num) psum1179o2_369
  · exact le_trans (by norm_num) psum1179o2_370
  · exact le_trans (by norm_num) psum1179o2_371
  · exact le_trans (by norm_num) psum1179o2_372
  · exact le_trans (by norm_num) psum1179o2_373
  · exact le_trans (by norm_num) psum1179o2_374
  · exact le_trans (by norm_num) psum1179o2_375
  · exact le_trans (by norm_num) psum1179o2_376
  · exact le_trans (by norm_num) psum1179o2_377
  · exact le_trans (by norm_num) psum1179o2_378
  · exact le_trans (by norm_num) psum1179o2_379
  · exact le_trans (by norm_num) psum1179o2_380
  · exact le_trans (by norm_num) psum1179o2_381
  · exact le_trans (by norm_num) psum1179o2_382
  · exact le_trans (by norm_num) psum1179o2_383
  · exact le_trans (by norm_num) psum1179o2_384
  · exact le_trans (by norm_num) psum1179o2_385
  · exact le_trans (by norm_num) psum1179o2_386
  · exact le_trans (by norm_num) psum1179o2_387
  · exact le_trans (by norm_num) psum1179o2_388
  · exact le_trans (by norm_num) psum1179o2_389
  · exact le_trans (by norm_num) psum1179o2_390
  · exact le_trans (by norm_num) psum1179o2_391
  · exact le_trans (by norm_num) psum1179o2_392
  · exact le_trans (by norm_num) psum1179o2_393
  · exact le_trans (by norm_num) psum1179o2_394
  · exact le_trans (by norm_num) psum1179o2_395
  · exact le_trans (by norm_num) psum1179o2_396
  · exact le_trans (by norm_num) psum1179o2_397
  · exact le_trans (by norm_num) psum1179o2_398
  · exact le_trans (by norm_num) psum1179o2_399
  · exact le_trans (by norm_num) psum1179o2_400
  · exact le_trans (by norm_num) psum1179o2_401
  · exact le_trans (by norm_num) psum1179o2_402
  · exact le_trans (by norm_num) psum1179o2_403
  · exact le_trans (by norm_num) psum1179o2_404
  · exact le_trans (by norm_num) psum1179o2_405
  · exact le_trans (by norm_num) psum1179o2_406
  · exact le_trans (by norm_num) psum1179o2_407
  · exact le_trans (by norm_num) psum1179o2_408
  · exact le_trans (by norm_num) psum1179o2_409
  · exact le_trans (by norm_num) psum1179o2_410
  · exact le_trans (by norm_num) psum1179o2_411
  · exact le_trans (by norm_num) psum1179o2_412
  · exact le_trans (by norm_num) psum1179o2_413
  · exact le_trans (by norm_num) psum1179o2_414
  · exact le_trans (by norm_num) psum1179o2_415
  · exact le_trans (by norm_num) psum1179o2_416
  · exact le_trans (by norm_num) psum1179o2_417
  · exact le_trans (by norm_num) psum1179o2_418
  · exact le_trans (by norm_num) psum1179o2_419
  · exact le_trans (by norm_num) psum1179o2_420
  · exact le_trans (by norm_num) psum1179o2_421
  · exact le_trans (by norm_num) psum1179o2_422
  · exact le_trans (by norm_num) psum1179o2_423
  · exact le_trans (by norm_num) psum1179o2_424
  · exact le_trans (by norm_num) psum1179o2_425
  · exact le_trans (by norm_num) psum1179o2_426
  · exact le_trans (by norm_num) psum1179o2_427
  · exact le_trans (by norm_num) psum1179o2_428
  · exact le_trans (by norm_num) psum1179o2_429
  · exact le_trans (by norm_num) psum1179o2_430
  · exact le_trans (by norm_num) psum1179o2_431
  · exact le_trans (by norm_num) psum1179o2_432
  · exact le_trans (by norm_num) psum1179o2_433
  · exact le_trans (by norm_num) psum1179o2_434
  · exact le_trans (by norm_num) psum1179o2_435
  · exact le_trans (by norm_num) psum1179o2_436
  · exact le_trans (by norm_num) psum1179o2_437
  · exact le_trans (by norm_num) psum1179o2_438
  · exact le_trans (by norm_num) psum1179o2_439
  · exact le_trans (by norm_num) psum1179o2_440
  · exact le_trans (by norm_num) psum1179o2_441
  · exact le_trans (by norm_num) psum1179o2_442
  · exact le_trans (by norm_num) psum1179o2_443
  · exact le_trans (by norm_num) psum1179o2_444
  · exact le_trans (by norm_num) psum1179o2_445
  · exact le_trans (by norm_num) psum1179o2_446
  · exact le_trans (by norm_num) psum1179o2_447
  · exact le_trans (by norm_num) psum1179o2_448
  · exact le_trans (by norm_num) psum1179o2_449
  · exact le_trans (by norm_num) psum1179o2_450
  · exact le_trans (by norm_num) psum1179o2_451
  · exact le_trans (by norm_num) psum1179o2_452
  · exact le_trans (by norm_num) psum1179o2_453
  · exact le_trans (by norm_num) psum1179o2_454
  · exact le_trans (by norm_num) psum1179o2_455
  · exact le_trans (by norm_num) psum1179o2_456
  · exact le_trans (by norm_num) psum1179o2_457
  · exact le_trans (by norm_num) psum1179o2_458
  · exact le_trans (by norm_num) psum1179o2_459
  · exact le_trans (by norm_num) psum1179o2_460
  · exact le_trans (by norm_num) psum1179o2_461
  · exact le_trans (by norm_num) psum1179o2_462
  · exact le_trans (by norm_num) psum1179o2_463
  · exact le_trans (by norm_num) psum1179o2_464
  · exact le_trans (by norm_num) psum1179o2_465
  · exact le_trans (by norm_num) psum1179o2_466
  · exact le_trans (by norm_num) psum1179o2_467
  · exact le_trans (by norm_num) psum1179o2_468
  · exact le_trans (by norm_num) psum1179o2_469
  · exact le_trans (by norm_num) psum1179o2_470
  · exact le_trans (by norm_num) psum1179o2_471
  · exact le_trans (by norm_num) psum1179o2_472
  · exact le_trans (by norm_num) psum1179o2_473
  · exact le_trans (by norm_num) psum1179o2_474
  · exact le_trans (by norm_num) psum1179o2_475
  · exact le_trans (by norm_num) psum1179o2_476
  · exact le_trans (by norm_num) psum1179o2_477
  · exact le_trans (by norm_num) psum1179o2_478
  · exact le_trans (by norm_num) psum1179o2_479
  · exact le_trans (by norm_num) psum1179o2_480
  · exact le_trans (by norm_num) psum1179o2_481
  · exact le_trans (by norm_num) psum1179o2_482
  · exact le_trans (by norm_num) psum1179o2_483
  · exact le_trans (by norm_num) psum1179o2_484
  · exact le_trans (by norm_num) psum1179o2_485
  · exact le_trans (by norm_num) psum1179o2_486
  · exact le_trans (by norm_num) psum1179o2_487
  · exact le_trans (by norm_num) psum1179o2_488
  · exact le_trans (by norm_num) psum1179o2_489
  · exact le_trans (by norm_num) psum1179o2_490
  · exact le_trans (by norm_num) psum1179o2_491
  · exact le_trans (by norm_num) psum1179o2_492
  · exact le_trans (by norm_num) psum1179o2_493
  · exact le_trans (by norm_num) psum1179o2_494
  · exact le_trans (by norm_num) psum1179o2_495
  · exact le_trans (by norm_num) psum1179o2_496
  · exact le_trans (by norm_num) psum1179o2_497
  · exact le_trans (by norm_num) psum1179o2_498
  · exact le_trans (by norm_num) psum1179o2_499
  · exact le_trans (by norm_num) psum1179o2_500
  · exact le_trans (by norm_num) psum1179o2_501
  · exact le_trans (by norm_num) psum1179o2_502
  · exact le_trans (by norm_num) psum1179o2_503
  · exact le_trans (by norm_num) psum1179o2_504
  · exact le_trans (by norm_num) psum1179o2_505
  · exact le_trans (by norm_num) psum1179o2_506
  · exact le_trans (by norm_num) psum1179o2_507
  · exact le_trans (by norm_num) psum1179o2_508
  · exact le_trans (by norm_num) psum1179o2_509
  · exact le_trans (by norm_num) psum1179o2_510
  · exact le_trans (by norm_num) psum1179o2_511
  · exact le_trans (by norm_num) psum1179o2_512
  · exact le_trans (by norm_num) psum1179o2_513
  · exact le_trans (by norm_num) psum1179o2_514
  · exact le_trans (by norm_num) psum1179o2_515
  · exact le_trans (by norm_num) psum1179o2_516
  · exact le_trans (by norm_num) psum1179o2_517
  · exact le_trans (by norm_num) psum1179o2_518
  · exact le_trans (by norm_num) psum1179o2_519
  · exact le_trans (by norm_num) psum1179o2_520
  · exact le_trans (by norm_num) psum1179o2_521
  · exact le_trans (by norm_num) psum1179o2_522
  · exact le_trans (by norm_num) psum1179o2_523
  · exact le_trans (by norm_num) psum1179o2_524
  · exact le_trans (by norm_num) psum1179o2_525
  · exact le_trans (by norm_num) psum1179o2_526
  · exact le_trans (by norm_num) psum1179o2_527
  · exact le_trans (by norm_num) psum1179o2_528
  · exact le_trans (by norm_num) psum1179o2_529
  · exact le_trans (by norm_num) psum1179o2_530
  · exact le_trans (by norm_num) psum1179o2_531
  · exact le_trans (by norm_num) psum1179o2_532
  · exact le_trans (by norm_num) psum1179o2_533
  · exact le_trans (by norm_num) psum1179o2_534
  · exact le_trans (by norm_num) psum1179o2_535
  · exact le_trans (by norm_num) psum1179o2_536
  · exact le_trans (by norm_num) psum1179o2_537
  · exact le_trans (by norm_num) psum1179o2_538
  · exact le_trans (by norm_num) psum1179o2_539
  · exact le_trans (by norm_num) psum1179o2_540
  · exact le_trans (by norm_num) psum1179o2_541
  · exact le_trans (by norm_num) psum1179o2_542
  · exact le_trans (by norm_num) psum1179o2_543
  · exact le_trans (by norm_num) psum1179o2_544
  · exact le_trans (by norm_num) psum1179o2_545
  · exact le_trans (by norm_num) psum1179o2_546
  · exact le_trans (by norm_num) psum1179o2_547
  · exact le_trans (by norm_num) psum1179o2_548
  · exact le_trans (by norm_num) psum1179o2_549
  · exact le_trans (by norm_num) psum1179o2_550
  · exact le_trans (by norm_num) psum1179o2_551
  · exact le_trans (by norm_num) psum1179o2_552
  · exact le_trans (by norm_num) psum1179o2_553
  · exact le_trans (by norm_num) psum1179o2_554
  · exact le_trans (by norm_num) psum1179o2_555
  · exact le_trans (by norm_num) psum1179o2_556
  · exact le_trans (by norm_num) psum1179o2_557
  · exact le_trans (by norm_num) psum1179o2_558
  · exact le_trans (by norm_num) psum1179o2_559
  · exact le_trans (by norm_num) psum1179o2_560
  · exact le_trans (by norm_num) psum1179o2_561
  · exact le_trans (by norm_num) psum1179o2_562
  · exact le_trans (by norm_num) psum1179o2_563
  · exact le_trans (by norm_num) psum1179o2_564
  · exact le_trans (by norm_num) psum1179o2_565
  · exact le_trans (by norm_num) psum1179o2_566
  · exact le_trans (by norm_num) psum1179o2_567
  · exact le_trans (by norm_num) psum1179o2_568
  · exact le_trans (by norm_num) psum1179o2_569
  · exact le_trans (by norm_num) psum1179o2_570
  · exact le_trans (by norm_num) psum1179o2_571
  · exact le_trans (by norm_num) psum1179o2_572
  · exact le_trans (by norm_num) psum1179o2_573
  · exact le_trans (by norm_num) psum1179o2_574
  · exact le_trans (by norm_num) psum1179o2_575
  · exact le_trans (by norm_num) psum1179o2_576
  · exact le_trans (by norm_num) psum1179o2_577
  · exact le_trans (by norm_num) psum1179o2_578
  · exact le_trans (by norm_num) psum1179o2_579
  · exact le_trans (by norm_num) psum1179o2_580
  · exact le_trans (by norm_num) psum1179o2_581
  · exact le_trans (by norm_num) psum1179o2_582
  · exact le_trans (by norm_num) psum1179o2_583
  · exact le_trans (by norm_num) psum1179o2_584
  · exact le_trans (by norm_num) psum1179o2_585
  · exact le_trans (by norm_num) psum1179o2_586
  · exact le_trans (by norm_num) psum1179o2_587
  · exact le_trans (by norm_num) psum1179o2_588
  · exact le_trans (by norm_num) psum1179o2_589
  · exact le_trans (by norm_num) psum1179o2_590
  · exact le_trans (by norm_num) psum1179o2_591
  · exact le_trans (by norm_num) psum1179o2_592
  · exact le_trans (by norm_num) psum1179o2_593
  · exact le_trans (by norm_num) psum1179o2_594
  · exact le_trans (by norm_num) psum1179o2_595
  · exact le_trans (by norm_num) psum1179o2_596
  · exact le_trans (by norm_num) psum1179o2_597
  · exact le_trans (by norm_num) psum1179o2_598
  · exact le_trans (by norm_num) psum1179o2_599
  · exact le_trans (by norm_num) psum1179o2_600
  · exact le_trans (by norm_num) psum1179o2_601
  · exact le_trans (by norm_num) psum1179o2_602
  · exact le_trans (by norm_num) psum1179o2_603
  · exact le_trans (by norm_num) psum1179o2_604
  · exact le_trans (by norm_num) psum1179o2_605
  · exact le_trans (by norm_num) psum1179o2_606
  · exact le_trans (by norm_num) psum1179o2_607
  · exact le_trans (by norm_num) psum1179o2_608
  · exact le_trans (by norm_num) psum1179o2_609
  · exact le_trans (by norm_num) psum1179o2_610
  · exact le_trans (by norm_num) psum1179o2_611
  · exact le_trans (by norm_num) psum1179o2_612
  · exact le_trans (by norm_num) psum1179o2_613
  · exact le_trans (by norm_num) psum1179o2_614
  · exact le_trans (by norm_num) psum1179o2_615
  · exact le_trans (by norm_num) psum1179o2_616
  · exact le_trans (by norm_num) psum1179o2_617
  · exact le_trans (by norm_num) psum1179o2_618
  · exact le_trans (by norm_num) psum1179o2_619
  · exact le_trans (by norm_num) psum1179o2_620
  · exact le_trans (by norm_num) psum1179o2_621
  · exact le_trans (by norm_num) psum1179o2_622
  · exact le_trans (by norm_num) psum1179o2_623
  · exact le_trans (by norm_num) psum1179o2_624
  · exact le_trans (by norm_num) psum1179o2_625
  · exact le_trans (by norm_num) psum1179o2_626
  · exact le_trans (by norm_num) psum1179o2_627
  · exact le_trans (by norm_num) psum1179o2_628
  · exact le_trans (by norm_num) psum1179o2_629
  · exact le_trans (by norm_num) psum1179o2_630
  · exact le_trans (by norm_num) psum1179o2_631
  · exact le_trans (by norm_num) psum1179o2_632
  · exact le_trans (by norm_num) psum1179o2_633
  · exact le_trans (by norm_num) psum1179o2_634
  · exact le_trans (by norm_num) psum1179o2_635
  · exact le_trans (by norm_num) psum1179o2_636
  · exact le_trans (by norm_num) psum1179o2_637
  · exact le_trans (by norm_num) psum1179o2_638
  · exact le_trans (by norm_num) psum1179o2_639
  · exact le_trans (by norm_num) psum1179o2_640
  · exact le_trans (by norm_num) psum1179o2_641
  · exact le_trans (by norm_num) psum1179o2_642
  · exact le_trans (by norm_num) psum1179o2_643
  · exact le_trans (by norm_num) psum1179o2_644
  · exact le_trans (by norm_num) psum1179o2_645
  · exact le_trans (by norm_num) psum1179o2_646
  · exact le_trans (by norm_num) psum1179o2_647
  · exact le_trans (by norm_num) psum1179o2_648
  · exact le_trans (by norm_num) psum1179o2_649
  · exact le_trans (by norm_num) psum1179o2_650
  · exact le_trans (by norm_num) psum1179o2_651
  · exact le_trans (by norm_num) psum1179o2_652
  · exact le_trans (by norm_num) psum1179o2_653
  · exact le_trans (by norm_num) psum1179o2_654
  · exact le_trans (by norm_num) psum1179o2_655
  · exact le_trans (by norm_num) psum1179o2_656
  · exact le_trans (by norm_num) psum1179o2_657
  · exact le_trans (by norm_num) psum1179o2_658
  · exact le_trans (by norm_num) psum1179o2_659
  · exact le_trans (by norm_num) psum1179o2_660
  · exact le_trans (by norm_num) psum1179o2_661
  · exact le_trans (by norm_num) psum1179o2_662
  · exact le_trans (by norm_num) psum1179o2_663
  · exact le_trans (by norm_num) psum1179o2_664
  · exact le_trans (by norm_num) psum1179o2_665
  · exact le_trans (by norm_num) psum1179o2_666
  · exact le_trans (by norm_num) psum1179o2_667
  · exact le_trans (by norm_num) psum1179o2_668
  · exact le_trans (by norm_num) psum1179o2_669
  · exact le_trans (by norm_num) psum1179o2_670
  · exact le_trans (by norm_num) psum1179o2_671
  · exact le_trans (by norm_num) psum1179o2_672
  · exact le_trans (by norm_num) psum1179o2_673
  · exact le_trans (by norm_num) psum1179o2_674
  · exact le_trans (by norm_num) psum1179o2_675
  · exact le_trans (by norm_num) psum1179o2_676
  · exact le_trans (by norm_num) psum1179o2_677
  · exact le_trans (by norm_num) psum1179o2_678
  · exact le_trans (by norm_num) psum1179o2_679
  · exact le_trans (by norm_num) psum1179o2_680
  · exact le_trans (by norm_num) psum1179o2_681
  · exact le_trans (by norm_num) psum1179o2_682
  · exact le_trans (by norm_num) psum1179o2_683
  · exact le_trans (by norm_num) psum1179o2_684
  · exact le_trans (by norm_num) psum1179o2_685
  · exact le_trans (by norm_num) psum1179o2_686
  · exact le_trans (by norm_num) psum1179o2_687
  · exact le_trans (by norm_num) psum1179o2_688
  · exact le_trans (by norm_num) psum1179o2_689
  · exact le_trans (by norm_num) psum1179o2_690
  · exact le_trans (by norm_num) psum1179o2_691
  · exact le_trans (by norm_num) psum1179o2_692
  · exact le_trans (by norm_num) psum1179o2_693
  · exact le_trans (by norm_num) psum1179o2_694
  · exact le_trans (by norm_num) psum1179o2_695
  · exact le_trans (by norm_num) psum1179o2_696
  · exact le_trans (by norm_num) psum1179o2_697
  · exact le_trans (by norm_num) psum1179o2_698
  · exact le_trans (by norm_num) psum1179o2_699
  · exact le_trans (by norm_num) psum1179o2_700
  · exact le_trans (by norm_num) psum1179o2_701
  · exact le_trans (by norm_num) psum1179o2_702
  · exact le_trans (by norm_num) psum1179o2_703
  · exact le_trans (by norm_num) psum1179o2_704
  · exact le_trans (by norm_num) psum1179o2_705
  · exact le_trans (by norm_num) psum1179o2_706
  · exact le_trans (by norm_num) psum1179o2_707
  · exact le_trans (by norm_num) psum1179o2_708
  · exact le_trans (by norm_num) psum1179o2_709
  · exact le_trans (by norm_num) psum1179o2_710
  · exact le_trans (by norm_num) psum1179o2_711
  · exact le_trans (by norm_num) psum1179o2_712
  · exact le_trans (by norm_num) psum1179o2_713
  · exact le_trans (by norm_num) psum1179o2_714
  · exact le_trans (by norm_num) psum1179o2_715
  · exact le_trans (by norm_num) psum1179o2_716
  · exact le_trans (by norm_num) psum1179o2_717
  · exact le_trans (by norm_num) psum1179o2_718
  · exact le_trans (by norm_num) psum1179o2_719
  · exact le_trans (by norm_num) psum1179o2_720
  · exact le_trans (by norm_num) psum1179o2_721
  · exact le_trans (by norm_num) psum1179o2_722
  · exact le_trans (by norm_num) psum1179o2_723
  · exact le_trans (by norm_num) psum1179o2_724
  · exact le_trans (by norm_num) psum1179o2_725
  · exact le_trans (by norm_num) psum1179o2_726
  · exact le_trans (by norm_num) psum1179o2_727
  · exact le_trans (by norm_num) psum1179o2_728
  · exact le_trans (by norm_num) psum1179o2_729
  · exact le_trans (by norm_num) psum1179o2_730
  · exact le_trans (by norm_num) psum1179o2_731
  · exact le_trans (by norm_num) psum1179o2_732
  · exact le_trans (by norm_num) psum1179o2_733
  · exact le_trans (by norm_num) psum1179o2_734
  · exact le_trans (by norm_num) psum1179o2_735
  · exact le_trans (by norm_num) psum1179o2_736
  · exact le_trans (by norm_num) psum1179o2_737
  · exact le_trans (by norm_num) psum1179o2_738
  · exact le_trans (by norm_num) psum1179o2_739
  · exact le_trans (by norm_num) psum1179o2_740
  · exact le_trans (by norm_num) psum1179o2_741
  · exact le_trans (by norm_num) psum1179o2_742
  · exact le_trans (by norm_num) psum1179o2_743
  · exact le_trans (by norm_num) psum1179o2_744
  · exact le_trans (by norm_num) psum1179o2_745
  · exact le_trans (by norm_num) psum1179o2_746
  · exact le_trans (by norm_num) psum1179o2_747
  · exact le_trans (by norm_num) psum1179o2_748
  · exact le_trans (by norm_num) psum1179o2_749
  · exact le_trans (by norm_num) psum1179o2_750
  · exact le_trans (by norm_num) psum1179o2_751
  · exact le_trans (by norm_num) psum1179o2_752
  · exact le_trans (by norm_num) psum1179o2_753
  · exact le_trans (by norm_num) psum1179o2_754
  · exact le_trans (by norm_num) psum1179o2_755
  · exact le_trans (by norm_num) psum1179o2_756
  · exact le_trans (by norm_num) psum1179o2_757
  · exact le_trans (by norm_num) psum1179o2_758
  · exact le_trans (by norm_num) psum1179o2_759
  · exact le_trans (by norm_num) psum1179o2_760
  · exact le_trans (by norm_num) psum1179o2_761
  · exact le_trans (by norm_num) psum1179o2_762
  · exact le_trans (by norm_num) psum1179o2_763
  · exact le_trans (by norm_num) psum1179o2_764
  · exact le_trans (by norm_num) psum1179o2_765
  · exact le_trans (by norm_num) psum1179o2_766
  · exact le_trans (by norm_num) psum1179o2_767
  · exact le_trans (by norm_num) psum1179o2_768
  · exact le_trans (by norm_num) psum1179o2_769
  · exact le_trans (by norm_num) psum1179o2_770
  · exact le_trans (by norm_num) psum1179o2_771
  · exact le_trans (by norm_num) psum1179o2_772
  · exact le_trans (by norm_num) psum1179o2_773
  · exact le_trans (by norm_num) psum1179o2_774
  · exact le_trans (by norm_num) psum1179o2_775
  · exact le_trans (by norm_num) psum1179o2_776
  · exact le_trans (by norm_num) psum1179o2_777
  · exact le_trans (by norm_num) psum1179o2_778
  · exact le_trans (by norm_num) psum1179o2_779
  · exact le_trans (by norm_num) psum1179o2_780
  · exact le_trans (by norm_num) psum1179o2_781
  · exact le_trans (by norm_num) psum1179o2_782
  · exact le_trans (by norm_num) psum1179o2_783
  · exact le_trans (by norm_num) psum1179o2_784
  · exact le_trans (by norm_num) psum1179o2_785
  · exact le_trans (by norm_num) psum1179o2_786
  · exact le_trans (by norm_num) psum1179o2_787
  · exact le_trans (by norm_num) psum1179o2_788
  · exact le_trans (by norm_num) psum1179o2_789
  · exact le_trans (by norm_num) psum1179o2_790
  · exact le_trans (by norm_num) psum1179o2_791
  · exact le_trans (by norm_num) psum1179o2_792
  · exact le_trans (by norm_num) psum1179o2_793
  · exact le_trans (by norm_num) psum1179o2_794
  · exact le_trans (by norm_num) psum1179o2_795
  · exact le_trans (by norm_num) psum1179o2_796
  · exact le_trans (by norm_num) psum1179o2_797
  · exact le_trans (by norm_num) psum1179o2_798
  · exact le_trans (by norm_num) psum1179o2_799
  · exact le_trans (by norm_num) psum1179o2_800
  · exact le_trans (by norm_num) psum1179o2_801
  · exact le_trans (by norm_num) psum1179o2_802
  · exact le_trans (by norm_num) psum1179o2_803
  · exact le_trans (by norm_num) psum1179o2_804
  · exact le_trans (by norm_num) psum1179o2_805
  · exact le_trans (by norm_num) psum1179o2_806
  · exact le_trans (by norm_num) psum1179o2_807
  · exact le_trans (by norm_num) psum1179o2_808
  · exact le_trans (by norm_num) psum1179o2_809
  · exact le_trans (by norm_num) psum1179o2_810
  · exact le_trans (by norm_num) psum1179o2_811
  · exact le_trans (by norm_num) psum1179o2_812
  · exact le_trans (by norm_num) psum1179o2_813
  · exact le_trans (by norm_num) psum1179o2_814
  · exact le_trans (by norm_num) psum1179o2_815
  · exact le_trans (by norm_num) psum1179o2_816
  · exact le_trans (by norm_num) psum1179o2_817
  · exact le_trans (by norm_num) psum1179o2_818
  · exact le_trans (by norm_num) psum1179o2_819
  · exact le_trans (by norm_num) psum1179o2_820
  · exact le_trans (by norm_num) psum1179o2_821
  · exact le_trans (by norm_num) psum1179o2_822
  · exact le_trans (by norm_num) psum1179o2_823
  · exact le_trans (by norm_num) psum1179o2_824
  · exact le_trans (by norm_num) psum1179o2_825
  · exact le_trans (by norm_num) psum1179o2_826
  · exact le_trans (by norm_num) psum1179o2_827
  · exact le_trans (by norm_num) psum1179o2_828
  · exact le_trans (by norm_num) psum1179o2_829
  · exact le_trans (by norm_num) psum1179o2_830
  · exact le_trans (by norm_num) psum1179o2_831
  · exact le_trans (by norm_num) psum1179o2_832
  · exact le_trans (by norm_num) psum1179o2_833
  · exact le_trans (by norm_num) psum1179o2_834
  · exact le_trans (by norm_num) psum1179o2_835
  · exact le_trans (by norm_num) psum1179o2_836
  · exact le_trans (by norm_num) psum1179o2_837
  · exact le_trans (by norm_num) psum1179o2_838
  · exact le_trans (by norm_num) psum1179o2_839
  · exact le_trans (by norm_num) psum1179o2_840
  · exact le_trans (by norm_num) psum1179o2_841
  · exact le_trans (by norm_num) psum1179o2_842
  · exact le_trans (by norm_num) psum1179o2_843
  · exact le_trans (by norm_num) psum1179o2_844
  · exact le_trans (by norm_num) psum1179o2_845
  · exact le_trans (by norm_num) psum1179o2_846
  · exact le_trans (by norm_num) psum1179o2_847
  · exact le_trans (by norm_num) psum1179o2_848
  · exact le_trans (by norm_num) psum1179o2_849
  · exact le_trans (by norm_num) psum1179o2_850
  · exact le_trans (by norm_num) psum1179o2_851
  · exact le_trans (by norm_num) psum1179o2_852
  · exact le_trans (by norm_num) psum1179o2_853
  · exact le_trans (by norm_num) psum1179o2_854
  · exact le_trans (by norm_num) psum1179o2_855
  · exact le_trans (by norm_num) psum1179o2_856
  · exact le_trans (by norm_num) psum1179o2_857
  · exact le_trans (by norm_num) psum1179o2_858
  · exact le_trans (by norm_num) psum1179o2_859
  · exact le_trans (by norm_num) psum1179o2_860
  · exact le_trans (by norm_num) psum1179o2_861
  · exact le_trans (by norm_num) psum1179o2_862
  · exact le_trans (by norm_num) psum1179o2_863
  · exact le_trans (by norm_num) psum1179o2_864
  · exact le_trans (by norm_num) psum1179o2_865
  · exact le_trans (by norm_num) psum1179o2_866
  · exact le_trans (by norm_num) psum1179o2_867
  · exact le_trans (by norm_num) psum1179o2_868
  · exact le_trans (by norm_num) psum1179o2_869
  · exact le_trans (by norm_num) psum1179o2_870
  · exact le_trans (by norm_num) psum1179o2_871
  · exact le_trans (by norm_num) psum1179o2_872
  · exact le_trans (by norm_num) psum1179o2_873
  · exact le_trans (by norm_num) psum1179o2_874
  · exact le_trans (by norm_num) psum1179o2_875
  · exact le_trans (by norm_num) psum1179o2_876
  · exact le_trans (by norm_num) psum1179o2_877
  · exact le_trans (by norm_num) psum1179o2_878
  · exact le_trans (by norm_num) psum1179o2_879
  · exact le_trans (by norm_num) psum1179o2_880
  · exact le_trans (by norm_num) psum1179o2_881
  · exact le_trans (by norm_num) psum1179o2_882
  · exact le_trans (by norm_num) psum1179o2_883
  · exact le_trans (by norm_num) psum1179o2_884
  · exact le_trans (by norm_num) psum1179o2_885
  · exact le_trans (by norm_num) psum1179o2_886
  · exact le_trans (by norm_num) psum1179o2_887
  · exact le_trans (by norm_num) psum1179o2_888
  · exact le_trans (by norm_num) psum1179o2_889
  · exact le_trans (by norm_num) psum1179o2_890
  · exact le_trans (by norm_num) psum1179o2_891
  · exact le_trans (by norm_num) psum1179o2_892
  · exact le_trans (by norm_num) psum1179o2_893
  · exact le_trans (by norm_num) psum1179o2_894
  · exact le_trans (by norm_num) psum1179o2_895
  · exact le_trans (by norm_num) psum1179o2_896
  · exact le_trans (by norm_num) psum1179o2_897
  · exact le_trans (by norm_num) psum1179o2_898
  · exact le_trans (by norm_num) psum1179o2_899
  · exact le_trans (by norm_num) psum1179o2_900
  · exact le_trans (by norm_num) psum1179o2_901
  · exact le_trans (by norm_num) psum1179o2_902
  · exact le_trans (by norm_num) psum1179o2_903
  · exact le_trans (by norm_num) psum1179o2_904
  · exact le_trans (by norm_num) psum1179o2_905
  · exact le_trans (by norm_num) psum1179o2_906
  · exact le_trans (by norm_num) psum1179o2_907
  · exact le_trans (by norm_num) psum1179o2_908
  · exact le_trans (by norm_num) psum1179o2_909
  · exact le_trans (by norm_num) psum1179o2_910
  · exact le_trans (by norm_num) psum1179o2_911
  · exact le_trans (by norm_num) psum1179o2_912
  · exact le_trans (by norm_num) psum1179o2_913
  · exact le_trans (by norm_num) psum1179o2_914
  · exact le_trans (by norm_num) psum1179o2_915
  · exact le_trans (by norm_num) psum1179o2_916
  · exact le_trans (by norm_num) psum1179o2_917
  · exact le_trans (by norm_num) psum1179o2_918
  · exact le_trans (by norm_num) psum1179o2_919
  · exact le_trans (by norm_num) psum1179o2_920
  · exact le_trans (by norm_num) psum1179o2_921
  · exact le_trans (by norm_num) psum1179o2_922
  · exact le_trans (by norm_num) psum1179o2_923
  · exact le_trans (by norm_num) psum1179o2_924
  · exact le_trans (by norm_num) psum1179o2_925
  · exact le_trans (by norm_num) psum1179o2_926
  · exact le_trans (by norm_num) psum1179o2_927
  · exact le_trans (by norm_num) psum1179o2_928
  · exact le_trans (by norm_num) psum1179o2_929
  · exact le_trans (by norm_num) psum1179o2_930
  · exact le_trans (by norm_num) psum1179o2_931
  · exact le_trans (by norm_num) psum1179o2_932
  · exact le_trans (by norm_num) psum1179o2_933
  · exact le_trans (by norm_num) psum1179o2_934
  · exact le_trans (by norm_num) psum1179o2_935
  · exact le_trans (by norm_num) psum1179o2_936
  · exact le_trans (by norm_num) psum1179o2_937
  · exact le_trans (by norm_num) psum1179o2_938
  · exact le_trans (by norm_num) psum1179o2_939
  · exact le_trans (by norm_num) psum1179o2_940
  · exact le_trans (by norm_num) psum1179o2_941
  · exact le_trans (by norm_num) psum1179o2_942
  · exact le_trans (by norm_num) psum1179o2_943
  · exact le_trans (by norm_num) psum1179o2_944
  · exact le_trans (by norm_num) psum1179o2_945
  · exact le_trans (by norm_num) psum1179o2_946
  · exact le_trans (by norm_num) psum1179o2_947
  · exact le_trans (by norm_num) psum1179o2_948
  · exact le_trans (by norm_num) psum1179o2_949
  · exact le_trans (by norm_num) psum1179o2_950
  · exact le_trans (by norm_num) psum1179o2_951
  · exact le_trans (by norm_num) psum1179o2_952
  · exact le_trans (by norm_num) psum1179o2_953
  · exact le_trans (by norm_num) psum1179o2_954
  · exact le_trans (by norm_num) psum1179o2_955
  · exact le_trans (by norm_num) psum1179o2_956
  · exact le_trans (by norm_num) psum1179o2_957
  · exact le_trans (by norm_num) psum1179o2_958
  · exact le_trans (by norm_num) psum1179o2_959
  · exact le_trans (by norm_num) psum1179o2_960
  · exact le_trans (by norm_num) psum1179o2_961
  · exact le_trans (by norm_num) psum1179o2_962
  · exact le_trans (by norm_num) psum1179o2_963
  · exact le_trans (by norm_num) psum1179o2_964
  · exact le_trans (by norm_num) psum1179o2_965
  · exact le_trans (by norm_num) psum1179o2_966
  · exact le_trans (by norm_num) psum1179o2_967
  · exact le_trans (by norm_num) psum1179o2_968
  · exact le_trans (by norm_num) psum1179o2_969
  · exact le_trans (by norm_num) psum1179o2_970
  · exact le_trans (by norm_num) psum1179o2_971
  · exact le_trans (by norm_num) psum1179o2_972
  · exact le_trans (by norm_num) psum1179o2_973
  · exact le_trans (by norm_num) psum1179o2_974
  · exact le_trans (by norm_num) psum1179o2_975
  · exact le_trans (by norm_num) psum1179o2_976
  · exact le_trans (by norm_num) psum1179o2_977
  · exact le_trans (by norm_num) psum1179o2_978
  · exact le_trans (by norm_num) psum1179o2_979
  · exact le_trans (by norm_num) psum1179o2_980
  · exact le_trans (by norm_num) psum1179o2_981
  · exact le_trans (by norm_num) psum1179o2_982
  · exact le_trans (by norm_num) psum1179o2_983
  · exact le_trans (by norm_num) psum1179o2_984
  · exact le_trans (by norm_num) psum1179o2_985
  · exact le_trans (by norm_num) psum1179o2_986
  · exact le_trans (by norm_num) psum1179o2_987
  · exact le_trans (by norm_num) psum1179o2_988
  · exact le_trans (by norm_num) psum1179o2_989
  · exact le_trans (by norm_num) psum1179o2_990
  · exact le_trans (by norm_num) psum1179o2_991
  · exact le_trans (by norm_num) psum1179o2_992
  · exact le_trans (by norm_num) psum1179o2_993
  · exact le_trans (by norm_num) psum1179o2_994
  · exact le_trans (by norm_num) psum1179o2_995
  · exact le_trans (by norm_num) psum1179o2_996
  · exact le_trans (by norm_num) psum1179o2_997
  · exact le_trans (by norm_num) psum1179o2_998
  · exact le_trans (by norm_num) psum1179o2_999
  · exact le_trans (by norm_num) psum1179o2_1000

end CriticalLinePhasor.DVP

section AxiomAudit
#print axioms CriticalLinePhasor.DVP.psum1179o2_floor
#print axioms CriticalLinePhasor.DVP.psum1179o2_1000
end AxiomAudit
