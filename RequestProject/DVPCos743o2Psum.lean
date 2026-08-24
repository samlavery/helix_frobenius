import RequestProject.DVPCos743o2Table

/-!
# The cosine partial-sum floor, `t = 743/2` (N = 500)
-/

open Finset

noncomputable section

namespace CriticalLinePhasor.DVP

/-- The cosine sequence of the `t = 743/2` segment certificate. -/
def cos743o2c (n : ℕ) : ℝ := Real.cos (((743:ℕ):ℝ) * (Real.log n / 2))

theorem psum743o2_11 : ((2743/15625 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 11, cos743o2c k := by
  rw [Finset.Icc_self, Finset.sum_singleton]
  have h : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 11 - ((43913/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_11).1
  push_cast at h ⊢
  linarith

theorem psum743o2_12 : ((1059931/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 12, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 12, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 11, cos743o2c k) + cos743o2c 12 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 11) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_11
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 12 - ((884479/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_12).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_13 : ((249791/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 13, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 13, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 12, cos743o2c k) + cos743o2c 13 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 12) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_12
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 13 - ((-560249/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_13).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_14 : ((368121/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 14, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 14, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 13, cos743o2c k) + cos743o2c 14 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 13) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_13
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 14 - ((486501/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_14).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_15 : ((2216879/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 15, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 15, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 14, cos743o2c k) + cos743o2c 15 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 14) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_14
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 15 - ((148899/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_15).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_16 : ((3127541/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 16, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 16, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 15, cos743o2c k) + cos743o2c 16 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 15) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_15
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 16 - ((455381/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_16).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_17 : ((533243/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 17, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 17, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 16, cos743o2c k) + cos743o2c 17 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 16) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_16
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 17 - ((-994469/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_17).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_18 : ((2927997/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 18, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 18, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 17, cos743o2c k) + cos743o2c 18 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 17) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_17
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 18 - ((6361/8000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_18).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_19 : ((752341/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 19, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 19, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 18, cos743o2c k) + cos743o2c 19 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 18) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_18
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 19 - ((52113/62500 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_19).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_20 : ((446493/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 20, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 20, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 19, cos743o2c k) + cos743o2c 20 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 19) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_19
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 20 - ((28133/40000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_20).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_21 : ((1365651/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 21, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 21, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 20, cos743o2c k) + cos743o2c 21 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 20) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_20
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 21 - ((498887/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_21).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_22 : ((2766301/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 22, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 22, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 21, cos743o2c k) + cos743o2c 22 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 21) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_21
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 22 - ((35049/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_22).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_23 : ((952859/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 23, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 23, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 22, cos743o2c k) + cos743o2c 23 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 22) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_22
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 23 - ((-768207/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_23).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_24 : ((1118823/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 24, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 24, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 23, cos743o2c k) + cos743o2c 24 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 23) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_23
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 24 - ((5187/6250 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_24).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_25 : ((5171359/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 25, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 25, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 24, cos743o2c k) + cos743o2c 25 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 24) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_24
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 25 - ((-6604/15625 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_25).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_26 : ((4526201/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 26, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 26, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 25, cos743o2c k) + cos743o2c 26 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 25) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_25
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 26 - ((-322529/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_26).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_27 : ((5209969/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 27, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 27, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 26, cos743o2c k) + cos743o2c 27 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 26) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_26
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 27 - ((170967/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_27).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_28 : ((155047/25000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 28, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 28, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 27, cos743o2c k) + cos743o2c 28 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 27) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_27
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 28 - ((992011/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_28).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_29 : ((7029069/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 29, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 29, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 28, cos743o2c k) + cos743o2c 29 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 28) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_28
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 29 - ((827289/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_29).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_30 : ((980023/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 30, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 30, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 29, cos743o2c k) + cos743o2c 30 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 29) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_29
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 30 - ((162243/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_30).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_31 : ((4405753/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 31, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 31, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 30, cos743o2c k) + cos743o2c 31 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 30) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_30
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 31 - ((485711/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_31).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_32 : ((4836579/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 32, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 32, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 31, cos743o2c k) + cos743o2c 32 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 31) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_31
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 32 - ((107719/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_32).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_33 : ((4788599/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 33, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 33, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 32, cos743o2c k) + cos743o2c 33 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 32) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_32
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 33 - ((-4793/50000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_33).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_34 : ((8577099/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 34, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 34, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 33, cos743o2c k) + cos743o2c 34 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 33) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_33
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 34 - ((-999999/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_34).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_35 : ((8802941/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 35, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 35, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 34, cos743o2c k) + cos743o2c 35 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 34) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_34
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 35 - ((112971/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_35).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_36 : ((9529057/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 36, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 36, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 35, cos743o2c k) + cos743o2c 36 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 35) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_35
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 36 - ((90777/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_36).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_37 : ((1705793/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 37, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 37, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 36, cos743o2c k) + cos743o2c 37 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 36) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_36
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 37 - ((-124999/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_37).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_38 : ((9416591/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 38, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 38, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 37, cos743o2c k) + cos743o2c 38 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 37) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_37
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 38 - ((443863/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_38).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_39 : ((865393/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 39, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 39, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 38, cos743o2c k) + cos743o2c 39 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 38) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_38
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 39 - ((-762561/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_39).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_40 : ((235717/25000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 40, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 40, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 39, cos743o2c k) + cos743o2c 40 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 39) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_39
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 40 - ((15497/20000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_40).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_41 : ((4260401/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 41, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 41, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 40, cos743o2c k) + cos743o2c 41 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 40) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_40
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 41 - ((-453889/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_41).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_42 : ((1903983/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 42, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 42, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 41, cos743o2c k) + cos743o2c 42 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 41) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_41
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 42 - ((999213/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_42).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_43 : ((2192477/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 43, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 43, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 42, cos743o2c k) + cos743o2c 43 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 42) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_42
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 43 - ((-749907/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_43).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_44 : ((4366779/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 44, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 44, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 43, cos743o2c k) + cos743o2c 44 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 43) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_43
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 44 - ((-29/800 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_44).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_45 : ((9630217/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 45, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 45, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 44, cos743o2c k) + cos743o2c 45 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 44) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_44
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 45 - ((896759/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_45).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_46 : ((8934279/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 46, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 46, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 45, cos743o2c k) + cos743o2c 46 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 45) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_45
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 46 - ((-347919/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_46).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_47 : ((8316647/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 47, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 47, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 46, cos743o2c k) + cos743o2c 47 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 46) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_46
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 47 - ((-154383/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_47).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_48 : ((4541259/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 48, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 48, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 47, cos743o2c k) + cos743o2c 48 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 47) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_47
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 48 - ((765971/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_48).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_49 : ((9860869/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 49, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 49, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 48, cos743o2c k) + cos743o2c 49 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 48) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_48
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 49 - ((778451/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_49).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_50 : ((9536763/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 50, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 50, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 49, cos743o2c k) + cos743o2c 50 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 49) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_49
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 50 - ((-162003/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_50).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_51 : ((4275317/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 51, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 51, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 50, cos743o2c k) + cos743o2c 51 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 50) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_50
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 51 - ((-986029/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_51).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_52 : ((1956991/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 52, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 52, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 51, cos743o2c k) + cos743o2c 52 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 51) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_51
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 52 - ((-72257/100000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_52).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_53 : ((7813573/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 53, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 53, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 52, cos743o2c k) + cos743o2c 53 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 52) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_52
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 53 - ((-14291/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_53).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_54 : ((420799/50000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 54, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 54, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 53, cos743o2c k) + cos743o2c 54 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 53) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_53
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 54 - ((602507/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_54).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_55 : ((9340541/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 55, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 55, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 54, cos743o2c k) + cos743o2c 55 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 54) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_54
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 55 - ((924661/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_55).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_56 : ((129253/12500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 56, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 56, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 55, cos743o2c k) + cos743o2c 56 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 55) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_55
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 56 - ((999799/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_56).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_57 : ((2258357/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 57, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 57, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 56, cos743o2c k) + cos743o2c 57 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 56) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_56
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 57 - ((190329/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_57).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_58 : ((6086981/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 58, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 58, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 57, cos743o2c k) + cos743o2c 58 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 57) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_57
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 58 - ((882277/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_58).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_59 : ((13022441/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 59, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 59, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 58, cos743o2c k) + cos743o2c 59 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 58) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_58
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 59 - ((848579/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_59).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_60 : ((555643/40000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 60, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 60, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 59, cos743o2c k) + cos743o2c 60 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 59) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_59
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 60 - ((434367/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_60).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_61 : ((14821261/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 61, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 61, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 60, cos743o2c k) + cos743o2c 61 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 60) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_60
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 61 - ((465143/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_61).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_62 : ((988269/62500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 62, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 62, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 61, cos743o2c k) + cos743o2c 62 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 61) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_61
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 62 - ((991143/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_62).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_63 : ((16791093/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 63, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 63, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 62, cos743o2c k) + cos743o2c 63 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 62) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_62
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 63 - ((978889/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_63).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_64 : ((4398491/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 64, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 64, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 63, cos743o2c k) + cos743o2c 64 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 63) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_63
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 64 - ((802971/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_64).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_65 : ((8995727/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 65, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 65, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 64, cos743o2c k) + cos743o2c 65 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 64) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_64
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 65 - ((39759/100000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_65).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_66 : ((17790313/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 66, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 66, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 65, cos743o2c k) + cos743o2c 66 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 65) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_65
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 66 - ((-201041/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_66).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_67 : ((4251873/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 67, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 67, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 66, cos743o2c k) + cos743o2c 67 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 66) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_66
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 67 - ((-782721/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_67).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_68 : ((2001647/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 68, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 68, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 67, cos743o2c k) + cos743o2c 68 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 67) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_67
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 68 - ((-124277/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_68).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_69 : ((15445581/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 69, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 69, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 68, cos743o2c k) + cos743o2c 69 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 68) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_68
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 69 - ((-113499/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_69).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_70 : ((15773611/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 70, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 70, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 69, cos743o2c k) + cos743o2c 70 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 69) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_69
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 70 - ((32813/100000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_70).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_71 : ((16748779/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 71, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 71, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 70, cos743o2c k) + cos743o2c 71 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 70) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_70
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 71 - ((243817/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_71).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_72 : ((1739777/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 72, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 72, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 71, cos743o2c k) + cos743o2c 72 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 71) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_71
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 72 - ((649091/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_72).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_73 : ((16960377/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 73, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 73, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 72, cos743o2c k) + cos743o2c 73 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 72) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_72
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 73 - ((-437293/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_73).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_74 : ((127731/8000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 74, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 74, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 73, cos743o2c k) + cos743o2c 74 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 73) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_73
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 74 - ((-496951/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_74).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_75 : ((1975401/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 75, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 75, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 74, cos743o2c k) + cos743o2c 75 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 74) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_74
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 75 - ((-163067/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_75).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_76 : ((1673471/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 76, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 76, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 75, cos743o2c k) + cos743o2c 76 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 75) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_75
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 76 - ((465801/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_76).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_77 : ((689117/40000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 77, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 77, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 76, cos743o2c k) + cos743o2c 77 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 76) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_76
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 77 - ((98663/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_77).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_78 : ((16400867/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 78, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 78, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 77, cos743o2c k) + cos743o2c 78 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 77) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_77
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 78 - ((-413479/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_78).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_79 : ((3164391/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 79, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 79, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 78, cos743o2c k) + cos743o2c 79 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 78) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_78
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 79 - ((-144703/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_79).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_80 : ((16659463/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 80, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 80, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 79, cos743o2c k) + cos743o2c 80 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 79) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_79
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 80 - ((104701/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_80).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_81 : ((4280391/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 81, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 81, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 80, cos743o2c k) + cos743o2c 81 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 80) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_80
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 81 - ((462201/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_81).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_82 : ((16174271/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 82, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 82, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 81, cos743o2c k) + cos743o2c 82 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 81) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_81
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 82 - ((-947193/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_82).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_83 : ((16057299/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 83, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 83, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 82, cos743o2c k) + cos743o2c 83 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 82) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_82
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 83 - ((-14609/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_83).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_84 : ((1065409/62500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 84, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 84, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 83, cos743o2c k) + cos743o2c 84 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 83) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_83
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 84 - ((197869/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_84).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_85 : ((3320141/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 85, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 85, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 84, cos743o2c k) + cos743o2c 85 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 84) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_84
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 85 - ((-445739/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_85).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_86 : ((15925231/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 86, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 86, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 85, cos743o2c k) + cos743o2c 86 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 85) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_85
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 86 - ((-337687/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_86).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_87 : ((8436557/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 87, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 87, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 86, cos743o2c k) + cos743o2c 87 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 86) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_86
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 87 - ((947983/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_87).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_88 : ((16730827/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 88, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 88, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 87, cos743o2c k) + cos743o2c 88 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 87) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_87
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 88 - ((-142187/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_88).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_89 : ((15939079/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 89, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 89, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 88, cos743o2c k) + cos743o2c 89 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 88) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_88
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 89 - ((-24739/31250 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_89).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_90 : ((8438833/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 90, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 90, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 89, cos743o2c k) + cos743o2c 90 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 89) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_89
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 90 - ((938687/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_90).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_91 : ((4156239/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 91, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 91, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 90, cos743o2c k) + cos743o2c 91 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 90) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_90
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 91 - ((-25261/100000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_91).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_92 : ((4002309/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 92, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 92, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 91, cos743o2c k) + cos743o2c 92 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 91) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_91
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 92 - ((-30781/50000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_92).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_93 : ((17008593/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 93, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 93, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 92, cos743o2c k) + cos743o2c 93 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 92) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_92
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 93 - ((999457/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_93).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_94 : ((8155443/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 94, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 94, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 93, cos743o2c k) + cos743o2c 94 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 93) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_93
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 94 - ((-697607/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_94).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_95 : ((16293181/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 95, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 95, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 94, cos743o2c k) + cos743o2c 95 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 94) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_94
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 95 - ((-3521/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_95).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_96 : ((4246603/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 96, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 96, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 95, cos743o2c k) + cos743o2c 96 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 95) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_95
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 96 - ((693331/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_96).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_97 : ((3198193/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 97, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 97, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 96, cos743o2c k) + cos743o2c 97 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 96) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_96
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 97 - ((-995347/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_97).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_98 : ((8415791/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 98, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 98, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 97, cos743o2c k) + cos743o2c 98 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 97) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_97
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 98 - ((840717/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_98).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_99 : ((4117797/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 99, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 99, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 98, cos743o2c k) + cos743o2c 99 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 98) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_98
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 99 - ((-180147/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_99).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_100 : ((16249433/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 100, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 100, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 99, cos743o2c k) + cos743o2c 100 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 99) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_99
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 100 - ((-44331/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_100).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_101 : ((847577/50000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 101, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 101, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 100, cos743o2c k) + cos743o2c 101 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 100) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_100
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 101 - ((702207/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_101).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_102 : ((15988681/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 102, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 102, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 101, cos743o2c k) + cos743o2c 102 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 101) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_101
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 102 - ((-962759/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_102).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_103 : ((16966813/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 103, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 103, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 102, cos743o2c k) + cos743o2c 103 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 102) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_102
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 103 - ((122279/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_103).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_104 : ((252731/15625 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 104, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 104, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 103, cos743o2c k) + cos743o2c 104 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 103) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_103
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 104 - ((-791929/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_104).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_105 : ((2081817/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 105, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 105, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 104, cos743o2c k) + cos743o2c 105 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 104) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_104
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 105 - ((119963/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_105).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_106 : ((4133497/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 106, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 106, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 105, cos743o2c k) + cos743o2c 106 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 105) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_105
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 106 - ((-1882/15625 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_106).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_107 : ((1630983/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 107, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 107, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 106, cos743o2c k) + cos743o2c 107 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 106) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_106
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 107 - ((-112029/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_107).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_108 : ((16824059/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 108, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 108, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 107, cos743o2c k) + cos743o2c 108 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 107) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_107
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 108 - ((514329/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_108).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_109 : ((8045521/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 109, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 109, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 108, cos743o2c k) + cos743o2c 109 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 108) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_108
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 109 - ((-732917/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_109).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_110 : ((2121241/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 110, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 110, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 109, cos743o2c k) + cos743o2c 110 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 109) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_109
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 110 - ((439493/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_110).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_111 : ((4001961/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 111, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 111, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 110, cos743o2c k) + cos743o2c 111 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 110) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_110
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 111 - ((-15031/15625 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_111).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_112 : ((1062751/62500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 112, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 112, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 111, cos743o2c k) + cos743o2c 112 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 111) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_111
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 112 - ((62267/62500 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_112).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_113 : ((8003337/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 113, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 113, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 112, cos743o2c k) + cos743o2c 113 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 112) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_112
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 113 - ((-498621/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_113).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_114 : ((2123183/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 114, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 114, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 113, cos743o2c k) + cos743o2c 114 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 113) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_113
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 114 - ((97889/100000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_114).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_115 : ((1603267/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 115, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 115, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 114, cos743o2c k) + cos743o2c 115 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 114) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_114
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 115 - ((-476347/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_115).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_116 : ((16959867/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 116, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 116, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 115, cos743o2c k) + cos743o2c 116 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 115) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_115
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 116 - ((927297/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_116).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_117 : ((16051201/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 117, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 117, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 116, cos743o2c k) + cos743o2c 117 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 116) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_116
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 117 - ((-454283/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_117).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_118 : ((16951073/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 118, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 118, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 117, cos743o2c k) + cos743o2c 118 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 117) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_117
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 118 - ((224993/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_118).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_119 : ((2006019/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 119, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 119, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 118, cos743o2c k) + cos743o2c 119 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 118) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_118
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 119 - ((-902821/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_119).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_120 : ((16964477/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 120, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 120, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 119, cos743o2c k) + cos743o2c 120 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 119) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_119
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 120 - ((36657/40000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_120).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_121 : ((16026091/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 121, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 121, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 120, cos743o2c k) + cos743o2c 121 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 120) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_120
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 121 - ((-469143/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_121).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_122 : ((16989977/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 122, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 122, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 121, cos743o2c k) + cos743o2c 122 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 121) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_121
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 122 - ((481993/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_122).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_123 : ((4000673/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 123, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 123, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 122, cos743o2c k) + cos743o2c 123 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 122) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_122
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 123 - ((-197437/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_123).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_124 : ((17002233/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 124, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 124, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 123, cos743o2c k) + cos743o2c 124 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 123) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_123
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 124 - ((999641/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_124).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_125 : ((16010681/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 125, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 125, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 124, cos743o2c k) + cos743o2c 125 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 124) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_124
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 125 - ((-247863/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_125).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_126 : ((678489/40000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 126, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 126, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 125, cos743o2c k) + cos743o2c 126 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 125) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_125
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 126 - ((237911/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_126).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_127 : ((16092869/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 127, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 127, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 126, cos743o2c k) + cos743o2c 127 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 126) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_126
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 127 - ((-108657/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_127).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_128 : ((8413947/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 128, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 128, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 127, cos743o2c k) + cos743o2c 128 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 127) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_127
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 128 - ((5881/8000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_128).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_129 : ((16283669/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 129, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 129, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 128, cos743o2c k) + cos743o2c 129 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 128) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_128
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 129 - ((-4353/8000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_129).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_130 : ((8290727/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 130, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 130, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 129, cos743o2c k) + cos743o2c 130 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 129) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_129
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 130 - ((59577/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_130).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_131 : ((16573703/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 131, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 131, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 130, cos743o2c k) + cos743o2c 131 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 130) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_130
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 131 - ((-7651/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_131).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_132 : ((2033707/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 132, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 132, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 131, cos743o2c k) + cos743o2c 132 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 131) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_131
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 132 - ((-303947/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_132).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_133 : ((3374413/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 133, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 133, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 132, cos743o2c k) + cos743o2c 133 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 132) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_132
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 133 - ((602509/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_133).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_134 : ((8013779/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 134, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 134, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 133, cos743o2c k) + cos743o2c 134 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 133) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_133
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 134 - ((-844407/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_134).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_135 : ((17010241/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 135, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 135, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 134, cos743o2c k) + cos743o2c 135 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 134) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_134
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 135 - ((982783/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_135).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_136 : ((16032963/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 136, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 136, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 135, cos743o2c k) + cos743o2c 136 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 135) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_135
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 136 - ((-488589/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_136).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_137 : ((16838527/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 137, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 137, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 136, cos743o2c k) + cos743o2c 137 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 136) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_136
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 137 - ((25177/31250 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_137).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_138 : ((4090407/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 138, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 138, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 137, cos743o2c k) + cos743o2c 138 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 137) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_137
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 138 - ((-476799/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_138).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_139 : ((8199639/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 139, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 139, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 138, cos743o2c k) + cos743o2c 139 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 138) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_138
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 139 - ((151/4000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_139).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_140 : ((16825783/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 140, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 140, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 139, cos743o2c k) + cos743o2c 140 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 139) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_139
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 140 - ((85321/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_140).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_141 : ((16019179/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 141, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 141, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 140, cos743o2c k) + cos743o2c 141 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 140) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_140
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 141 - ((-100813/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_141).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_142 : ((8506153/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 142, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 142, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 141, cos743o2c k) + cos743o2c 142 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 141) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_141
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 142 - ((993227/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_142).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_143 : ((2012293/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 143, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 143, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 142, cos743o2c k) + cos743o2c 143 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 142) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_142
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 143 - ((-456931/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_143).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_144 : ((4165709/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 144, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 144, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 143, cos743o2c k) + cos743o2c 144 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 143) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_143
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 144 - ((35287/62500 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_144).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_145 : ((16633429/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 145, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 145, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 144, cos743o2c k) + cos743o2c 145 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 144) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_144
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 145 - ((-29307/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_145).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_146 : ((16102991/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 146, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 146, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 145, cos743o2c k) + cos743o2c 146 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 145) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_145
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 146 - ((-265169/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_146).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_147 : ((4255397/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 147, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 147, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 146, cos743o2c k) + cos743o2c 147 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 146) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_146
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 147 - ((918697/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_147).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_148 : ((401123/25000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 148, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 148, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 147, cos743o2c k) + cos743o2c 148 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 147) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_147
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 148 - ((-122071/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_148).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_149 : ((16699693/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 149, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 149, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 148, cos743o2c k) + cos743o2c 149 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 148) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_148
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 149 - ((654873/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_149).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_150 : ((4160569/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 150, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 150, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 149, cos743o2c k) + cos743o2c 150 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 149) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_149
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 150 - ((-57317/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_150).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_151 : ((2008073/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 151, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 151, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 150, cos743o2c k) + cos743o2c 151 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 150) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_150
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 151 - ((-72199/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_151).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_152 : ((8514711/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 152, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 152, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 151, cos743o2c k) + cos743o2c 152 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 151) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_151
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 152 - ((482469/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_152).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_153 : ((16124541/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 153, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 153, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 152, cos743o2c k) + cos743o2c 153 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 152) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_152
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 153 - ((-904781/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_153).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_154 : ((16522577/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 154, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 154, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 153, cos743o2c k) + cos743o2c 154 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 153) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_153
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 154 - ((49767/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_154).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_155 : ((673769/40000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 155, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 155, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 154, cos743o2c k) + cos743o2c 155 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 154) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_154
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 155 - ((80437/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_155).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_156 : ((7981063/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 156, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 156, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 155, cos743o2c k) + cos743o2c 156 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 155) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_155
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 156 - ((-881999/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_156).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_157 : ((8461943/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 157, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 157, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 156, cos743o2c k) + cos743o2c 157 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 156) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_156
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 157 - ((48093/50000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_157).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_158 : ((821743/50000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 158, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 158, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 157, cos743o2c k) + cos743o2c 158 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 157) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_157
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 158 - ((-244463/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_158).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_159 : ((16151811/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 159, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 159, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 158, cos743o2c k) + cos743o2c 159 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 158) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_158
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 159 - ((-282949/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_159).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_160 : ((8521301/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 160, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 160, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 159, cos743o2c k) + cos743o2c 160 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 159) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_159
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 160 - ((890891/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_160).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_161 : ((16105019/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 161, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 161, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 160, cos743o2c k) + cos743o2c 161 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 160) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_160
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 161 - ((-937483/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_161).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_162 : ((16470319/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 162, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 162, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 161, cos743o2c k) + cos743o2c 162 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 161) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_161
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 162 - ((1827/5000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_162).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_163 : ((42333/2500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 163, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 163, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 162, cos743o2c k) + cos743o2c 163 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 162) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_162
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 163 - ((462981/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_163).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_164 : ((7978603/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 164, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 164, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 163, cos743o2c k) + cos743o2c 164 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 163) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_163
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 164 - ((-487947/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_164).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_165 : ((3349023/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 165, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 165, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 164, cos743o2c k) + cos743o2c 165 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 164) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_164
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 165 - ((788009/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_165).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_166 : ((669373/40000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 166, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 166, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 165, cos743o2c k) + cos743o2c 166 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 165) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_165
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 166 - ((-1069/100000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_166).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_167 : ((3987781/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 167, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 167, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 166, cos743o2c k) + cos743o2c 167 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 166) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_166
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 167 - ((-783101/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_167).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_168 : ((3383861/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 168, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 168, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 167, cos743o2c k) + cos743o2c 168 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 167) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_167
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 168 - ((968281/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_168).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_169 : ((8273473/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 169, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 169, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 168, cos743o2c k) + cos743o2c 169 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 168) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_168
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 169 - ((-372259/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_169).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_170 : ((16008551/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 170, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 170, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 169, cos743o2c k) + cos743o2c 170 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 169) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_169
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 170 - ((-107659/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_170).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_171 : ((1062979/62500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 171, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 171, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 170, cos743o2c k) + cos743o2c 171 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 170) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_170
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 171 - ((999213/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_171).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_172 : ((16414339/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 172, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 172, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 171, cos743o2c k) + cos743o2c 172 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 171) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_171
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 172 - ((-23729/40000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_172).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_173 : ((251072/15625 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 173, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 173, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 172, cos743o2c k) + cos743o2c 173 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 172) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_172
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 173 - ((-345631/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_173).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_174 : ((17044947/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 174, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 174, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 173, cos743o2c k) + cos743o2c 174 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 173) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_173
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 174 - ((976439/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_174).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_175 : ((1021541/62500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 175, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 175, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 174, cos743o2c k) + cos743o2c 175 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 174) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_174
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 175 - ((-700191/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_175).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_176 : ((3219601/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 176, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 176, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 175, cos743o2c k) + cos743o2c 176 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 175) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_175
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 176 - ((-246551/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_176).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_177 : ((17057587/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 177, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 177, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 176, cos743o2c k) + cos743o2c 177 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 176) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_176
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 177 - ((479841/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_177).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_178 : ((1633521/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 178, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 178, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 177, cos743o2c k) + cos743o2c 178 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 177) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_177
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 178 - ((-722277/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_178).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_179 : ((16084559/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 179, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 179, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 178, cos743o2c k) + cos743o2c 179 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 178) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_178
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 179 - ((-250551/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_179).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_180 : ((3410891/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 180, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 180, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 179, cos743o2c k) + cos743o2c 180 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 179) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_179
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 180 - ((242499/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_180).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_181 : ((4096319/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 181, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 181, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 180, cos743o2c k) + cos743o2c 181 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 180) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_180
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 181 - ((-669079/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_181).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_182 : ((16031211/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 182, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 182, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 181, cos743o2c k) + cos743o2c 182 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 181) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_181
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 182 - ((-70793/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_182).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_183 : ((1064113/62500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 183, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 183, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 182, cos743o2c k) + cos743o2c 183 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 182) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_182
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 183 - ((994697/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_183).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_184 : ((1649727/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 184, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 184, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 183, cos743o2c k) + cos743o2c 184 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 183) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_183
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 184 - ((-264219/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_184).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_185 : ((15956473/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 185, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 185, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 184, cos743o2c k) + cos743o2c 185 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 184) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_184
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 185 - ((-540697/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_185).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_186 : ((677867/40000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 186, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 186, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 185, cos743o2c k) + cos743o2c 186 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 185) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_185
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 186 - ((495151/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_186).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_187 : ((16668483/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 187, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 187, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 186, cos743o2c k) + cos743o2c 187 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 186) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_186
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 187 - ((-69523/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_187).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_188 : ((15898623/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 188, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 188, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 187, cos743o2c k) + cos743o2c 188 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 187) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_187
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 188 - ((-4811/6250 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_188).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_189 : ((2098281/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 189, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 189, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 188, cos743o2c k) + cos743o2c 189 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 188) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_188
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 189 - ((35509/40000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_189).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_190 : ((8437419/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 190, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 190, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 189, cos743o2c k) + cos743o2c 190 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 189) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_189
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 190 - ((8869/100000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_190).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_191 : ((15916651/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 191, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 191, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 190, cos743o2c k) + cos743o2c 191 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 190) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_190
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 191 - ((-958087/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_191).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_192 : ((8264711/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 192, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 192, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 191, cos743o2c k) + cos743o2c 192 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 191) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_191
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 192 - ((612871/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_192).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_193 : ((1065859/62500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 193, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 193, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 192, cos743o2c k) + cos743o2c 193 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 192) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_192
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 193 - ((262211/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_193).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_194 : ((8037081/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 194, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 194, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 193, cos743o2c k) + cos743o2c 194 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 193) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_193
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 194 - ((-489741/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_194).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_195 : ((16209953/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 195, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 195, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 194, cos743o2c k) + cos743o2c 195 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 194) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_194
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 195 - ((135891/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_195).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_196 : ((8551663/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 196, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 196, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 195, cos743o2c k) + cos743o2c 196 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 195) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_195
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 196 - ((893473/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_196).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_197 : ((1639599/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 197, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 197, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 196, cos743o2c k) + cos743o2c 197 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 196) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_196
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 197 - ((-176809/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_197).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_198 : ((3187711/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 198, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 198, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 197, cos743o2c k) + cos743o2c 198 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 197) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_197
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 198 - ((-91467/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_198).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_199 : ((1057707/62500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 199, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 199, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 198, cos743o2c k) + cos743o2c 199 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 198) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_198
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 199 - ((984857/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_199).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_200 : ((16806381/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 200, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 200, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 199, cos743o2c k) + cos743o2c 200 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 199) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_199
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 200 - ((-116831/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_200).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_201 : ((15884907/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 201, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 201, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 200, cos743o2c k) + cos743o2c 201 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 200) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_200
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 201 - ((-460687/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_201).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_202 : ((257928/15625 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 202, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 202, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 201, cos743o2c k) + cos743o2c 202 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 201) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_201
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 202 - ((124517/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_202).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_203 : ((17100447/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 203, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 203, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 202, cos743o2c k) + cos743o2c 203 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 202) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_202
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 203 - ((118631/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_203).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_204 : ((16171763/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 204, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 204, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 203, cos743o2c k) + cos743o2c 204 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 203) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_203
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 204 - ((-116073/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_204).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_205 : ((2004711/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 205, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 205, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 204, cos743o2c k) + cos743o2c 205 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 204) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_204
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 205 - ((-5359/40000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_205).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_206 : ((17032327/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 206, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 206, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 205, cos743o2c k) + cos743o2c 206 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 205) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_205
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 206 - ((994739/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_206).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_207 : ((8353691/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 207, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 207, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 206, cos743o2c k) + cos743o2c 207 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 206) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_206
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 207 - ((-64969/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_207).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_208 : ((7927489/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 208, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 208, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 207, cos743o2c k) + cos743o2c 208 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 207) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_207
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 208 - ((-53269/62500 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_208).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_209 : ((16544823/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 209, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 209, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 208, cos743o2c k) + cos743o2c 209 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 208) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_208
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 209 - ((137989/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_209).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_210 : ((8557523/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 210, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 210, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 209, cos743o2c k) + cos743o2c 210 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 209) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_209
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 210 - ((570323/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_210).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_211 : ((4049741/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 211, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 211, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 210, cos743o2c k) + cos743o2c 211 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 210) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_210
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 211 - ((-457991/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_211).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_212 : ((7986829/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 212, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 212, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 211, cos743o2c k) + cos743o2c 212 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 211) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_211
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 212 - ((-112603/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_212).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_213 : ((16972323/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 213, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 213, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 212, cos743o2c k) + cos743o2c 213 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 212) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_212
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 213 - ((199753/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_213).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_214 : ((1053309/62500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 214, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 214, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 213, cos743o2c k) + cos743o2c 214 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 213) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_213
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 214 - ((-119279/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_214).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_215 : ((7945991/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 215, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 215, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 214, cos743o2c k) + cos743o2c 215 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 214) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_214
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 215 - ((-480431/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_215).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_216 : ((3262443/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 216, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 216, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 215, cos743o2c k) + cos743o2c 216 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 215) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_215
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 216 - ((420333/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_216).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_217 : ((17149159/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 217, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 217, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 216, cos743o2c k) + cos743o2c 217 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 216) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_216
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 217 - ((209261/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_217).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_218 : ((8246273/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 218, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 218, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 217, cos743o2c k) + cos743o2c 218 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 217) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_217
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 218 - ((-656513/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_218).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_219 : ((1582919/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 219, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 219, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 218, cos743o2c k) + cos743o2c 219 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 218) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_218
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 219 - ((-82907/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_219).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_220 : ((16652457/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 220, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 220, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 219, cos743o2c k) + cos743o2c 220 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 219) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_219
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 220 - ((823367/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_220).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_221 : ((3424499/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 221, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 221, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 220, cos743o2c k) + cos743o2c 221 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 220) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_220
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 221 - ((235069/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_221).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_222 : ((8097437/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 222, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 222, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 221, cos743o2c k) + cos743o2c 222 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 221) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_221
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 222 - ((-927521/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_222).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_223 : ((15914387/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 223, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 223, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 222, cos743o2c k) + cos743o2c 223 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 222) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_222
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 223 - ((-280387/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_223).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_224 : ((211197/12500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 224, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 224, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 223, cos743o2c k) + cos743o2c 224 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 223) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_223
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 224 - ((981473/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_224).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_225 : ((17004223/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 225, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 225, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 224, cos743o2c k) + cos743o2c 225 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 224) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_224
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 225 - ((108563/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_225).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_226 : ((16004639/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 226, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 226, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 225, cos743o2c k) + cos743o2c 226 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 225) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_225
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 226 - ((-249871/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_226).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_227 : ((16041787/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 227, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 227, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 226, cos743o2c k) + cos743o2c 227 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 226) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_226
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 227 - ((582/15625 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_227).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_228 : ((4259187/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 228, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 228, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 227, cos743o2c k) + cos743o2c 228 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 227) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_227
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 228 - ((995061/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_228).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_229 : ((42207/2500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 229, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 229, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 228, cos743o2c k) + cos743o2c 229 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 228) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_228
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 229 - ((-19231/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_229).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_230 : ((7951557/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 230, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 230, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 229, cos743o2c k) + cos743o2c 230 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 229) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_229
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 230 - ((-489793/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_230).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_231 : ((8071971/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 231, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 231, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 230, cos743o2c k) + cos743o2c 231 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 230) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_230
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 231 - ((7529/31250 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_231).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_232 : ((4276413/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 232, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 232, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 231, cos743o2c k) + cos743o2c 232 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 231) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_231
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 232 - ((96181/100000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_232).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_233 : ((16805909/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 233, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 233, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 232, cos743o2c k) + cos743o2c 233 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 232) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_232
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 233 - ((-299643/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_233).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_234 : ((15858013/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 234, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 234, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 233, cos743o2c k) + cos743o2c 234 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 233) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_233
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 234 - ((-236949/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_234).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_235 : ((16189489/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 235, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 235, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 234, cos743o2c k) + cos743o2c 235 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 234) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_234
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 235 - ((41447/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_235).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_236 : ((17130573/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 236, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 236, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 235, cos743o2c k) + cos743o2c 236 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 235) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_235
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 236 - ((14706/15625 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_236).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_237 : ((16792563/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 237, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 237, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 236, cos743o2c k) + cos743o2c 237 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 236) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_236
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 237 - ((-33791/100000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_237).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_238 : ((3962269/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 238, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 238, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 237, cos743o2c k) + cos743o2c 238 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 237) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_237
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 238 - ((-943387/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_238).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_239 : ((4042063/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 239, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 239, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 238, cos743o2c k) + cos743o2c 239 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 238) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_238
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 239 - ((79819/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_239).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_240 : ((171219/10000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 240, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 240, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 239, cos743o2c k) + cos743o2c 240 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 239) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_239
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 240 - ((238437/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_240).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_241 : ((2105773/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 241, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 241, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 240, cos743o2c k) + cos743o2c 241 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 240) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_240
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 241 - ((-8613/31250 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_241).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_242 : ((15876371/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 242, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 242, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 241, cos743o2c k) + cos743o2c 242 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 241) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_241
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 242 - ((-969713/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_242).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_243 : ((16082677/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 243, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 243, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 242, cos743o2c k) + cos743o2c 243 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 242) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_242
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 243 - ((103203/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_243).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_244 : ((8534679/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 244, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 244, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 243, cos743o2c k) + cos743o2c 244 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 243) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_243
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 244 - ((986781/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_244).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_245 : ((2119761/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 245, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 245, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 244, cos743o2c k) + cos743o2c 245 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 244) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_244
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 245 - ((-11117/100000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_245).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_246 : ((7979719/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 246, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 246, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 245, cos743o2c k) + cos743o2c 246 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 245) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_245
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 246 - ((-19971/20000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_246).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_247 : ((1993687/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 247, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 247, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 246, cos743o2c k) + cos743o2c 247 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 246) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_246
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 247 - ((-4921/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_247).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_248 : ((16946227/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 248, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 248, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 247, cos743o2c k) + cos743o2c 248 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 247) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_247
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 248 - ((996831/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_248).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_249 : ((8550487/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 249, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 249, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 248, cos743o2c k) + cos743o2c 249 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 248) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_248
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 249 - ((154847/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_249).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_250 : ((2016111/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 250, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 250, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 249, cos743o2c k) + cos743o2c 250 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 249) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_249
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 250 - ((-485993/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_250).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_251 : ((15809453/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 251, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 251, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 250, cos743o2c k) + cos743o2c 251 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 250) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_250
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 251 - ((-63867/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_251).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_252 : ((1672297/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 252, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 252, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 251, cos743o2c k) + cos743o2c 252 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 251) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_251
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 252 - ((913617/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_252).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_253 : ((17218197/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 253, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 253, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 252, cos743o2c k) + cos743o2c 253 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 252) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_252
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 253 - ((495327/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_253).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_254 : ((3281253/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 254, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 254, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 253, cos743o2c k) + cos743o2c 254 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 253) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_253
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 254 - ((-101479/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_254).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_255 : ((15735893/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 255, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 255, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 254, cos743o2c k) + cos743o2c 255 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 254) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_254
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 255 - ((-10473/15625 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_255).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_256 : ((3278951/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 256, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 256, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 255, cos743o2c k) + cos743o2c 256 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 255) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_255
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 256 - ((329481/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_256).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_257 : ((17221697/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 257, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 257, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 256, cos743o2c k) + cos743o2c 257 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 256) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_256
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 257 - ((413521/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_257).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_258 : ((524053/31250 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 258, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 258, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 257, cos743o2c k) + cos743o2c 258 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 257) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_257
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 258 - ((-451901/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_258).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_259 : ((15825267/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 259, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 259, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 258, cos743o2c k) + cos743o2c 259 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 258) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_258
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 259 - ((-944329/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_259).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_260 : ((2002497/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 260, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 260, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 259, cos743o2c k) + cos743o2c 260 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 259) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_259
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 260 - ((194809/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_260).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_261 : ((4254639/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 261, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 261, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 260, cos743o2c k) + cos743o2c 261 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 260) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_260
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 261 - ((24967/25000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_261).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_262 : ((17117057/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 262, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 262, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 261, cos743o2c k) + cos743o2c 262 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 261) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_261
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 262 - ((98601/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_262).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_263 : ((129193/8000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 263, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 263, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 262, cos743o2c k) + cos743o2c 263 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 262) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_262
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 263 - ((-120979/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_263).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_264 : ((1574561/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 264, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 264, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 263, cos743o2c k) + cos743o2c 264 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 263) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_263
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 264 - ((-80683/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_264).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_265 : ((16581143/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 265, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 265, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 264, cos743o2c k) + cos743o2c 265 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 264) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_264
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 265 - ((835633/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_265).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_266 : ((17264913/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 266, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 266, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 265, cos743o2c k) + cos743o2c 266 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 265) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_265
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 266 - ((68387/100000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_266).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_267 : ((26667/1600 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 267, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 267, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 266, cos743o2c k) + cos743o2c 267 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 266) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_266
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 267 - ((-298969/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_267).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_268 : ((7885119/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 268, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 268, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 267, cos743o2c k) + cos743o2c 268 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 267) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_267
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 268 - ((-896537/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_268).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_269 : ((16038533/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 269, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 269, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 268, cos743o2c k) + cos743o2c 269 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 268) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_268
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 269 - ((53679/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_269).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_270 : ((17035281/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 270, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 270, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 269, cos743o2c k) + cos743o2c 270 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 269) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_269
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 270 - ((62303/62500 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_270).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_271 : ((2144111/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 271, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 271, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 270, cos743o2c k) + cos743o2c 271 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 270) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_270
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 271 - ((117707/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_271).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_272 : ((162037/10000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 272, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 272, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 271, cos743o2c k) + cos743o2c 272 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 271) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_271
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 272 - ((-29659/31250 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_272).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_273 : ((15699819/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 273, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 273, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 272, cos743o2c k) + cos743o2c 273 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 272) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_272
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 273 - ((-503781/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_273).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_274 : ((4109477/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 274, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 274, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 273, cos743o2c k) + cos743o2c 274 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 273) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_273
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 274 - ((738189/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_274).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_275 : ((8627889/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 275, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 275, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 274, cos743o2c k) + cos743o2c 275 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 274) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_274
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 275 - ((81797/100000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_275).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_276 : ((16874937/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 276, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 276, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 275, cos743o2c k) + cos743o2c 276 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 275) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_275
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 276 - ((-380741/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_276).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_277 : ((7944079/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 277, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 277, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 276, cos743o2c k) + cos743o2c 277 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 276) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_276
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 277 - ((-986679/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_277).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_278 : ((7909729/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 278, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 278, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 277, cos743o2c k) + cos743o2c 278 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 277) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_277
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 278 - ((-343/5000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_278).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_279 : ((8386521/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 279, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 279, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 278, cos743o2c k) + cos743o2c 279 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 278) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_278
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 279 - ((238421/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_279).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_280 : ((4323299/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 280, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 280, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 279, cos743o2c k) + cos743o2c 280 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 279) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_279
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 280 - ((260127/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_280).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_281 : ((663671/40000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 281, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 281, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 280, cos743o2c k) + cos743o2c 281 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 280) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_280
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 281 - ((-701321/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_281).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_282 : ((7863469/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 282, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 282, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 281, cos743o2c k) + cos743o2c 282 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 281) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_281
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 282 - ((-864737/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_282).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_283 : ((15993963/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 283, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 283, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 282, cos743o2c k) + cos743o2c 283 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 282) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_282
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 283 - ((2137/8000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_283).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_284 : ((16993813/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 284, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 284, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 283, cos743o2c k) + cos743o2c 284 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 283) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_283
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 284 - ((19999/20000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_284).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_285 : ((17245929/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 285, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 285, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 284, cos743o2c k) + cos743o2c 285 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 284) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_284
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 285 - ((31527/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_285).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_286 : ((16380261/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 286, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 286, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 285, cos743o2c k) + cos743o2c 286 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 285) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_285
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 286 - ((-27049/31250 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_286).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_287 : ((15663763/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 287, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 287, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 286, cos743o2c k) + cos743o2c 287 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 286) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_286
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 287 - ((-358199/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_287).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_288 : ((16137397/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 288, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 288, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 287, cos743o2c k) + cos743o2c 288 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 287) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_287
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 288 - ((236867/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_288).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_289 : ((427881/25000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 289, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 289, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 288, cos743o2c k) + cos743o2c 289 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 288) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_288
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 289 - ((977943/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_289).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_290 : ((3438433/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 290, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 290, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 289, cos743o2c k) + cos743o2c 290 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 289) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_289
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 290 - ((3081/40000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_290).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_291 : ((8129703/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 291, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 291, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 290, cos743o2c k) + cos743o2c 291 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 290) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_290
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 291 - ((-932659/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_291).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_292 : ((15641923/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 292, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 292, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 291, cos743o2c k) + cos743o2c 292 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 291) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_291
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 292 - ((-617383/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_292).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_293 : ((4052579/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 293, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 293, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 292, cos743o2c k) + cos743o2c 293 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 292) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_292
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 293 - ((568493/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_293).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_294 : ((8582833/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 294, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 294, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 293, cos743o2c k) + cos743o2c 294 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 293) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_293
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 294 - ((19109/20000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_294).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_295 : ((17175283/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 295, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 295, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 294, cos743o2c k) + cos743o2c 295 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 294) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_294
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 295 - ((9717/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_295).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_296 : ((16226997/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 296, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 296, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 295, cos743o2c k) + cos743o2c 296 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 295) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_295
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 296 - ((-474093/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_296).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_297 : ((15628773/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 297, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 297, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 296, cos743o2c k) + cos743o2c 297 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 296) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_296
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 297 - ((-149531/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_297).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_298 : ((8099771/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 298, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 298, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 297, cos743o2c k) + cos743o2c 298 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 297) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_297
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 298 - ((570869/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_298).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_299 : ((17160129/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 299, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 299, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 298, cos743o2c k) + cos743o2c 299 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 298) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_298
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 299 - ((960687/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_299).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_300 : ((8604537/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 300, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 300, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 299, cos743o2c k) + cos743o2c 300 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 299) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_299
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 300 - ((9809/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_300).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_301 : ((4070411/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 301, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 301, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 300, cos743o2c k) + cos743o2c 301 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 300) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_300
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 301 - ((-92733/100000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_301).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_302 : ((3905129/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 302, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 302, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 301, cos743o2c k) + cos743o2c 302 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 301) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_301
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 302 - ((-165257/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_302).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_303 : ((644201/40000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 303, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 303, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 302, cos743o2c k) + cos743o2c 303 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 302) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_302
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 303 - ((484609/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_303).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_304 : ((17092283/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 304, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 304, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 303, cos743o2c k) + cos743o2c 304 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 303) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_303
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 304 - ((493679/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_304).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_305 : ((4320657/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 305, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 305, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 304, cos743o2c k) + cos743o2c 305 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 304) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_304
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 305 - ((38089/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_305).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_306 : ((8214049/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 306, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 306, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 305, cos743o2c k) + cos743o2c 306 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 305) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_305
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 306 - ((-85443/100000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_306).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_307 : ((15641521/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 307, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 307, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 306, cos743o2c k) + cos743o2c 307 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 306) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_306
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 307 - ((-786477/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_307).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_308 : ((15939839/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 308, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 308, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 307, cos743o2c k) + cos743o2c 308 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 307) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_307
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 308 - ((149209/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_308).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_309 : ((16937721/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 309, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 309, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 308, cos743o2c k) + cos743o2c 309 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 308) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_308
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 309 - ((498991/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_309).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_310 : ((17358147/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 310, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 310, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 309, cos743o2c k) + cos743o2c 310 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 309) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_309
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 310 - ((210263/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_310).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_311 : ((16667341/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 311, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 311, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 310, cos743o2c k) + cos743o2c 311 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 310) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_310
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 311 - ((-345353/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_311).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_312 : ((3935041/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 312, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 312, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 311, cos743o2c k) + cos743o2c 312 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 311) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_311
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 312 - ((-927077/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_312).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_313 : ((7871163/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 313, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 313, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 312, cos743o2c k) + cos743o2c 313 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 312) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_312
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 313 - ((1131/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_313).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_314 : ((8334789/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 314, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 314, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 313, cos743o2c k) + cos743o2c 314 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 313) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_313
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 314 - ((115919/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_314).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_315 : ((271372/15625 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 315, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 315, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 314, cos743o2c k) + cos743o2c 315 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 314) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_314
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 315 - ((69833/100000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_315).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_316 : ((16974199/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 316, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 316, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 315, cos743o2c k) + cos743o2c 316 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 315) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_315
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 316 - ((-393509/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_316).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_317 : ((7987063/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 317, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 317, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 316, cos743o2c k) + cos743o2c 317 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 316) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_316
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 317 - ((-999973/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_317).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_318 : ((3897693/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 318, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 318, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 317, cos743o2c k) + cos743o2c 318 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 317) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_317
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 318 - ((-191627/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_318).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_319 : ((16289043/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 319, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 319, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 318, cos743o2c k) + cos743o2c 319 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 318) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_318
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 319 - ((698371/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_319).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_320 : ((17223051/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 320, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 320, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 319, cos743o2c k) + cos743o2c 320 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 319) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_319
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 320 - ((233527/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_320).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_321 : ((17269533/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 321, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 321, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 320, cos743o2c k) + cos743o2c 321 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 320) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_320
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 321 - ((23291/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_321).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_322 : ((16374217/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 322, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 322, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 321, cos743o2c k) + cos743o2c 322 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 321) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_321
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 322 - ((-55951/62500 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_322).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_323 : ((15602913/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 323, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 323, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 322, cos743o2c k) + cos743o2c 323 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 322) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_322
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 323 - ((-192801/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_323).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_324 : ((15867279/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 324, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 324, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 323, cos743o2c k) + cos743o2c 324 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 323) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_323
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 324 - ((132233/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_324).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_325 : ((16854671/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 325, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 325, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 324, cos743o2c k) + cos743o2c 325 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 324) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_324
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 325 - ((246873/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_325).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_326 : ((4352277/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 326, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 326, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 325, cos743o2c k) + cos743o2c 326 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 325) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_325
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 326 - ((554537/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_326).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_327 : ((168863/10000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 327, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 327, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 326, cos743o2c k) + cos743o2c 327 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 326) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_326
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 327 - ((-130677/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_327).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_328 : ((7946323/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 328, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 328, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 327, cos743o2c k) + cos743o2c 328 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 327) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_327
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 328 - ((-496777/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_328).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_329 : ((3892999/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 329, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 329, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 328, cos743o2c k) + cos743o2c 329 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 328) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_328
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 329 - ((-6411/20000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_329).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_330 : ((16290057/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 330, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 330, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 329, cos743o2c k) + cos743o2c 330 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 329) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_329
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 330 - ((718161/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_330).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_331 : ((1722781/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 331, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 331, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 330, cos743o2c k) + cos743o2c 331 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 330) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_330
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 331 - ((937853/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_331).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_332 : ((17323287/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 332, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 332, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 331, cos743o2c k) + cos743o2c 332 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 331) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_331
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 332 - ((95577/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_332).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_333 : ((8235131/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 333, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 333, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 332, cos743o2c k) + cos743o2c 333 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 332) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_332
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 333 - ((-34117/40000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_333).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_334 : ((7812709/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 334, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 334, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 333, cos743o2c k) + cos743o2c 334 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 333) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_333
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 334 - ((-105593/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_334).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_335 : ((7864839/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 335, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 335, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 334, cos743o2c k) + cos743o2c 335 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 334) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_334
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 335 - ((2609/25000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_335).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_336 : ((16665843/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 336, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 336, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 335, cos743o2c k) + cos743o2c 336 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 335) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_335
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 336 - ((187253/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_336).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_337 : ((17400783/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 337, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 337, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 336, cos743o2c k) + cos743o2c 337 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 336) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_336
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 337 - ((2297/3125 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_337).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_338 : ((2141143/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 338, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 338, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 337, cos743o2c k) + cos743o2c 338 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 337) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_337
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 338 - ((-271539/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_338).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_339 : ((8074319/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 339, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 339, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 338, cos743o2c k) + cos743o2c 339 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 338) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_338
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 339 - ((-490203/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_339).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_340 : ((15523777/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 340, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 340, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 339, cos743o2c k) + cos743o2c 340 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 339) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_339
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 340 - ((-624761/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_340).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_341 : ((15927961/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 341, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 341, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 340, cos743o2c k) + cos743o2c 341 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 340) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_340
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 341 - ((101071/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_341).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_342 : ((3385127/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 342, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 342, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 341, cos743o2c k) + cos743o2c 342 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 341) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_341
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 342 - ((498887/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_342).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_343 : ((17450663/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 343, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 343, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 342, cos743o2c k) + cos743o2c 343 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 342) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_342
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 343 - ((65641/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_343).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_344 : ((16946199/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 344, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 344, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 343, cos743o2c k) + cos743o2c 344 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 343) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_343
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 344 - ((-126091/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_344).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_345 : ((3986689/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 345, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 345, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 344, cos743o2c k) + cos743o2c 345 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 344) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_344
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 345 - ((-999343/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_345).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_346 : ((15503313/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 346, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 346, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 345, cos743o2c k) + cos743o2c 346 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 345) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_345
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 346 - ((-443343/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_346).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_347 : ((16078393/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 347, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 347, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 346, cos743o2c k) + cos743o2c 347 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 346) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_346
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 347 - ((28759/50000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_347).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_348 : ((266752/15625 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 348, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 348, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 347, cos743o2c k) + cos743o2c 348 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 347) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_347
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 348 - ((198767/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_348).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_349 : ((872781/50000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 349, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 349, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 348, cos743o2c k) + cos743o2c 349 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 348) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_348
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 349 - ((47949/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_349).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_350 : ((210439/12500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 350, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 350, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 349, cos743o2c k) + cos743o2c 350 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 349) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_349
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 350 - ((-1551/2500 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_350).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_351 : ((990471/62500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 351, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 351, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 350, cos743o2c k) + cos743o2c 351 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 350) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_350
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 351 - ((-246871/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_351).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_352 : ((7749673/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 352, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 352, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 351, cos743o2c k) + cos743o2c 352 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 351) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_351
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 352 - ((-34809/100000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_352).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_353 : ((807111/50000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 353, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 353, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 352, cos743o2c k) + cos743o2c 353 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 352) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_352
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 353 - ((321487/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_353).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_354 : ((4281557/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 354, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 354, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 353, cos743o2c k) + cos743o2c 354 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 353) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_353
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 354 - ((246027/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_354).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_355 : ((17463717/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 355, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 355, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 354, cos743o2c k) + cos743o2c 355 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 354) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_354
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 355 - ((337589/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_355).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_356 : ((16818883/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 356, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 356, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 355, cos743o2c k) + cos743o2c 356 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 355) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_355
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 356 - ((-322367/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_356).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_357 : ((1979191/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 357, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 357, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 356, cos743o2c k) + cos743o2c 357 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 356) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_356
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 357 - ((-197051/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_357).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_358 : ((3096287/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 358, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 358, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 357, cos743o2c k) + cos743o2c 358 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 357) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_357
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 358 - ((-351993/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_358).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_359 : ((16107451/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 359, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 359, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 358, cos743o2c k) + cos743o2c 359 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 358) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_358
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 359 - ((156529/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_359).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_360 : ((17097683/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 360, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 360, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 359, cos743o2c k) + cos743o2c 360 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 359) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_359
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 360 - ((247583/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_360).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_361 : ((17488037/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 361, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 361, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 360, cos743o2c k) + cos743o2c 361 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 360) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_360
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 361 - ((195227/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_361).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_362 : ((16901579/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 362, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 362, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 361, cos743o2c k) + cos743o2c 362 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 361) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_361
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 362 - ((-293179/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_362).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_363 : ((3976181/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 363, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 363, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 362, cos743o2c k) + cos743o2c 363 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 362) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_362
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 363 - ((-199351/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_363).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_364 : ((618133/40000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 364, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 364, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 363, cos743o2c k) + cos743o2c 364 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 363) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_363
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 364 - ((-451299/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_364).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_365 : ((3994189/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 365, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 365, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 364, cos743o2c k) + cos743o2c 365 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 364) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_364
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 365 - ((523531/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_365).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_366 : ((339533/20000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 366, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 366, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 365, cos743o2c k) + cos743o2c 366 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 365) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_365
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 366 - ((499997/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_366).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_367 : ((3501639/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 367, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 367, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 366, cos743o2c k) + cos743o2c 367 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 366) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_366
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 367 - ((106329/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_367).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_368 : ((17072817/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 368, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 368, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 367, cos743o2c k) + cos743o2c 368 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 367) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_367
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 368 - ((-217639/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_368).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_369 : ((16079017/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 369, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 369, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 368, cos743o2c k) + cos743o2c 369 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 368) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_368
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 369 - ((-9937/10000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_369).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_370 : ((15451931/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 370, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 370, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 369, cos743o2c k) + cos743o2c 370 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 369) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_369
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 370 - ((-313493/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_370).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_371 : ((788557/50000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 371, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 371, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 370, cos743o2c k) + cos743o2c 371 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 370) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_370
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 371 - ((319309/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_371).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_372 : ((3348197/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 372, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 372, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 371, cos743o2c k) + cos743o2c 372 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 371) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_371
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 372 - ((193989/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_372).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_373 : ((698861/40000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 373, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 373, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 372, cos743o2c k) + cos743o2c 373 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 372) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_372
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 373 - ((9133/12500 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_373).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_374 : ((3459393/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 374, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 374, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 373, cos743o2c k) + cos743o2c 374 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 373) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_373
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 374 - ((-8723/50000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_374).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_375 : ((8188571/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 375, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 375, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 374, cos743o2c k) + cos743o2c 375 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 374) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_374
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 375 - ((-919723/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_375).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_376 : ((7771919/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 376, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 376, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 375, cos743o2c k) + cos743o2c 376 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 375) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_375
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 376 - ((-208301/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_376).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_377 : ((3109113/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 377, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 377, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 376, cos743o2c k) + cos743o2c 377 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 376) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_376
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 377 - ((1827/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_377).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_378 : ((16379251/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 378, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 378, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 377, cos743o2c k) + cos743o2c 378 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 377) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_377
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 378 - ((416893/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_378).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_379 : ((8650751/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 379, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 379, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 378, cos743o2c k) + cos743o2c 379 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 378) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_378
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 379 - ((922351/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_379).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_380 : ((2186923/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 380, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 380, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 379, cos743o2c k) + cos743o2c 380 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 379) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_379
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 380 - ((96991/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_380).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_381 : ((16791209/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 381, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 381, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 380, cos743o2c k) + cos743o2c 381 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 380) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_380
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 381 - ((-28163/40000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_381).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_382 : ((7904007/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 382, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 382, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 381, cos743o2c k) + cos743o2c 382 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 381) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_381
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 382 - ((-196619/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_382).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_383 : ((7702157/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 383, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 383, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 382, cos743o2c k) + cos743o2c 383 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 382) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_382
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 383 - ((-1009/2500 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_383).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_384 : ((15929691/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 384, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 384, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 383, cos743o2c k) + cos743o2c 384 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 383) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_383
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 384 - ((525477/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_384).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_385 : ((8464137/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 385, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 385, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 384, cos743o2c k) + cos743o2c 385 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 384) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_384
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 385 - ((998683/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_385).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_386 : ((3508013/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 386, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 386, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 385, cos743o2c k) + cos743o2c 386 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 385) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_385
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 386 - ((611891/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_386).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_387 : ((3448367/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 387, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 387, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 386, cos743o2c k) + cos743o2c 387 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 386) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_386
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 387 - ((-29813/100000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_387).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_388 : ((8144599/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 388, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 388, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 387, cos743o2c k) + cos743o2c 388 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 387) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_387
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 388 - ((-952537/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_388).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_389 : ((15491147/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 389, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 389, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 388, cos743o2c k) + cos743o2c 389 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 388) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_388
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 389 - ((-797951/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_389).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_390 : ((15520943/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 390, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 390, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 389, cos743o2c k) + cos743o2c 390 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 389) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_389
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 390 - ((3737/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_390).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_391 : ((16352029/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 391, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 391, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 390, cos743o2c k) + cos743o2c 391 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 390) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_390
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 391 - ((415593/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_391).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_392 : ((345761/20000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 392, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 392, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 391, cos743o2c k) + cos743o2c 392 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 391) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_391
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 392 - ((936121/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_392).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_393 : ((17549787/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 393, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 393, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 392, cos743o2c k) + cos743o2c 393 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 392) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_392
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 393 - ((261837/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_393).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_394 : ((16921541/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 394, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 394, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 393, cos743o2c k) + cos743o2c 394 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 393) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_393
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 394 - ((-314073/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_394).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_395 : ((15922693/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 395, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 395, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 394, cos743o2c k) + cos743o2c 395 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 394) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_394
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 395 - ((-249687/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_395).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_396 : ((15373391/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 396, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 396, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 395, cos743o2c k) + cos743o2c 396 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 395) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_395
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 396 - ((-274601/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_396).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_397 : ((3930341/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 397, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 397, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 396, cos743o2c k) + cos743o2c 397 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 396) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_396
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 397 - ((348073/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_397).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_398 : ((2085267/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 398, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 398, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 397, cos743o2c k) + cos743o2c 398 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 397) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_397
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 398 - ((120109/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_398).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_399 : ((17477163/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 399, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 399, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 398, cos743o2c k) + cos743o2c 399 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 398) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_398
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 399 - ((795127/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_399).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_400 : ((8733189/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 400, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 400, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 399, cos743o2c k) + cos743o2c 400 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 399) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_399
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 400 - ((-2137/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_400).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_401 : ((16659733/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 401, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 401, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 400, cos743o2c k) + cos743o2c 401 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 400) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_400
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 401 - ((-161309/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_401).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_402 : ((7851089/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 402, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 402, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 401, cos743o2c k) + cos743o2c 402 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 401) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_401
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 402 - ((-191491/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_402).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_403 : ((239913/15625 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 403, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 403, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 402, cos743o2c k) + cos743o2c 403 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 402) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_402
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 403 - ((-173823/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_403).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_404 : ((15890279/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 404, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 404, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 403, cos743o2c k) + cos743o2c 404 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 403) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_403
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 404 - ((535947/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_404).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_405 : ((16886419/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 405, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 405, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 404, cos743o2c k) + cos743o2c 405 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 404) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_404
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 405 - ((12453/12500 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_405).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_406 : ((17561629/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 406, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 406, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 405, cos743o2c k) + cos743o2c 406 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 405) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_405
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 406 - ((67531/100000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_406).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_407 : ((8694939/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 407, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 407, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 406, cos743o2c k) + cos743o2c 407 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 406) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_406
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 407 - ((-171651/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_407).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_408 : ((2063233/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 408, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 408, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 407, cos743o2c k) + cos743o2c 408 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 407) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_407
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 408 - ((-441957/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_408).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_409 : ((15593821/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 409, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 409, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 408, cos743o2c k) + cos743o2c 409 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 408) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_408
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 409 - ((-911943/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_409).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_410 : ((15355249/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 410, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 410, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 409, cos743o2c k) + cos743o2c 410 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 409) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_409
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 410 - ((-29809/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_410).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_411 : ((7985797/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 411, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 411, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 410, cos743o2c k) + cos743o2c 411 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 410) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_410
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 411 - ((123289/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_411).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_412 : ((16971487/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 412, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 412, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 411, cos743o2c k) + cos743o2c 412 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 411) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_411
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 412 - ((999993/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_412).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_413 : ((1099719/62500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 413, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 413, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 412, cos743o2c k) + cos743o2c 413 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 412) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_412
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 413 - ((624117/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_413).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_414 : ((17372849/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 414, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 414, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 413, cos743o2c k) + cos743o2c 414 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 413) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_413
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 414 - ((-44511/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_414).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_415 : ((16472337/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 415, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 415, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 414, cos743o2c k) + cos743o2c 415 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 414) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_414
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 415 - ((-225103/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_415).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_416 : ((38923/2500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 416, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 416, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 415, cos743o2c k) + cos743o2c 416 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 415) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_415
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 416 - ((-903037/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_416).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_417 : ((3834109/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 417, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 417, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 416, cos743o2c k) + cos743o2c 417 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 416) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_416
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 417 - ((-29083/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_417).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_418 : ((1993187/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 418, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 418, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 417, cos743o2c k) + cos743o2c 418 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 417) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_417
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 418 - ((15229/25000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_418).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_419 : ((16945001/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 419, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 419, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 418, cos743o2c k) + cos743o2c 419 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 418) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_418
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 419 - ((199921/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_419).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_420 : ((17599243/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 420, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 420, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 419, cos743o2c k) + cos743o2c 420 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 419) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_419
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 420 - ((327171/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_420).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_421 : ((1742981/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 421, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 421, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 420, cos743o2c k) + cos743o2c 421 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 420) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_420
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 421 - ((-169333/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_421).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_422 : ((16561523/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 422, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 422, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 421, cos743o2c k) + cos743o2c 422 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 421) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_421
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 422 - ((-868187/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_422).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_423 : ((1953191/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 423, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 423, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 422, cos743o2c k) + cos743o2c 423 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 422) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_422
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 423 - ((-187179/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_423).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_424 : ((15298013/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 424, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 424, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 423, cos743o2c k) + cos743o2c 424 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 423) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_423
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 424 - ((-65483/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_424).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_425 : ((79067/5000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 425, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 425, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 424, cos743o2c k) + cos743o2c 425 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 424) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_424
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 425 - ((515487/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_425).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_426 : ((8400569/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 426, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 426, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 425, cos743o2c k) + cos743o2c 426 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 425) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_425
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 426 - ((493919/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_426).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_427 : ((8778087/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 427, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 427, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 426, cos743o2c k) + cos743o2c 427 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 426) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_426
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 427 - ((11799/15625 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_427).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_428 : ((219287/12500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 428, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 428, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 427, cos743o2c k) + cos743o2c 428 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 427) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_427
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 428 - ((-6557/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_428).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_429 : ((4193011/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 429, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 429, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 428, cos743o2c k) + cos743o2c 429 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 428) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_428
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 429 - ((-12044/15625 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_429).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_430 : ((7893547/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 430, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 430, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 429, cos743o2c k) + cos743o2c 430 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 429) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_429
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 430 - ((-19697/20000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_430).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_431 : ((477449/31250 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 431, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 431, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 430, cos743o2c k) + cos743o2c 431 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 430) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_430
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 431 - ((-254313/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_431).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_432 : ((3119963/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 432, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 432, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 431, cos743o2c k) + cos743o2c 432 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 431) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_431
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 432 - ((321547/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_432).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_433 : ((16526719/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 433, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 433, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 432, cos743o2c k) + cos743o2c 433 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 432) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_432
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 433 - ((231751/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_433).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_434 : ((17417041/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 434, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 434, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 433, cos743o2c k) + cos743o2c 434 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 433) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_433
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 434 - ((445211/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_434).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_435 : ((17657813/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 435, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 435, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 434, cos743o2c k) + cos743o2c 435 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 434) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_434
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 435 - ((30109/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_435).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_436 : ((17085031/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 436, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 436, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 435, cos743o2c k) + cos743o2c 436 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 435) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_435
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 436 - ((-286341/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_436).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_437 : ((1609097/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 437, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 437, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 436, cos743o2c k) + cos743o2c 437 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 436) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_436
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 437 - ((-993961/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_437).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_438 : ((15351877/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 438, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 438, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 437, cos743o2c k) + cos743o2c 438 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 437) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_437
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 438 - ((-738993/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_438).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_439 : ((960463/62500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 439, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 439, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 438, cos743o2c k) + cos743o2c 439 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 438) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_438
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 439 - ((15631/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_439).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_440 : ((16125741/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 440, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 440, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 439, cos743o2c k) + cos743o2c 440 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 439) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_439
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 440 - ((758433/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_440).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_441 : ((68467/4000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 441, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 441, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 440, cos743o2c k) + cos743o2c 441 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 440) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_440
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 441 - ((991109/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_441).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_442 : ((8838951/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 442, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 442, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 441, cos743o2c k) + cos743o2c 442 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 441) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_441
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 442 - ((140313/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_442).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_443 : ((348731/20000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 443, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 443, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 442, cos743o2c k) + cos743o2c 443 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 442) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_442
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 443 - ((-60313/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_443).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_444 : ((8276937/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 444, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 444, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 443, cos743o2c k) + cos743o2c 444 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 443) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_443
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 444 - ((-55161/62500 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_444).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_445 : ((3903283/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 445, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 445, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 444, cos743o2c k) + cos743o2c 445 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 444) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_444
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 445 - ((-470321/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_445).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_446 : ((380807/25000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 446, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 446, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 445, cos743o2c k) + cos743o2c 446 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 445) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_445
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 446 - ((-23797/62500 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_446).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_447 : ((15659387/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 447, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 447, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 446, cos743o2c k) + cos743o2c 447 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 446) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_446
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 447 - ((427207/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_447).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_448 : ((16614859/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 448, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 448, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 447, cos743o2c k) + cos743o2c 448 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 447) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_447
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 448 - ((238893/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_448).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_449 : ((2184753/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 449, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 449, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 448, cos743o2c k) + cos743o2c 449 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 448) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_448
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 449 - ((172653/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_449).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_450 : ((8845747/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 450, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 450, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 449, cos743o2c k) + cos743o2c 450 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 449) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_449
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 450 - ((21357/100000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_450).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_451 : ((3423799/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 451, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 451, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 450, cos743o2c k) + cos743o2c 451 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 450) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_450
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 451 - ((-572399/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_451).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_452 : ((100803/6250 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 452, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 452, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 451, cos743o2c k) + cos743o2c 452 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 451) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_451
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 452 - ((-198083/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_452).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_453 : ((15352347/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 453, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 453, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 452, cos743o2c k) + cos743o2c 453 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 452) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_452
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 453 - ((-776033/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_453).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_454 : ((15283109/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 454, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 454, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 453, cos743o2c k) + cos743o2c 454 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 453) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_453
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 454 - ((-34569/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_454).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_455 : ((15963343/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 455, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 455, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 454, cos743o2c k) + cos743o2c 455 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 454) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_454
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 455 - ((340167/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_455).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_456 : ((16963219/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 456, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 456, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 455, cos743o2c k) + cos743o2c 456 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 455) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_455
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 456 - ((124997/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_456).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_457 : ((551717/31250 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 457, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 457, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 456, cos743o2c k) + cos743o2c 457 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 456) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_456
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 457 - ((27673/40000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_457).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_458 : ((17606851/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 458, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 458, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 457, cos743o2c k) + cos743o2c 458 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 457) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_457
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 458 - ((-47993/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_458).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_459 : ((674001/40000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 459, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 459, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 458, cos743o2c k) + cos743o2c 459 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 458) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_458
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 459 - ((-378363/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_459).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_460 : ((634181/40000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 460, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 460, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 459, cos743o2c k) + cos743o2c 460 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 459) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_459
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 460 - ((-4977/5000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_460).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_461 : ((7617467/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 461, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 461, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 460, cos743o2c k) + cos743o2c 461 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 460) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_460
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 461 - ((-619491/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_461).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_462 : ((15371279/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 462, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 462, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 461, cos743o2c k) + cos743o2c 462 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 461) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_461
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 462 - ((27289/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_462).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_463 : ((16178813/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 463, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 463, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 462, cos743o2c k) + cos743o2c 463 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 462) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_462
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 463 - ((403817/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_463).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_464 : ((3432831/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 464, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 464, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 463, cos743o2c k) + cos743o2c 464 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 463) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_463
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 464 - ((492721/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_464).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_465 : ((8864411/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 465, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 465, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 464, cos743o2c k) + cos743o2c 465 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 464) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_464
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 465 - ((564767/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_465).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_466 : ((3506421/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 466, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 466, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 465, cos743o2c k) + cos743o2c 466 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 465) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_465
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 466 - ((-196617/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_466).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_467 : ((16693653/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 467, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 467, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 466, cos743o2c k) + cos743o2c 467 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 466) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_466
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 467 - ((-52397/62500 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_467).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_468 : ((7858621/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 468, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 468, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 467, cos743o2c k) + cos743o2c 468 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 467) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_467
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 468 - ((-976311/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_468).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_469 : ((15186181/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 469, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 469, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 468, cos743o2c k) + cos743o2c 469 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 468) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_468
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 469 - ((-530961/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_469).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_470 : ((7707771/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 470, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 470, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 469, cos743o2c k) + cos743o2c 470 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 469) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_469
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 470 - ((229461/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_470).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_471 : ((1626813/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 471, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 471, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 470, cos743o2c k) + cos743o2c 471 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 470) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_470
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 471 - ((53293/62500 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_471).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_472 : ((4309947/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 472, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 472, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 471, cos743o2c k) + cos743o2c 472 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 471) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_471
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 472 - ((485879/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_472).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_473 : ((17759239/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 473, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 473, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 472, cos743o2c k) + cos743o2c 473 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 472) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_472
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 473 - ((519551/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_473).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_474 : ((3504621/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 474, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 474, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 473, cos743o2c k) + cos743o2c 474 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 473) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_473
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 474 - ((-118017/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_474).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_475 : ((833513/50000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 475, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 475, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 474, cos743o2c k) + cos743o2c 475 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 474) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_474
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 475 - ((-170549/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_475).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_476 : ((196211/12500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 476, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 476, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 475, cos743o2c k) + cos743o2c 476 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 475) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_475
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 476 - ((-6083/6250 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_476).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_477 : ((3033207/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 477, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 477, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 476, cos743o2c k) + cos743o2c 477 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 476) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_476
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 477 - ((-106149/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_477).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_478 : ((480711/31250 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 478, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 478, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 477, cos743o2c k) + cos743o2c 478 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 477) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_477
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 478 - ((216817/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_478).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_479 : ((4055341/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 479, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 479, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 478, cos743o2c k) + cos743o2c 479 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 478) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_478
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 479 - ((104839/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_479).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_480 : ((3440309/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 480, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 480, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 479, cos743o2c k) + cos743o2c 480 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 479) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_479
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 480 - ((980281/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_480).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_481 : ((3553011/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 481, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 481, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 480, cos743o2c k) + cos743o2c 481 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 480) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_480
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 481 - ((56361/100000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_481).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_482 : ((3518599/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 482, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 482, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 481, cos743o2c k) + cos743o2c 482 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 481) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_481
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 482 - ((-4299/25000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_482).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_483 : ((16783717/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 483, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 483, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 482, cos743o2c k) + cos743o2c 483 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 482) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_482
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 483 - ((-404589/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_483).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_484 : ((15793447/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 484, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 484, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 483, cos743o2c k) + cos743o2c 484 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 483) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_483
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 484 - ((-99017/100000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_484).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_485 : ((15177289/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 485, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 485, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 484, cos743o2c k) + cos743o2c 485 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 484) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_484
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 485 - ((-308029/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_485).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_486 : ((7639251/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 486, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 486, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 485, cos743o2c k) + cos743o2c 486 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 485) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_485
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 486 - ((101313/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_486).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_487 : ((8019783/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 487, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 487, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 486, cos743o2c k) + cos743o2c 487 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 486) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_486
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 487 - ((190291/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_487).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_488 : ((8518939/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 488, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 488, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 487, cos743o2c k) + cos743o2c 488 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 487) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_487
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 488 - ((249603/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_488).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_489 : ((3544463/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 489, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 489, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 488, cos743o2c k) + cos743o2c 489 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 488) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_488
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 489 - ((684537/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_489).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_490 : ((8858623/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 490, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 490, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 489, cos743o2c k) + cos743o2c 490 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 489) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_489
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 490 - ((-4969/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_490).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_491 : ((17026499/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 491, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 491, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 490, cos743o2c k) + cos743o2c 491 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 490) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_490
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 491 - ((-690647/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_491).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_492 : ((801389/50000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 492, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 492, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 491, cos743o2c k) + cos743o2c 492 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 491) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_491
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 492 - ((-998619/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_492).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_493 : ((3815989/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 493, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 493, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 492, cos743o2c k) + cos743o2c 493 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 492) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_492
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 493 - ((-190931/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_493).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_494 : ((15147863/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 494, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 494, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 493, cos743o2c k) + cos743o2c 494 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 493) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_493
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 494 - ((-115993/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_494).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_495 : ((3148187/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 495, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 495, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 494, cos743o2c k) + cos743o2c 495 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 494) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_494
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 495 - ((148293/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_495).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_496 : ((16723579/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 496, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 496, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 495, cos743o2c k) + cos743o2c 496 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 495) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_495
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 496 - ((122843/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_496).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_497 : ((8784783/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 497, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 497, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 496, cos743o2c k) + cos743o2c 497 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 496) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_496
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 497 - ((846087/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_497).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_498 : ((1114273/62500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 498, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 498, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 497, cos743o2c k) + cos743o2c 498 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 497) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_497
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 498 - ((129451/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_498).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_499 : ((8681763/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 499, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 499, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 498, cos743o2c k) + cos743o2c 499 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 498) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_498
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 499 - ((-232371/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_499).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum743o2_500 : ((3284383/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 500, cos743o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 500, cos743o2c k)
      = (∑ k ∈ Finset.Icc 11 499, cos743o2c k) + cos743o2c 500 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 499) (by norm_num) cos743o2c
    simpa using h
  have hprev := psum743o2_499
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos743o2c 500 - ((-941511/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos743o2_br_500).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

set_option maxHeartbeats 6400000 in
set_option maxRecDepth 16384 in
theorem psum743o2_floor : ∀ j : ℕ, 11 ≤ j → j ≤ 500 →
    ((0 : ℚ) : ℝ) ≤ ∑ k ∈ Finset.Icc 11 j, cos743o2c k := by
  intro j hj1 hj2
  interval_cases j
  · exact le_trans (by norm_num) psum743o2_11
  · exact le_trans (by norm_num) psum743o2_12
  · exact le_trans (by norm_num) psum743o2_13
  · exact le_trans (by norm_num) psum743o2_14
  · exact le_trans (by norm_num) psum743o2_15
  · exact le_trans (by norm_num) psum743o2_16
  · exact le_trans (by norm_num) psum743o2_17
  · exact le_trans (by norm_num) psum743o2_18
  · exact le_trans (by norm_num) psum743o2_19
  · exact le_trans (by norm_num) psum743o2_20
  · exact le_trans (by norm_num) psum743o2_21
  · exact le_trans (by norm_num) psum743o2_22
  · exact le_trans (by norm_num) psum743o2_23
  · exact le_trans (by norm_num) psum743o2_24
  · exact le_trans (by norm_num) psum743o2_25
  · exact le_trans (by norm_num) psum743o2_26
  · exact le_trans (by norm_num) psum743o2_27
  · exact le_trans (by norm_num) psum743o2_28
  · exact le_trans (by norm_num) psum743o2_29
  · exact le_trans (by norm_num) psum743o2_30
  · exact le_trans (by norm_num) psum743o2_31
  · exact le_trans (by norm_num) psum743o2_32
  · exact le_trans (by norm_num) psum743o2_33
  · exact le_trans (by norm_num) psum743o2_34
  · exact le_trans (by norm_num) psum743o2_35
  · exact le_trans (by norm_num) psum743o2_36
  · exact le_trans (by norm_num) psum743o2_37
  · exact le_trans (by norm_num) psum743o2_38
  · exact le_trans (by norm_num) psum743o2_39
  · exact le_trans (by norm_num) psum743o2_40
  · exact le_trans (by norm_num) psum743o2_41
  · exact le_trans (by norm_num) psum743o2_42
  · exact le_trans (by norm_num) psum743o2_43
  · exact le_trans (by norm_num) psum743o2_44
  · exact le_trans (by norm_num) psum743o2_45
  · exact le_trans (by norm_num) psum743o2_46
  · exact le_trans (by norm_num) psum743o2_47
  · exact le_trans (by norm_num) psum743o2_48
  · exact le_trans (by norm_num) psum743o2_49
  · exact le_trans (by norm_num) psum743o2_50
  · exact le_trans (by norm_num) psum743o2_51
  · exact le_trans (by norm_num) psum743o2_52
  · exact le_trans (by norm_num) psum743o2_53
  · exact le_trans (by norm_num) psum743o2_54
  · exact le_trans (by norm_num) psum743o2_55
  · exact le_trans (by norm_num) psum743o2_56
  · exact le_trans (by norm_num) psum743o2_57
  · exact le_trans (by norm_num) psum743o2_58
  · exact le_trans (by norm_num) psum743o2_59
  · exact le_trans (by norm_num) psum743o2_60
  · exact le_trans (by norm_num) psum743o2_61
  · exact le_trans (by norm_num) psum743o2_62
  · exact le_trans (by norm_num) psum743o2_63
  · exact le_trans (by norm_num) psum743o2_64
  · exact le_trans (by norm_num) psum743o2_65
  · exact le_trans (by norm_num) psum743o2_66
  · exact le_trans (by norm_num) psum743o2_67
  · exact le_trans (by norm_num) psum743o2_68
  · exact le_trans (by norm_num) psum743o2_69
  · exact le_trans (by norm_num) psum743o2_70
  · exact le_trans (by norm_num) psum743o2_71
  · exact le_trans (by norm_num) psum743o2_72
  · exact le_trans (by norm_num) psum743o2_73
  · exact le_trans (by norm_num) psum743o2_74
  · exact le_trans (by norm_num) psum743o2_75
  · exact le_trans (by norm_num) psum743o2_76
  · exact le_trans (by norm_num) psum743o2_77
  · exact le_trans (by norm_num) psum743o2_78
  · exact le_trans (by norm_num) psum743o2_79
  · exact le_trans (by norm_num) psum743o2_80
  · exact le_trans (by norm_num) psum743o2_81
  · exact le_trans (by norm_num) psum743o2_82
  · exact le_trans (by norm_num) psum743o2_83
  · exact le_trans (by norm_num) psum743o2_84
  · exact le_trans (by norm_num) psum743o2_85
  · exact le_trans (by norm_num) psum743o2_86
  · exact le_trans (by norm_num) psum743o2_87
  · exact le_trans (by norm_num) psum743o2_88
  · exact le_trans (by norm_num) psum743o2_89
  · exact le_trans (by norm_num) psum743o2_90
  · exact le_trans (by norm_num) psum743o2_91
  · exact le_trans (by norm_num) psum743o2_92
  · exact le_trans (by norm_num) psum743o2_93
  · exact le_trans (by norm_num) psum743o2_94
  · exact le_trans (by norm_num) psum743o2_95
  · exact le_trans (by norm_num) psum743o2_96
  · exact le_trans (by norm_num) psum743o2_97
  · exact le_trans (by norm_num) psum743o2_98
  · exact le_trans (by norm_num) psum743o2_99
  · exact le_trans (by norm_num) psum743o2_100
  · exact le_trans (by norm_num) psum743o2_101
  · exact le_trans (by norm_num) psum743o2_102
  · exact le_trans (by norm_num) psum743o2_103
  · exact le_trans (by norm_num) psum743o2_104
  · exact le_trans (by norm_num) psum743o2_105
  · exact le_trans (by norm_num) psum743o2_106
  · exact le_trans (by norm_num) psum743o2_107
  · exact le_trans (by norm_num) psum743o2_108
  · exact le_trans (by norm_num) psum743o2_109
  · exact le_trans (by norm_num) psum743o2_110
  · exact le_trans (by norm_num) psum743o2_111
  · exact le_trans (by norm_num) psum743o2_112
  · exact le_trans (by norm_num) psum743o2_113
  · exact le_trans (by norm_num) psum743o2_114
  · exact le_trans (by norm_num) psum743o2_115
  · exact le_trans (by norm_num) psum743o2_116
  · exact le_trans (by norm_num) psum743o2_117
  · exact le_trans (by norm_num) psum743o2_118
  · exact le_trans (by norm_num) psum743o2_119
  · exact le_trans (by norm_num) psum743o2_120
  · exact le_trans (by norm_num) psum743o2_121
  · exact le_trans (by norm_num) psum743o2_122
  · exact le_trans (by norm_num) psum743o2_123
  · exact le_trans (by norm_num) psum743o2_124
  · exact le_trans (by norm_num) psum743o2_125
  · exact le_trans (by norm_num) psum743o2_126
  · exact le_trans (by norm_num) psum743o2_127
  · exact le_trans (by norm_num) psum743o2_128
  · exact le_trans (by norm_num) psum743o2_129
  · exact le_trans (by norm_num) psum743o2_130
  · exact le_trans (by norm_num) psum743o2_131
  · exact le_trans (by norm_num) psum743o2_132
  · exact le_trans (by norm_num) psum743o2_133
  · exact le_trans (by norm_num) psum743o2_134
  · exact le_trans (by norm_num) psum743o2_135
  · exact le_trans (by norm_num) psum743o2_136
  · exact le_trans (by norm_num) psum743o2_137
  · exact le_trans (by norm_num) psum743o2_138
  · exact le_trans (by norm_num) psum743o2_139
  · exact le_trans (by norm_num) psum743o2_140
  · exact le_trans (by norm_num) psum743o2_141
  · exact le_trans (by norm_num) psum743o2_142
  · exact le_trans (by norm_num) psum743o2_143
  · exact le_trans (by norm_num) psum743o2_144
  · exact le_trans (by norm_num) psum743o2_145
  · exact le_trans (by norm_num) psum743o2_146
  · exact le_trans (by norm_num) psum743o2_147
  · exact le_trans (by norm_num) psum743o2_148
  · exact le_trans (by norm_num) psum743o2_149
  · exact le_trans (by norm_num) psum743o2_150
  · exact le_trans (by norm_num) psum743o2_151
  · exact le_trans (by norm_num) psum743o2_152
  · exact le_trans (by norm_num) psum743o2_153
  · exact le_trans (by norm_num) psum743o2_154
  · exact le_trans (by norm_num) psum743o2_155
  · exact le_trans (by norm_num) psum743o2_156
  · exact le_trans (by norm_num) psum743o2_157
  · exact le_trans (by norm_num) psum743o2_158
  · exact le_trans (by norm_num) psum743o2_159
  · exact le_trans (by norm_num) psum743o2_160
  · exact le_trans (by norm_num) psum743o2_161
  · exact le_trans (by norm_num) psum743o2_162
  · exact le_trans (by norm_num) psum743o2_163
  · exact le_trans (by norm_num) psum743o2_164
  · exact le_trans (by norm_num) psum743o2_165
  · exact le_trans (by norm_num) psum743o2_166
  · exact le_trans (by norm_num) psum743o2_167
  · exact le_trans (by norm_num) psum743o2_168
  · exact le_trans (by norm_num) psum743o2_169
  · exact le_trans (by norm_num) psum743o2_170
  · exact le_trans (by norm_num) psum743o2_171
  · exact le_trans (by norm_num) psum743o2_172
  · exact le_trans (by norm_num) psum743o2_173
  · exact le_trans (by norm_num) psum743o2_174
  · exact le_trans (by norm_num) psum743o2_175
  · exact le_trans (by norm_num) psum743o2_176
  · exact le_trans (by norm_num) psum743o2_177
  · exact le_trans (by norm_num) psum743o2_178
  · exact le_trans (by norm_num) psum743o2_179
  · exact le_trans (by norm_num) psum743o2_180
  · exact le_trans (by norm_num) psum743o2_181
  · exact le_trans (by norm_num) psum743o2_182
  · exact le_trans (by norm_num) psum743o2_183
  · exact le_trans (by norm_num) psum743o2_184
  · exact le_trans (by norm_num) psum743o2_185
  · exact le_trans (by norm_num) psum743o2_186
  · exact le_trans (by norm_num) psum743o2_187
  · exact le_trans (by norm_num) psum743o2_188
  · exact le_trans (by norm_num) psum743o2_189
  · exact le_trans (by norm_num) psum743o2_190
  · exact le_trans (by norm_num) psum743o2_191
  · exact le_trans (by norm_num) psum743o2_192
  · exact le_trans (by norm_num) psum743o2_193
  · exact le_trans (by norm_num) psum743o2_194
  · exact le_trans (by norm_num) psum743o2_195
  · exact le_trans (by norm_num) psum743o2_196
  · exact le_trans (by norm_num) psum743o2_197
  · exact le_trans (by norm_num) psum743o2_198
  · exact le_trans (by norm_num) psum743o2_199
  · exact le_trans (by norm_num) psum743o2_200
  · exact le_trans (by norm_num) psum743o2_201
  · exact le_trans (by norm_num) psum743o2_202
  · exact le_trans (by norm_num) psum743o2_203
  · exact le_trans (by norm_num) psum743o2_204
  · exact le_trans (by norm_num) psum743o2_205
  · exact le_trans (by norm_num) psum743o2_206
  · exact le_trans (by norm_num) psum743o2_207
  · exact le_trans (by norm_num) psum743o2_208
  · exact le_trans (by norm_num) psum743o2_209
  · exact le_trans (by norm_num) psum743o2_210
  · exact le_trans (by norm_num) psum743o2_211
  · exact le_trans (by norm_num) psum743o2_212
  · exact le_trans (by norm_num) psum743o2_213
  · exact le_trans (by norm_num) psum743o2_214
  · exact le_trans (by norm_num) psum743o2_215
  · exact le_trans (by norm_num) psum743o2_216
  · exact le_trans (by norm_num) psum743o2_217
  · exact le_trans (by norm_num) psum743o2_218
  · exact le_trans (by norm_num) psum743o2_219
  · exact le_trans (by norm_num) psum743o2_220
  · exact le_trans (by norm_num) psum743o2_221
  · exact le_trans (by norm_num) psum743o2_222
  · exact le_trans (by norm_num) psum743o2_223
  · exact le_trans (by norm_num) psum743o2_224
  · exact le_trans (by norm_num) psum743o2_225
  · exact le_trans (by norm_num) psum743o2_226
  · exact le_trans (by norm_num) psum743o2_227
  · exact le_trans (by norm_num) psum743o2_228
  · exact le_trans (by norm_num) psum743o2_229
  · exact le_trans (by norm_num) psum743o2_230
  · exact le_trans (by norm_num) psum743o2_231
  · exact le_trans (by norm_num) psum743o2_232
  · exact le_trans (by norm_num) psum743o2_233
  · exact le_trans (by norm_num) psum743o2_234
  · exact le_trans (by norm_num) psum743o2_235
  · exact le_trans (by norm_num) psum743o2_236
  · exact le_trans (by norm_num) psum743o2_237
  · exact le_trans (by norm_num) psum743o2_238
  · exact le_trans (by norm_num) psum743o2_239
  · exact le_trans (by norm_num) psum743o2_240
  · exact le_trans (by norm_num) psum743o2_241
  · exact le_trans (by norm_num) psum743o2_242
  · exact le_trans (by norm_num) psum743o2_243
  · exact le_trans (by norm_num) psum743o2_244
  · exact le_trans (by norm_num) psum743o2_245
  · exact le_trans (by norm_num) psum743o2_246
  · exact le_trans (by norm_num) psum743o2_247
  · exact le_trans (by norm_num) psum743o2_248
  · exact le_trans (by norm_num) psum743o2_249
  · exact le_trans (by norm_num) psum743o2_250
  · exact le_trans (by norm_num) psum743o2_251
  · exact le_trans (by norm_num) psum743o2_252
  · exact le_trans (by norm_num) psum743o2_253
  · exact le_trans (by norm_num) psum743o2_254
  · exact le_trans (by norm_num) psum743o2_255
  · exact le_trans (by norm_num) psum743o2_256
  · exact le_trans (by norm_num) psum743o2_257
  · exact le_trans (by norm_num) psum743o2_258
  · exact le_trans (by norm_num) psum743o2_259
  · exact le_trans (by norm_num) psum743o2_260
  · exact le_trans (by norm_num) psum743o2_261
  · exact le_trans (by norm_num) psum743o2_262
  · exact le_trans (by norm_num) psum743o2_263
  · exact le_trans (by norm_num) psum743o2_264
  · exact le_trans (by norm_num) psum743o2_265
  · exact le_trans (by norm_num) psum743o2_266
  · exact le_trans (by norm_num) psum743o2_267
  · exact le_trans (by norm_num) psum743o2_268
  · exact le_trans (by norm_num) psum743o2_269
  · exact le_trans (by norm_num) psum743o2_270
  · exact le_trans (by norm_num) psum743o2_271
  · exact le_trans (by norm_num) psum743o2_272
  · exact le_trans (by norm_num) psum743o2_273
  · exact le_trans (by norm_num) psum743o2_274
  · exact le_trans (by norm_num) psum743o2_275
  · exact le_trans (by norm_num) psum743o2_276
  · exact le_trans (by norm_num) psum743o2_277
  · exact le_trans (by norm_num) psum743o2_278
  · exact le_trans (by norm_num) psum743o2_279
  · exact le_trans (by norm_num) psum743o2_280
  · exact le_trans (by norm_num) psum743o2_281
  · exact le_trans (by norm_num) psum743o2_282
  · exact le_trans (by norm_num) psum743o2_283
  · exact le_trans (by norm_num) psum743o2_284
  · exact le_trans (by norm_num) psum743o2_285
  · exact le_trans (by norm_num) psum743o2_286
  · exact le_trans (by norm_num) psum743o2_287
  · exact le_trans (by norm_num) psum743o2_288
  · exact le_trans (by norm_num) psum743o2_289
  · exact le_trans (by norm_num) psum743o2_290
  · exact le_trans (by norm_num) psum743o2_291
  · exact le_trans (by norm_num) psum743o2_292
  · exact le_trans (by norm_num) psum743o2_293
  · exact le_trans (by norm_num) psum743o2_294
  · exact le_trans (by norm_num) psum743o2_295
  · exact le_trans (by norm_num) psum743o2_296
  · exact le_trans (by norm_num) psum743o2_297
  · exact le_trans (by norm_num) psum743o2_298
  · exact le_trans (by norm_num) psum743o2_299
  · exact le_trans (by norm_num) psum743o2_300
  · exact le_trans (by norm_num) psum743o2_301
  · exact le_trans (by norm_num) psum743o2_302
  · exact le_trans (by norm_num) psum743o2_303
  · exact le_trans (by norm_num) psum743o2_304
  · exact le_trans (by norm_num) psum743o2_305
  · exact le_trans (by norm_num) psum743o2_306
  · exact le_trans (by norm_num) psum743o2_307
  · exact le_trans (by norm_num) psum743o2_308
  · exact le_trans (by norm_num) psum743o2_309
  · exact le_trans (by norm_num) psum743o2_310
  · exact le_trans (by norm_num) psum743o2_311
  · exact le_trans (by norm_num) psum743o2_312
  · exact le_trans (by norm_num) psum743o2_313
  · exact le_trans (by norm_num) psum743o2_314
  · exact le_trans (by norm_num) psum743o2_315
  · exact le_trans (by norm_num) psum743o2_316
  · exact le_trans (by norm_num) psum743o2_317
  · exact le_trans (by norm_num) psum743o2_318
  · exact le_trans (by norm_num) psum743o2_319
  · exact le_trans (by norm_num) psum743o2_320
  · exact le_trans (by norm_num) psum743o2_321
  · exact le_trans (by norm_num) psum743o2_322
  · exact le_trans (by norm_num) psum743o2_323
  · exact le_trans (by norm_num) psum743o2_324
  · exact le_trans (by norm_num) psum743o2_325
  · exact le_trans (by norm_num) psum743o2_326
  · exact le_trans (by norm_num) psum743o2_327
  · exact le_trans (by norm_num) psum743o2_328
  · exact le_trans (by norm_num) psum743o2_329
  · exact le_trans (by norm_num) psum743o2_330
  · exact le_trans (by norm_num) psum743o2_331
  · exact le_trans (by norm_num) psum743o2_332
  · exact le_trans (by norm_num) psum743o2_333
  · exact le_trans (by norm_num) psum743o2_334
  · exact le_trans (by norm_num) psum743o2_335
  · exact le_trans (by norm_num) psum743o2_336
  · exact le_trans (by norm_num) psum743o2_337
  · exact le_trans (by norm_num) psum743o2_338
  · exact le_trans (by norm_num) psum743o2_339
  · exact le_trans (by norm_num) psum743o2_340
  · exact le_trans (by norm_num) psum743o2_341
  · exact le_trans (by norm_num) psum743o2_342
  · exact le_trans (by norm_num) psum743o2_343
  · exact le_trans (by norm_num) psum743o2_344
  · exact le_trans (by norm_num) psum743o2_345
  · exact le_trans (by norm_num) psum743o2_346
  · exact le_trans (by norm_num) psum743o2_347
  · exact le_trans (by norm_num) psum743o2_348
  · exact le_trans (by norm_num) psum743o2_349
  · exact le_trans (by norm_num) psum743o2_350
  · exact le_trans (by norm_num) psum743o2_351
  · exact le_trans (by norm_num) psum743o2_352
  · exact le_trans (by norm_num) psum743o2_353
  · exact le_trans (by norm_num) psum743o2_354
  · exact le_trans (by norm_num) psum743o2_355
  · exact le_trans (by norm_num) psum743o2_356
  · exact le_trans (by norm_num) psum743o2_357
  · exact le_trans (by norm_num) psum743o2_358
  · exact le_trans (by norm_num) psum743o2_359
  · exact le_trans (by norm_num) psum743o2_360
  · exact le_trans (by norm_num) psum743o2_361
  · exact le_trans (by norm_num) psum743o2_362
  · exact le_trans (by norm_num) psum743o2_363
  · exact le_trans (by norm_num) psum743o2_364
  · exact le_trans (by norm_num) psum743o2_365
  · exact le_trans (by norm_num) psum743o2_366
  · exact le_trans (by norm_num) psum743o2_367
  · exact le_trans (by norm_num) psum743o2_368
  · exact le_trans (by norm_num) psum743o2_369
  · exact le_trans (by norm_num) psum743o2_370
  · exact le_trans (by norm_num) psum743o2_371
  · exact le_trans (by norm_num) psum743o2_372
  · exact le_trans (by norm_num) psum743o2_373
  · exact le_trans (by norm_num) psum743o2_374
  · exact le_trans (by norm_num) psum743o2_375
  · exact le_trans (by norm_num) psum743o2_376
  · exact le_trans (by norm_num) psum743o2_377
  · exact le_trans (by norm_num) psum743o2_378
  · exact le_trans (by norm_num) psum743o2_379
  · exact le_trans (by norm_num) psum743o2_380
  · exact le_trans (by norm_num) psum743o2_381
  · exact le_trans (by norm_num) psum743o2_382
  · exact le_trans (by norm_num) psum743o2_383
  · exact le_trans (by norm_num) psum743o2_384
  · exact le_trans (by norm_num) psum743o2_385
  · exact le_trans (by norm_num) psum743o2_386
  · exact le_trans (by norm_num) psum743o2_387
  · exact le_trans (by norm_num) psum743o2_388
  · exact le_trans (by norm_num) psum743o2_389
  · exact le_trans (by norm_num) psum743o2_390
  · exact le_trans (by norm_num) psum743o2_391
  · exact le_trans (by norm_num) psum743o2_392
  · exact le_trans (by norm_num) psum743o2_393
  · exact le_trans (by norm_num) psum743o2_394
  · exact le_trans (by norm_num) psum743o2_395
  · exact le_trans (by norm_num) psum743o2_396
  · exact le_trans (by norm_num) psum743o2_397
  · exact le_trans (by norm_num) psum743o2_398
  · exact le_trans (by norm_num) psum743o2_399
  · exact le_trans (by norm_num) psum743o2_400
  · exact le_trans (by norm_num) psum743o2_401
  · exact le_trans (by norm_num) psum743o2_402
  · exact le_trans (by norm_num) psum743o2_403
  · exact le_trans (by norm_num) psum743o2_404
  · exact le_trans (by norm_num) psum743o2_405
  · exact le_trans (by norm_num) psum743o2_406
  · exact le_trans (by norm_num) psum743o2_407
  · exact le_trans (by norm_num) psum743o2_408
  · exact le_trans (by norm_num) psum743o2_409
  · exact le_trans (by norm_num) psum743o2_410
  · exact le_trans (by norm_num) psum743o2_411
  · exact le_trans (by norm_num) psum743o2_412
  · exact le_trans (by norm_num) psum743o2_413
  · exact le_trans (by norm_num) psum743o2_414
  · exact le_trans (by norm_num) psum743o2_415
  · exact le_trans (by norm_num) psum743o2_416
  · exact le_trans (by norm_num) psum743o2_417
  · exact le_trans (by norm_num) psum743o2_418
  · exact le_trans (by norm_num) psum743o2_419
  · exact le_trans (by norm_num) psum743o2_420
  · exact le_trans (by norm_num) psum743o2_421
  · exact le_trans (by norm_num) psum743o2_422
  · exact le_trans (by norm_num) psum743o2_423
  · exact le_trans (by norm_num) psum743o2_424
  · exact le_trans (by norm_num) psum743o2_425
  · exact le_trans (by norm_num) psum743o2_426
  · exact le_trans (by norm_num) psum743o2_427
  · exact le_trans (by norm_num) psum743o2_428
  · exact le_trans (by norm_num) psum743o2_429
  · exact le_trans (by norm_num) psum743o2_430
  · exact le_trans (by norm_num) psum743o2_431
  · exact le_trans (by norm_num) psum743o2_432
  · exact le_trans (by norm_num) psum743o2_433
  · exact le_trans (by norm_num) psum743o2_434
  · exact le_trans (by norm_num) psum743o2_435
  · exact le_trans (by norm_num) psum743o2_436
  · exact le_trans (by norm_num) psum743o2_437
  · exact le_trans (by norm_num) psum743o2_438
  · exact le_trans (by norm_num) psum743o2_439
  · exact le_trans (by norm_num) psum743o2_440
  · exact le_trans (by norm_num) psum743o2_441
  · exact le_trans (by norm_num) psum743o2_442
  · exact le_trans (by norm_num) psum743o2_443
  · exact le_trans (by norm_num) psum743o2_444
  · exact le_trans (by norm_num) psum743o2_445
  · exact le_trans (by norm_num) psum743o2_446
  · exact le_trans (by norm_num) psum743o2_447
  · exact le_trans (by norm_num) psum743o2_448
  · exact le_trans (by norm_num) psum743o2_449
  · exact le_trans (by norm_num) psum743o2_450
  · exact le_trans (by norm_num) psum743o2_451
  · exact le_trans (by norm_num) psum743o2_452
  · exact le_trans (by norm_num) psum743o2_453
  · exact le_trans (by norm_num) psum743o2_454
  · exact le_trans (by norm_num) psum743o2_455
  · exact le_trans (by norm_num) psum743o2_456
  · exact le_trans (by norm_num) psum743o2_457
  · exact le_trans (by norm_num) psum743o2_458
  · exact le_trans (by norm_num) psum743o2_459
  · exact le_trans (by norm_num) psum743o2_460
  · exact le_trans (by norm_num) psum743o2_461
  · exact le_trans (by norm_num) psum743o2_462
  · exact le_trans (by norm_num) psum743o2_463
  · exact le_trans (by norm_num) psum743o2_464
  · exact le_trans (by norm_num) psum743o2_465
  · exact le_trans (by norm_num) psum743o2_466
  · exact le_trans (by norm_num) psum743o2_467
  · exact le_trans (by norm_num) psum743o2_468
  · exact le_trans (by norm_num) psum743o2_469
  · exact le_trans (by norm_num) psum743o2_470
  · exact le_trans (by norm_num) psum743o2_471
  · exact le_trans (by norm_num) psum743o2_472
  · exact le_trans (by norm_num) psum743o2_473
  · exact le_trans (by norm_num) psum743o2_474
  · exact le_trans (by norm_num) psum743o2_475
  · exact le_trans (by norm_num) psum743o2_476
  · exact le_trans (by norm_num) psum743o2_477
  · exact le_trans (by norm_num) psum743o2_478
  · exact le_trans (by norm_num) psum743o2_479
  · exact le_trans (by norm_num) psum743o2_480
  · exact le_trans (by norm_num) psum743o2_481
  · exact le_trans (by norm_num) psum743o2_482
  · exact le_trans (by norm_num) psum743o2_483
  · exact le_trans (by norm_num) psum743o2_484
  · exact le_trans (by norm_num) psum743o2_485
  · exact le_trans (by norm_num) psum743o2_486
  · exact le_trans (by norm_num) psum743o2_487
  · exact le_trans (by norm_num) psum743o2_488
  · exact le_trans (by norm_num) psum743o2_489
  · exact le_trans (by norm_num) psum743o2_490
  · exact le_trans (by norm_num) psum743o2_491
  · exact le_trans (by norm_num) psum743o2_492
  · exact le_trans (by norm_num) psum743o2_493
  · exact le_trans (by norm_num) psum743o2_494
  · exact le_trans (by norm_num) psum743o2_495
  · exact le_trans (by norm_num) psum743o2_496
  · exact le_trans (by norm_num) psum743o2_497
  · exact le_trans (by norm_num) psum743o2_498
  · exact le_trans (by norm_num) psum743o2_499
  · exact le_trans (by norm_num) psum743o2_500

end CriticalLinePhasor.DVP

section AxiomAudit
#print axioms CriticalLinePhasor.DVP.psum743o2_floor
#print axioms CriticalLinePhasor.DVP.psum743o2_500
end AxiomAudit
