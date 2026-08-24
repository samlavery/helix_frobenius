import RequestProject.DVPCos813o2Table

/-!
# The cosine partial-sum floor, `t = 813/2` (N = 500)
-/

open Finset

noncomputable section

namespace CriticalLinePhasor.DVP

/-- The cosine sequence of the `t = 813/2` segment certificate. -/
def cos813o2c (n : ℕ) : ℝ := Real.cos (((813:ℕ):ℝ) * (Real.log n / 2))

theorem psum813o2_11 : ((4121/6250 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 11, cos813o2c k := by
  rw [Finset.Icc_self, Finset.sum_singleton]
  have h : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 11 - ((32973/50000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_11).1
  push_cast at h ⊢
  linarith

theorem psum813o2_12 : ((751643/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 12, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 12, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 11, cos813o2c k) + cos813o2c 12 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 11) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_11
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 12 - ((92383/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_12).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_13 : ((337709/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 13, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 13, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 12, cos813o2c k) + cos813o2c 13 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 12) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_12
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 13 - ((468501/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_13).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_14 : ((1611443/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 14, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 14, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 13, cos813o2c k) + cos813o2c 14 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 13) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_13
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 14 - ((-38501/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_14).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_15 : ((956199/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 15, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 15, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 14, cos813o2c k) + cos813o2c 15 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 14) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_14
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 15 - ((60211/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_15).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_16 : ((598741/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 16, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 16, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 15, cos813o2c k) + cos813o2c 16 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 15) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_15
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 16 - ((-11169/15625 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_16).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_17 : ((894687/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 17, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 17, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 16, cos813o2c k) + cos813o2c 17 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 16) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_16
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 17 - ((-60539/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_17).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_18 : ((473599/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 18, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 18, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 17, cos813o2c k) + cos813o2c 18 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 17) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_17
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 18 - ((999809/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_18).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_19 : ((44741/50000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 19, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 19, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 18, cos813o2c k) + cos813o2c 19 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 18) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_18
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 19 - ((-249869/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_19).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_20 : ((1282301/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 20, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 20, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 19, cos813o2c k) + cos813o2c 20 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 19) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_19
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 20 - ((387581/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_20).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_21 : ((2264369/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 21, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 21, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 20, cos813o2c k) + cos813o2c 21 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 20) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_20
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 21 - ((122771/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_21).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_22 : ((3256049/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 22, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 22, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 21, cos813o2c k) + cos813o2c 22 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 21) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_21
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 22 - ((49589/50000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_22).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_23 : ((3871111/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 23, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 23, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 22, cos813o2c k) + cos813o2c 23 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 22) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_22
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 23 - ((307581/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_23).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_24 : ((619231/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 24, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 24, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 23, cos813o2c k) + cos813o2c 24 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 23) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_23
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 24 - ((-96857/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_24).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_25 : ((1548181/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 25, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 25, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 24, cos813o2c k) + cos813o2c 25 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 24) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_24
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 25 - ((307/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_25).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_26 : ((66581/20000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 26, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 26, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 25, cos813o2c k) + cos813o2c 26 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 25) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_25
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 26 - ((58197/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_26).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_27 : ((1730079/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 27, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 27, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 26, cos813o2c k) + cos813o2c 27 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 26) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_26
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 27 - ((16401/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_27).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_28 : ((20717/8000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 28, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 28, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 27, cos813o2c k) + cos813o2c 28 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 27) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_27
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 28 - ((-870433/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_28).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_29 : ((3188453/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 29, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 29, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 28, cos813o2c k) + cos813o2c 29 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 28) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_28
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 29 - ((37433/62500 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_29).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_30 : ((2073873/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 30, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 30, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 29, cos813o2c k) + cos813o2c 30 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 29) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_29
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 30 - ((959393/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_30).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_31 : ((4646363/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 31, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 31, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 30, cos813o2c k) + cos813o2c 31 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 30) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_30
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 31 - ((498717/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_31).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_32 : ((4827891/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 32, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 32, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 31, cos813o2c k) + cos813o2c 32 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 31) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_31
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 32 - ((45407/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_32).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_33 : ((63323/12500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 33, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 33, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 32, cos813o2c k) + cos813o2c 33 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 32) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_32
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 33 - ((238049/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_33).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_34 : ((5687887/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 34, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 34, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 33, cos813o2c k) + cos813o2c 34 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 33) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_33
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 34 - ((622147/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_34).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_35 : ((267241/40000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 35, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 35, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 34, cos813o2c k) + cos813o2c 35 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 34) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_34
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 35 - ((496619/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_35).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_36 : ((7222457/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 36, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 36, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 35, cos813o2c k) + cos813o2c 36 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 35) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_35
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 36 - ((135383/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_36).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_37 : ((808357/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 37, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 37, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 36, cos813o2c k) + cos813o2c 37 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 36) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_36
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 37 - ((-755501/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_37).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_38 : ((742007/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 38, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 38, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 37, cos813o2c k) + cos813o2c 38 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 37) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_37
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 38 - ((-5307/10000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_38).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_39 : ((3464207/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 39, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 39, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 38, cos813o2c k) + cos813o2c 39 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 38) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_38
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 39 - ((496229/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_39).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_40 : ((6379457/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 40, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 40, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 39, cos813o2c k) + cos813o2c 40 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 39) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_39
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 40 - ((-548857/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_40).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_41 : ((3173797/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 41, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 41, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 40, cos813o2c k) + cos813o2c 41 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 40) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_40
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 41 - ((-31763/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_41).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_42 : ((1347873/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 42, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 42, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 41, cos813o2c k) + cos813o2c 42 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 41) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_41
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 42 - ((391871/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_42).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_43 : ((97227/15625 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 43, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 43, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 42, cos813o2c k) + cos813o2c 43 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 42) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_42
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 43 - ((-516737/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_43).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_44 : ((6669499/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 44, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 44, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 43, cos813o2c k) + cos813o2c 44 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 43) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_43
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 44 - ((447071/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_44).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_45 : ((649637/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 45, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 45, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 44, cos813o2c k) + cos813o2c 45 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 44) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_44
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 45 - ((-173029/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_45).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_46 : ((3092537/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 46, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 46, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 45, cos813o2c k) + cos813o2c 46 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 45) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_45
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 46 - ((-77799/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_46).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_47 : ((351293/50000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 47, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 47, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 46, cos813o2c k) + cos813o2c 47 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 46) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_46
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 47 - ((420443/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_47).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_48 : ((6068869/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 48, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 48, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 47, cos813o2c k) + cos813o2c 48 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 47) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_47
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 48 - ((-956891/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_48).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_49 : ((393731/62500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 49, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 49, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 48, cos813o2c k) + cos813o2c 49 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 48) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_48
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 49 - ((230927/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_49).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_50 : ((1782427/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 50, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 50, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 49, cos813o2c k) + cos813o2c 50 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 49) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_49
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 50 - ((25941/31250 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_50).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_51 : ((100331/15625 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 51, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 51, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 50, cos813o2c k) + cos813o2c 51 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 50) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_50
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 51 - ((-88553/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_51).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_52 : ((1148761/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 52, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 52, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 51, cos813o2c k) + cos813o2c 52 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 51) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_51
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 52 - ((-677279/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_52).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_53 : ((1599991/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 53, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 53, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 52, cos813o2c k) + cos813o2c 53 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 52) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_52
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 53 - ((656259/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_53).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_54 : ((455989/62500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 54, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 54, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 53, cos813o2c k) + cos813o2c 54 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 53) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_53
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 54 - ((22399/25000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_54).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_55 : ((1807659/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 55, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 55, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 54, cos813o2c k) + cos813o2c 55 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 54) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_54
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 55 - ((-1017/15625 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_55).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_56 : ((6336413/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 56, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 56, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 55, cos813o2c k) + cos813o2c 56 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 55) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_55
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 56 - ((-894123/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_56).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_57 : ((5434727/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 57, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 57, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 56, cos813o2c k) + cos813o2c 57 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 56) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_56
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 57 - ((-450793/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_57).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_58 : ((5104121/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 58, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 58, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 57, cos813o2c k) + cos813o2c 58 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 57) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_57
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 58 - ((-165253/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_58).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_59 : ((217079/40000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 59, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 59, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 58, cos813o2c k) + cos813o2c 59 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 58) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_58
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 59 - ((161477/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_59).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_60 : ((3098089/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 60, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 60, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 59, cos813o2c k) + cos813o2c 60 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 59) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_59
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 60 - ((769303/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_60).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_61 : ((7163217/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 61, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 61, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 60, cos813o2c k) + cos813o2c 61 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 60) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_60
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 61 - ((967139/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_61).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_62 : ((8160693/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 62, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 62, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 61, cos813o2c k) + cos813o2c 62 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 61) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_61
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 62 - ((124697/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_62).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_63 : ((9118661/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 63, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 63, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 62, cos813o2c k) + cos813o2c 63 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 62) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_62
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 63 - ((239517/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_63).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_64 : ((2007207/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 64, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 64, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 63, cos813o2c k) + cos813o2c 64 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 63) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_63
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 64 - ((458737/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_64).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_65 : ((10945573/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 65, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 65, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 64, cos813o2c k) + cos813o2c 65 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 64) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_64
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 65 - ((454819/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_65).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_66 : ((185693/15625 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 66, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 66, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 65, cos813o2c k) + cos813o2c 66 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 65) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_65
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 66 - ((938879/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_66).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_67 : ((804243/62500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 67, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 67, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 66, cos813o2c k) + cos813o2c 67 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 66) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_66
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 67 - ((245909/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_67).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_68 : ((2772923/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 68, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 68, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 67, cos813o2c k) + cos813o2c 68 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 67) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_67
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 68 - ((996827/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_68).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_69 : ((14774121/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 69, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 69, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 68, cos813o2c k) + cos813o2c 69 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 68) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_68
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 69 - ((454803/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_69).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_70 : ((3084891/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 70, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 70, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 69, cos813o2c k) + cos813o2c 70 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 69) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_69
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 70 - ((325217/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_70).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_71 : ((7807103/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 71, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 71, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 70, cos813o2c k) + cos813o2c 71 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 70) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_70
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 71 - ((189851/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_71).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_72 : ((3043697/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 72, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 72, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 71, cos813o2c k) + cos813o2c 72 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 71) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_71
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 72 - ((-395621/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_72).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_73 : ((14335039/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 73, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 73, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 72, cos813o2c k) + cos813o2c 73 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 72) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_72
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 73 - ((-441673/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_73).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_74 : ((13369759/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 74, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 74, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 73, cos813o2c k) + cos813o2c 74 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 73) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_73
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 74 - ((-48259/50000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_74).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_75 : ((645419/50000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 75, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 75, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 74, cos813o2c k) + cos813o2c 75 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 74) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_74
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 75 - ((-461279/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_75).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_76 : ((13315653/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 76, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 76, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 75, cos813o2c k) + cos813o2c 76 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 75) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_75
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 76 - ((407373/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_76).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_77 : ((2859813/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 77, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 77, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 76, cos813o2c k) + cos813o2c 77 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 76) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_76
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 77 - ((122939/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_77).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_78 : ((7477173/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 78, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 78, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 77, cos813o2c k) + cos813o2c 78 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 77) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_77
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 78 - ((655381/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_78).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_79 : ((1457397/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 79, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 79, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 78, cos813o2c k) + cos813o2c 79 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 78) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_78
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 79 - ((-95069/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_79).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_80 : ((1696741/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 80, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 80, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 79, cos813o2c k) + cos813o2c 80 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 79) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_79
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 80 - ((-499971/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_80).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_81 : ((13232663/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 81, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 81, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 80, cos813o2c k) + cos813o2c 81 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 80) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_80
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 81 - ((-68233/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_81).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_82 : ((7022183/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 82, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 82, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 81, cos813o2c k) + cos813o2c 82 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 81) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_81
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 82 - ((811803/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_82).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_83 : ((7393961/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 83, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 83, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 82, cos813o2c k) + cos813o2c 83 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 82) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_82
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 83 - ((92957/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_83).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_84 : ((445089/31250 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 84, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 84, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 83, cos813o2c k) + cos813o2c 84 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 83) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_83
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 84 - ((-272487/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_84).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_85 : ((13354851/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 85, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 85, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 84, cos813o2c k) + cos813o2c 85 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 84) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_84
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 85 - ((-887897/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_85).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_86 : ((551083/40000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 86, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 86, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 85, cos813o2c k) + cos813o2c 86 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 85) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_85
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 86 - ((105581/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_86).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_87 : ((917369/62500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 87, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 87, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 86, cos813o2c k) + cos813o2c 87 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 86) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_86
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 87 - ((900929/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_87).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_88 : ((14184823/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 88, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 88, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 87, cos813o2c k) + cos813o2c 88 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 87) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_87
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 88 - ((-492981/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_88).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_89 : ((13379447/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 89, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 89, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 88, cos813o2c k) + cos813o2c 89 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 88) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_88
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 89 - ((-201319/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_89).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_90 : ((7050123/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 90, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 90, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 89, cos813o2c k) + cos813o2c 90 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 89) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_89
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 90 - ((720899/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_90).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_91 : ((14618627/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 91, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 91, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 90, cos813o2c k) + cos813o2c 91 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 90) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_90
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 91 - ((518481/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_91).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_92 : ((2731239/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 92, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 92, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 91, cos813o2c k) + cos813o2c 92 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 91) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_91
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 92 - ((-240583/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_92).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_93 : ((13698497/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 93, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 93, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 92, cos813o2c k) + cos813o2c 93 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 92) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_92
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 93 - ((21201/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_93).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_94 : ((3654161/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 94, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 94, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 93, cos813o2c k) + cos813o2c 94 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 93) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_93
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 94 - ((918247/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_94).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_95 : ((3471703/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 95, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 95, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 94, cos813o2c k) + cos813o2c 95 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 94) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_94
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 95 - ((-182433/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_95).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_96 : ((13594001/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 96, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 96, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 95, cos813o2c k) + cos813o2c 96 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 95) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_95
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 96 - ((-292711/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_96).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_97 : ((14573397/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 97, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 97, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 96, cos813o2c k) + cos813o2c 97 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 96) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_96
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 97 - ((122437/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_97).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_98 : ((13894611/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 98, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 98, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 97, cos813o2c k) + cos813o2c 98 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 97) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_97
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 98 - ((-339343/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_98).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_99 : ((3414351/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 99, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 99, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 98, cos813o2c k) + cos813o2c 99 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 98) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_98
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 99 - ((-237107/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_99).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_100 : ((729157/50000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 100, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 100, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 99, cos813o2c k) + cos813o2c 100 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 99) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_99
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 100 - ((231459/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_100).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_101 : ((13713087/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 101, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 101, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 100, cos813o2c k) + cos813o2c 101 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 100) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_100
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 101 - ((-869953/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_101).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_102 : ((6951777/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 102, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 102, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 101, cos813o2c k) + cos813o2c 102 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 101) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_101
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 102 - ((190567/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_102).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_103 : ((2898927/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 103, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 103, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 102, cos813o2c k) + cos813o2c 103 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 102) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_102
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 103 - ((591181/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_103).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_104 : ((13506111/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 104, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 104, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 103, cos813o2c k) + cos813o2c 104 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 103) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_103
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 104 - ((-123553/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_104).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_105 : ((716677/50000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 105, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 105, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 104, cos813o2c k) + cos813o2c 105 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 104) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_104
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 105 - ((827529/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_105).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_106 : ((3518319/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 106, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 106, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 105, cos813o2c k) + cos813o2c 106 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 105) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_105
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 106 - ((-65041/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_106).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_107 : ((13672579/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 107, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 107, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 106, cos813o2c k) + cos813o2c 107 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 106) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_106
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 107 - ((-400597/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_107).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_108 : ((454403/31250 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 108, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 108, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 107, cos813o2c k) + cos813o2c 108 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 107) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_107
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 108 - ((868417/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_108).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_109 : ((2708901/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 109, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 109, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 108, cos813o2c k) + cos813o2c 109 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 108) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_108
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 109 - ((-996291/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_109).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_110 : ((14336277/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 110, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 110, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 109, cos813o2c k) + cos813o2c 110 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 109) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_109
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 110 - ((12373/15625 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_110).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_111 : ((6984173/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 111, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 111, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 110, cos813o2c k) + cos813o2c 111 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 110) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_110
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 111 - ((-367831/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_111).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_112 : ((13841123/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 112, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 112, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 111, cos813o2c k) + cos813o2c 112 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 111) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_111
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 112 - ((-127123/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_112).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_113 : ((14405049/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 113, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 113, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 112, cos813o2c k) + cos813o2c 113 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 112) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_112
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 113 - ((282013/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_113).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_114 : ((2708593/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 114, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 114, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 113, cos813o2c k) + cos813o2c 114 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 113) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_113
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 114 - ((-26937/31250 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_114).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_115 : ((7267657/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 115, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 115, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 114, cos813o2c k) + cos813o2c 115 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 114) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_114
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 115 - ((992449/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_115).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_116 : ((13567529/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 116, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 116, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 115, cos813o2c k) + cos813o2c 116 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 115) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_115
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 116 - ((-193537/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_116).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_117 : ((14391273/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 117, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 117, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 116, cos813o2c k) + cos813o2c 117 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 116) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_116
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 117 - ((205961/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_117).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_118 : ((2757173/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 118, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 118, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 117, cos813o2c k) + cos813o2c 118 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 117) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_117
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 118 - ((-151327/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_118).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_119 : ((565573/40000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 119, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 119, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 118, cos813o2c k) + cos813o2c 119 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 118) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_118
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 119 - ((8839/25000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_119).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_120 : ((2807629/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 120, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 120, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 119, cos813o2c k) + cos813o2c 120 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 119) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_119
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 120 - ((-2527/25000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_120).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_121 : ((13907799/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 121, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 121, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 120, cos813o2c k) + cos813o2c 121 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 120) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_120
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 121 - ((-65123/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_121).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_122 : ((7118103/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 122, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 122, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 121, cos813o2c k) + cos813o2c 122 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 121) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_121
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 122 - ((328507/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_122).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_123 : ((1374661/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 123, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 123, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 122, cos813o2c k) + cos813o2c 123 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 122) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_122
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 123 - ((-61187/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_123).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_124 : ((3590189/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 124, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 124, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 123, cos813o2c k) + cos813o2c 124 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 123) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_123
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 124 - ((307123/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_124).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_125 : ((6826941/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 125, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 125, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 124, cos813o2c k) + cos813o2c 125 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 124) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_124
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 125 - ((-353387/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_125).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_126 : ((14426053/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 126, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 126, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 125, cos813o2c k) + cos813o2c 126 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 125) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_125
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 126 - ((772271/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_126).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_127 : ((13610079/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 127, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 127, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 126, cos813o2c k) + cos813o2c 127 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 126) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_126
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 127 - ((-407937/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_127).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_128 : ((14451939/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 128, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 128, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 127, cos813o2c k) + cos813o2c 128 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 127) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_127
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 128 - ((21049/25000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_128).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_129 : ((339957/25000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 129, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 129, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 128, cos813o2c k) + cos813o2c 129 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 128) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_128
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 129 - ((-853559/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_129).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_130 : ((14450381/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 130, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 130, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 129, cos813o2c k) + cos813o2c 130 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 129) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_129
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 130 - ((852201/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_130).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_131 : ((1361231/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 131, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 131, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 130, cos813o2c k) + cos813o2c 131 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 130) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_130
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 131 - ((-837971/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_131).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_132 : ((1442167/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 132, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 132, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 131, cos813o2c k) + cos813o2c 132 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 131) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_131
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 132 - ((40473/50000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_132).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_133 : ((6828757/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 133, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 133, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 132, cos813o2c k) + cos813o2c 133 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 132) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_132
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 133 - ((-95507/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_133).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_134 : ((3588913/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 134, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 134, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 133, cos813o2c k) + cos813o2c 134 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 133) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_133
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 134 - ((349119/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_134).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_135 : ((6873733/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 135, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 135, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 134, cos813o2c k) + cos813o2c 135 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 134) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_134
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 135 - ((-304043/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_135).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_136 : ((2847469/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 136, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 136, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 135, cos813o2c k) + cos813o2c 136 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 135) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_135
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 136 - ((489979/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_136).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_137 : ((6947863/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 137, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 137, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 136, cos813o2c k) + cos813o2c 137 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 136) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_136
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 137 - ((-341519/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_137).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_138 : ((14058193/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 138, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 138, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 137, cos813o2c k) + cos813o2c 138 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 137) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_137
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 138 - ((162567/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_138).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_139 : ((881333/62500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 139, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 139, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 138, cos813o2c k) + cos813o2c 139 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 138) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_138
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 139 - ((8647/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_139).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_140 : ((13833681/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 140, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 140, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 139, cos813o2c k) + cos813o2c 140 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 139) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_139
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 140 - ((-267547/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_140).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_141 : ((716489/50000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 141, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 141, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 140, cos813o2c k) + cos813o2c 141 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 140) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_140
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 141 - ((496199/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_141).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_142 : ((6810371/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 142, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 142, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 141, cos813o2c k) + cos813o2c 142 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 141) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_141
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 142 - ((-354469/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_142).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_143 : ((3625287/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 143, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 143, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 142, cos813o2c k) + cos813o2c 143 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 142) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_142
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 143 - ((440253/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_143).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_144 : ((6759057/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 144, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 144, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 143, cos813o2c k) + cos813o2c 144 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 143) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_143
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 144 - ((-491467/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_144).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_145 : ((58031/4000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 145, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 145, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 144, cos813o2c k) + cos813o2c 145 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 144) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_144
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 145 - ((123717/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_145).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_146 : ((13625863/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 146, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 146, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 145, cos813o2c k) + cos813o2c 146 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 145) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_145
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 146 - ((-881787/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_146).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_147 : ((7139849/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 147, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 147, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 146, cos813o2c k) + cos813o2c 147 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 146) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_146
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 147 - ((130787/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_147).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_148 : ((218098/15625 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 148, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 148, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 147, cos813o2c k) + cos813o2c 148 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 147) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_147
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 148 - ((-160663/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_148).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_149 : ((3470299/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 149, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 149, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 148, cos813o2c k) + cos813o2c 149 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 148) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_148
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 149 - ((-4811/62500 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_149).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_150 : ((897511/62500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 150, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 150, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 149, cos813o2c k) + cos813o2c 150 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 149) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_149
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 150 - ((11977/25000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_150).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_151 : ((6776209/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 151, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 151, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 150, cos813o2c k) + cos813o2c 151 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 150) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_150
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 151 - ((-403829/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_151).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_152 : ((581501/40000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 152, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 152, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 151, cos813o2c k) + cos813o2c 152 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 151) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_151
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 152 - ((985207/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_152).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_153 : ((848951/62500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 153, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 153, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 152, cos813o2c k) + cos813o2c 153 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 152) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_152
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 153 - ((-954209/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_153).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_154 : ((14281859/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 154, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 154, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 153, cos813o2c k) + cos813o2c 154 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 153) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_153
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 154 - ((698743/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_154).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_155 : ((3505417/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 155, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 155, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 154, cos813o2c k) + cos813o2c 155 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 154) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_154
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 155 - ((-260091/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_155).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_156 : ((43001/3125 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 156, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 156, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 155, cos813o2c k) + cos813o2c 156 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 155) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_155
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 156 - ((-4082/15625 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_156).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_157 : ((181043/12500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 157, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 157, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 156, cos813o2c k) + cos813o2c 157 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 156) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_156
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 157 - ((36161/50000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_157).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_158 : ((13503613/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 158, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 158, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 157, cos813o2c k) + cos813o2c 158 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 157) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_157
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 158 - ((-979727/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_158).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_159 : ((7216973/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 159, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 159, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 158, cos813o2c k) + cos813o2c 159 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 158) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_158
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 159 - ((930433/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_159).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_160 : ((2773413/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 160, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 160, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 159, cos813o2c k) + cos813o2c 160 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 159) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_159
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 160 - ((-566781/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_160).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_161 : ((1732583/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 161, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 161, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 160, cos813o2c k) + cos813o2c 161 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 160) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_160
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 161 - ((-6301/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_161).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_162 : ((1806299/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 162, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 162, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 161, cos813o2c k) + cos813o2c 162 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 161) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_161
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 162 - ((147457/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_162).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_163 : ((13494931/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 163, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 163, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 162, cos813o2c k) + cos813o2c 163 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 162) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_162
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 163 - ((-955361/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_163).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_164 : ((577293/40000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 164, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 164, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 163, cos813o2c k) + cos813o2c 164 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 163) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_163
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 164 - ((468747/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_164).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_165 : ((1739239/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 165, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 165, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 164, cos813o2c k) + cos813o2c 165 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 164) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_164
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 165 - ((-518313/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_165).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_166 : ((6886877/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 166, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 166, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 165, cos813o2c k) + cos813o2c 166 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 165) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_165
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 166 - ((-70029/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_166).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_167 : ((45371/3125 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 167, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 167, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 166, cos813o2c k) + cos813o2c 167 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 166) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_166
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 167 - ((372533/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_167).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_168 : ((13518739/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 168, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 168, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 167, cos813o2c k) + cos813o2c 168 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 167) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_167
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 168 - ((-999881/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_168).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_169 : ((14274597/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 169, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 169, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 168, cos813o2c k) + cos813o2c 169 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 168) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_168
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 169 - ((377979/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_169).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_170 : ((1416099/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 170, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 170, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 169, cos813o2c k) + cos813o2c 170 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 169) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_169
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 170 - ((-113507/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_170).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_171 : ((3390187/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 171, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 171, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 170, cos813o2c k) + cos813o2c 171 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 170) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_170
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 171 - ((-300071/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_171).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_172 : ((7274269/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 172, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 172, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 171, cos813o2c k) + cos813o2c 172 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 171) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_171
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 172 - ((98789/100000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_172).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_173 : ((13739989/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 173, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 173, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 172, cos813o2c k) + cos813o2c 173 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 172) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_172
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 173 - ((-808449/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_173).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_174 : ((6941133/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 174, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 174, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 173, cos813o2c k) + cos813o2c 174 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 173) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_173
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 174 - ((142377/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_174).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_175 : ((580101/40000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 175, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 175, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 174, cos813o2c k) + cos813o2c 175 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 174) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_174
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 175 - ((620359/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_175).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_176 : ((1350533/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 176, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 176, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 175, cos813o2c k) + cos813o2c 176 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 175) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_175
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 176 - ((-199419/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_176).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_177 : ((7114273/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 177, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 177, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 176, cos813o2c k) + cos813o2c 177 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 176) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_176
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 177 - ((180829/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_177).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_178 : ((7135647/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 178, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 178, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 177, cos813o2c k) + cos813o2c 178 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 177) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_177
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 178 - ((1339/31250 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_178).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_179 : ((6741731/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 179, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 179, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 178, cos813o2c k) + cos813o2c 179 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 178) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_178
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 179 - ((-196933/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_179).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_180 : ((14460699/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 180, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 180, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 179, cos813o2c k) + cos813o2c 180 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 179) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_179
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 180 - ((977337/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_180).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_181 : ((2801901/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 181, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 181, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 180, cos813o2c k) + cos813o2c 181 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 180) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_180
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 181 - ((-225547/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_181).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_182 : ((3397237/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 182, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 182, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 181, cos813o2c k) + cos813o2c 182 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 181) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_181
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 182 - ((-420457/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_182).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_183 : ((14564159/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 183, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 183, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 182, cos813o2c k) + cos813o2c 183 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 182) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_182
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 183 - ((975311/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_183).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_184 : ((13801579/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 184, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 184, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 183, cos813o2c k) + cos813o2c 184 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 183) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_183
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 184 - ((-9531/12500 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_184).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_185 : ((2746071/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 185, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 185, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 184, cos813o2c k) + cos813o2c 185 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 184) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_184
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 185 - ((-17781/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_185).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_186 : ((227861/15625 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 186, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 186, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 185, cos813o2c k) + cos813o2c 186 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 185) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_185
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 186 - ((852849/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_186).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_187 : ((13666907/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 187, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 187, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 186, cos813o2c k) + cos813o2c 187 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 186) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_186
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 187 - ((-916097/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_187).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_188 : ((1385039/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 188, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 188, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 187, cos813o2c k) + cos813o2c 188 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 187) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_187
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 188 - ((183583/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_188).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_189 : ((910497/62500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 189, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 189, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 188, cos813o2c k) + cos813o2c 189 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 188) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_188
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 189 - ((358831/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_189).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_190 : ((424791/31250 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 190, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 190, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 189, cos813o2c k) + cos813o2c 190 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 189) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_189
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 190 - ((-48727/50000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_190).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_191 : ((13923821/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 191, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 191, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 190, cos813o2c k) + cos813o2c 191 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 190) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_190
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 191 - ((330609/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_191).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_192 : ((7277011/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 192, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 192, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 191, cos813o2c k) + cos813o2c 192 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 191) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_191
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 192 - ((630301/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_192).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_193 : ((13563853/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 193, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 193, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 192, cos813o2c k) + cos813o2c 193 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 192) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_192
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 193 - ((-990069/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_193).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_194 : ((2788593/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 194, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 194, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 193, cos813o2c k) + cos813o2c 194 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 193) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_193
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 194 - ((94803/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_194).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_195 : ((1819761/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 195, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 195, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 194, cos813o2c k) + cos813o2c 195 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 194) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_194
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 195 - ((615223/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_195).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_196 : ((271397/20000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 196, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 196, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 195, cos813o2c k) + cos813o2c 196 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 195) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_195
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 196 - ((-494069/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_196).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_197 : ((6953383/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 197, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 197, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 196, cos813o2c k) + cos813o2c 197 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 196) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_196
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 197 - ((42127/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_197).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_198 : ((1458067/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 198, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 198, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 197, cos813o2c k) + cos813o2c 198 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 197) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_197
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 198 - ((168501/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_198).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_199 : ((6807419/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 199, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 199, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 198, cos813o2c k) + cos813o2c 199 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 198) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_198
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 199 - ((-241433/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_199).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_200 : ((345439/25000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 200, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 200, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 199, cos813o2c k) + cos813o2c 200 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 199) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_199
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 200 - ((101411/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_200).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_201 : ((14606899/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 201, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 201, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 200, cos813o2c k) + cos813o2c 201 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 200) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_200
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 201 - ((789439/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_201).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_202 : ((171403/12500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 202, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 202, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 201, cos813o2c k) + cos813o2c 202 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 201) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_201
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 202 - ((-894559/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_202).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_203 : ((13685413/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 203, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 203, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 202, cos813o2c k) + cos813o2c 203 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 202) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_202
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 203 - ((-26727/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_203).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_204 : ((14606369/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 204, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 204, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 203, cos813o2c k) + cos813o2c 204 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 203) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_203
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 204 - ((28783/31250 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_204).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_205 : ((13877171/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 205, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 205, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 204, cos813o2c k) + cos813o2c 205 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 204) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_204
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 205 - ((-364549/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_205).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_206 : ((6768741/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 206, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 206, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 205, cos813o2c k) + cos813o2c 206 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 205) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_205
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 206 - ((-339589/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_206).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_207 : ((14536069/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 207, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 207, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 206, cos813o2c k) + cos813o2c 207 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 206) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_206
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 207 - ((998687/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_207).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_208 : ((14110491/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 208, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 208, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 207, cos813o2c k) + cos813o2c 208 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 207) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_207
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 208 - ((-212739/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_208).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_209 : ((3356741/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 209, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 209, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 208, cos813o2c k) + cos813o2c 209 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 208) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_208
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 209 - ((-683427/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_209).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_210 : ((287089/20000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 210, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 210, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 209, cos813o2c k) + cos813o2c 210 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 209) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_209
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 210 - ((463793/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_210).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_211 : ((14376923/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 211, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 211, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 210, cos813o2c k) + cos813o2c 211 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 210) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_210
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 211 - ((22573/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_211).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_212 : ((13430329/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 212, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 212, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 211, cos813o2c k) + cos813o2c 212 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 211) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_211
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 212 - ((-473247/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_212).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_213 : ((2810361/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 213, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 213, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 212, cos813o2c k) + cos813o2c 213 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 212) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_212
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 213 - ((77697/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_213).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_214 : ((3647167/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 214, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 214, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 213, cos813o2c k) + cos813o2c 214 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 213) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_213
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 214 - ((536963/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_214).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_215 : ((6808917/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 215, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 215, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 214, cos813o2c k) + cos813o2c 215 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 214) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_214
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 215 - ((-485367/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_215).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_216 : ((13690669/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 216, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 216, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 215, cos813o2c k) + cos813o2c 216 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 215) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_215
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 216 - ((14587/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_216).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_217 : ((14619313/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 217, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 217, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 216, cos813o2c k) + cos813o2c 217 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 216) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_216
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 217 - ((116093/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_217).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_218 : ((3498003/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 218, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 218, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 217, cos813o2c k) + cos813o2c 218 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 217) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_217
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 218 - ((-627201/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_218).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_219 : ((13424623/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 219, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 219, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 218, cos813o2c k) + cos813o2c 219 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 218) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_218
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 219 - ((-567289/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_219).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_220 : ((898319/62500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 220, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 220, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 219, cos813o2c k) + cos813o2c 220 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 219) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_219
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 220 - ((948581/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_220).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_221 : ((2884459/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 221, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 221, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 220, cos813o2c k) + cos813o2c 221 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 220) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_220
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 221 - ((49291/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_221).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_222 : ((2689047/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 222, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 222, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 221, cos813o2c k) + cos813o2c 222 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 221) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_221
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 222 - ((-3053/3125 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_222).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_223 : ((694957/50000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 223, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 223, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 222, cos813o2c k) + cos813o2c 223 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 222) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_222
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 223 - ((90801/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_223).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_224 : ((3662833/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 224, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 224, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 223, cos813o2c k) + cos813o2c 224 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 223) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_223
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 224 - ((188073/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_224).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_225 : ((13832511/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 225, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 225, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 224, cos813o2c k) + cos813o2c 225 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 224) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_224
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 225 - ((-818721/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_225).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_226 : ((2692341/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 226, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 226, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 225, cos813o2c k) + cos813o2c 226 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 225) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_225
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 226 - ((-185353/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_226).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_227 : ((2889897/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 227, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 227, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 226, cos813o2c k) + cos813o2c 227 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 226) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_226
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 227 - ((24697/25000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_227).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_228 : ((7194627/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 228, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 228, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 227, cos813o2c k) + cos813o2c 228 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 227) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_227
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 228 - ((-60131/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_228).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_229 : ((1678119/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 229, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 229, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 228, cos813o2c k) + cos813o2c 229 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 228) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_228
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 229 - ((-482101/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_229).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_230 : ((13876689/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 230, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 230, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 229, cos813o2c k) + cos813o2c 230 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 229) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_229
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 230 - ((451837/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_230).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_231 : ((14665607/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 231, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 231, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 230, cos813o2c k) + cos813o2c 231 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 230) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_230
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 231 - ((394509/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_231).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_232 : ((13916403/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 232, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 232, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 231, cos813o2c k) + cos813o2c 232 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 231) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_231
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 232 - ((-46819/62500 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_232).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_233 : ((6698307/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 233, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 233, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 232, cos813o2c k) + cos813o2c 233 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 232) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_232
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 233 - ((-519689/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_233).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_234 : ((358163/25000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 234, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 234, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 233, cos813o2c k) + cos813o2c 234 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 233) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_233
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 234 - ((465003/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_234).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_235 : ((14538481/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 235, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 235, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 234, cos813o2c k) + cos813o2c 235 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 234) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_234
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 235 - ((212061/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_235).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_236 : ((13540083/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 236, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 236, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 235, cos813o2c k) + cos813o2c 236 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 235) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_235
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 236 - ((-499149/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_236).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_237 : ((1703689/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 237, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 237, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 236, cos813o2c k) + cos813o2c 237 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 236) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_236
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 237 - ((89529/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_237).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_238 : ((7301491/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 238, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 238, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 237, cos813o2c k) + cos813o2c 238 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 237) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_237
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 238 - ((97357/100000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_238).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_239 : ((14246831/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 239, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 239, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 238, cos813o2c k) + cos813o2c 239 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 238) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_238
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 239 - ((-356051/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_239).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_240 : ((13364653/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 240, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 240, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 239, cos813o2c k) + cos813o2c 240 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 239) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_239
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 240 - ((-441039/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_240).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_241 : ((6968699/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 241, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 241, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 240, cos813o2c k) + cos813o2c 241 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 240) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_240
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 241 - ((114569/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_241).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_242 : ((1835939/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 242, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 242, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 241, cos813o2c k) + cos813o2c 242 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 241) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_241
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 242 - ((375107/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_242).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_243 : ((139509/10000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 243, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 243, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 242, cos813o2c k) + cos813o2c 243 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 242) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_242
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 243 - ((-11508/15625 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_243).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_244 : ((6675089/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 244, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 244, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 243, cos813o2c k) + cos813o2c 244 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 243) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_243
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 244 - ((-300311/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_244).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_245 : ((14201287/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 245, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 245, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 244, cos813o2c k) + cos813o2c 245 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 244) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_244
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 245 - ((851209/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_245).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_246 : ((2930367/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 246, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 246, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 245, cos813o2c k) + cos813o2c 246 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 245) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_245
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 246 - ((56331/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_246).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_247 : ((13726521/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 247, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 247, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 246, cos813o2c k) + cos813o2c 247 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 246) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_246
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 247 - ((-462607/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_247).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_248 : ((13414161/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 248, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 248, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 247, cos813o2c k) + cos813o2c 248 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 247) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_247
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 248 - ((-15613/50000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_248).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_249 : ((7191167/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 249, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 249, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 248, cos813o2c k) + cos813o2c 249 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 248) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_248
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 249 - ((968273/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_249).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_250 : ((14575093/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 250, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 250, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 249, cos813o2c k) + cos813o2c 250 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 249) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_249
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 250 - ((192859/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_250).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_251 : ((543403/40000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 251, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 251, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 250, cos813o2c k) + cos813o2c 251 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 250) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_250
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 251 - ((-494959/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_251).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_252 : ((1348849/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 252, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 252, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 251, cos813o2c k) + cos813o2c 252 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 251) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_251
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 252 - ((-19297/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_252).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_253 : ((905421/62500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 253, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 253, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 252, cos813o2c k) + cos813o2c 253 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 252) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_252
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 253 - ((499173/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_253).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_254 : ((14511397/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 254, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 254, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 253, cos813o2c k) + cos813o2c 254 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 253) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_253
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 254 - ((24761/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_254).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_255 : ((6755649/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 255, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 255, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 254, cos813o2c k) + cos813o2c 255 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 254) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_254
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 255 - ((-999999/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_255).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_256 : ((13533101/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 256, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 256, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 255, cos813o2c k) + cos813o2c 256 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 255) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_255
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 256 - ((21903/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_256).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_257 : ((14532357/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 257, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 257, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 256, cos813o2c k) + cos813o2c 257 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 256) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_256
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 257 - ((249839/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_257).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_258 : ((1811067/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 258, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 258, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 257, cos813o2c k) + cos813o2c 258 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 257) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_257
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 258 - ((-43721/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_258).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_259 : ((1348947/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 259, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 259, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 258, cos813o2c k) + cos813o2c 259 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 258) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_258
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 259 - ((-499483/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_259).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_260 : ((2706107/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 260, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 260, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 259, cos813o2c k) + cos813o2c 260 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 259) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_259
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 260 - ((8233/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_260).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_261 : ((14529959/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 261, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 261, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 260, cos813o2c k) + cos813o2c 261 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 260) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_260
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 261 - ((249881/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_261).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_262 : ((14515307/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 262, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 262, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 261, cos813o2c k) + cos813o2c 262 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 261) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_261
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 262 - ((-1819/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_262).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_263 : ((13515237/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 263, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 263, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 262, cos813o2c k) + cos813o2c 263 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 262) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_262
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 263 - ((-99997/100000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_263).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_264 : ((21567/1600 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 264, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 264, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 263, cos813o2c k) + cos813o2c 264 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 263) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_263
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 264 - ((-17881/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_264).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_265 : ((7238423/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 265, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 265, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 264, cos813o2c k) + cos813o2c 265 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 264) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_264
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 265 - ((997571/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_265).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_266 : ((7292977/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 266, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 266, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 265, cos813o2c k) + cos813o2c 266 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 265) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_265
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 266 - ((13651/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_266).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_267 : ((13597829/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 267, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 267, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 266, cos813o2c k) + cos813o2c 267 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 266) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_266
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 267 - ((-39521/40000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_267).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_268 : ((2678619/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 268, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 268, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 267, cos813o2c k) + cos813o2c 268 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 267) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_267
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 268 - ((-102317/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_268).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_269 : ((14358631/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 269, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 269, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 268, cos813o2c k) + cos813o2c 269 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 268) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_268
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 269 - ((241409/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_269).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_270 : ((458693/31250 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 270, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 270, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 269, cos813o2c k) + cos813o2c 270 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 269) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_269
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 270 - ((63929/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_270).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_271 : ((275089/20000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 271, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 271, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 270, cos813o2c k) + cos813o2c 271 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 270) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_270
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 271 - ((-461813/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_271).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_272 : ((13304197/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 272, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 272, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 271, cos813o2c k) + cos813o2c 272 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 271) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_271
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 272 - ((-450153/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_272).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_273 : ((2831741/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 273, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 273, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 272, cos813o2c k) + cos813o2c 273 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 272) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_272
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 273 - ((53413/62500 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_273).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_274 : ((14748129/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 274, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 274, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 273, cos813o2c k) + cos813o2c 274 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 273) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_273
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 274 - ((147381/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_274).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_275 : ((2799301/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 275, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 275, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 274, cos813o2c k) + cos813o2c 275 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 274) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_274
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 275 - ((-187881/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_275).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_276 : ((13268193/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 276, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 276, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 275, cos813o2c k) + cos813o2c 276 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 275) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_275
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 276 - ((-182053/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_276).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_277 : ((13876839/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 277, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 277, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 276, cos813o2c k) + cos813o2c 277 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 276) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_276
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 277 - ((304373/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_277).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_278 : ((14730023/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 278, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 278, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 277, cos813o2c k) + cos813o2c 278 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 277) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_277
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 278 - ((213321/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_278).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_279 : ((7153201/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 279, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 279, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 278, cos813o2c k) + cos813o2c 279 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 278) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_278
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 279 - ((-423521/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_279).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_280 : ((2671473/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 280, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 280, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 279, cos813o2c k) + cos813o2c 280 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 279) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_279
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 280 - ((-948937/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_280).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_281 : ((1694409/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 281, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 281, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 280, cos813o2c k) + cos813o2c 281 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 280) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_280
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 281 - ((198007/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_281).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_282 : ((14552539/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 282, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 282, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 281, cos813o2c k) + cos813o2c 282 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 281) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_281
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 282 - ((997367/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_282).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_283 : ((14611693/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 283, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 283, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 282, cos813o2c k) + cos813o2c 283 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 282) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_282
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 283 - ((29627/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_283).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_284 : ((6815389/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 284, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 284, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 283, cos813o2c k) + cos813o2c 284 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 283) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_283
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 284 - ((-196163/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_284).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_285 : ((13298901/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 285, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 285, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 284, cos813o2c k) + cos813o2c 285 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 284) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_284
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 285 - ((-331777/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_285).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_286 : ((14183413/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 286, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 286, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 285, cos813o2c k) + cos813o2c 286 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 285) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_285
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 286 - ((221153/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_286).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_287 : ((14778167/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 287, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 287, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 286, cos813o2c k) + cos813o2c 287 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 286) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_286
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 287 - ((297427/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_287).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_288 : ((14077063/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 288, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 288, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 287, cos813o2c k) + cos813o2c 288 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 287) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_287
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 288 - ((-175251/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_288).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_289 : ((66301/5000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 289, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 289, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 288, cos813o2c k) + cos813o2c 289 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 288) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_288
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 289 - ((-816763/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_289).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_290 : ((684681/50000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 290, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 290, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 289, cos813o2c k) + cos813o2c 290 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 289) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_289
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 290 - ((5419/12500 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_290).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_291 : ((14655429/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 291, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 291, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 290, cos813o2c k) + cos813o2c 291 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 290) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_290
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 291 - ((961909/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_291).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_292 : ((14554863/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 292, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 292, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 291, cos813o2c k) + cos813o2c 292 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 291) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_291
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 292 - ((-50233/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_292).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_293 : ((2711599/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 293, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 293, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 292, cos813o2c k) + cos813o2c 293 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 292) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_292
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 293 - ((-31149/31250 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_293).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_294 : ((33237/2500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 294, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 294, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 293, cos813o2c k) + cos813o2c 294 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 293) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_293
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 294 - ((-52619/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_294).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_295 : ((14192207/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 295, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 295, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 294, cos813o2c k) + cos813o2c 295 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 294) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_294
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 295 - ((897507/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_295).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_296 : ((231231/15625 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 296, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 296, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 295, cos813o2c k) + cos813o2c 296 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 295) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_295
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 296 - ((606677/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_296).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_297 : ((7069977/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 297, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 297, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 296, cos813o2c k) + cos813o2c 297 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 296) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_296
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 297 - ((-65873/100000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_297).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_298 : ((6634707/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 298, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 298, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 297, cos813o2c k) + cos813o2c 298 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 297) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_297
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 298 - ((-21761/25000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_298).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_299 : ((2714059/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 299, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 299, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 298, cos813o2c k) + cos813o2c 299 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 298) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_298
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 299 - ((300981/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_299).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_300 : ((14565949/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 300, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 300, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 299, cos813o2c k) + cos813o2c 300 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 299) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_299
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 300 - ((497877/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_300).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_301 : ((117531/8000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 301, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 301, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 300, cos813o2c k) + cos813o2c 301 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 300) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_300
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 301 - ((62763/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_301).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_302 : ((6875673/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 302, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 302, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 301, cos813o2c k) + cos813o2c 302 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 301) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_301
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 302 - ((-939929/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_302).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_303 : ((6603553/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 303, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 303, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 302, cos813o2c k) + cos813o2c 303 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 302) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_302
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 303 - ((-27207/50000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_303).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_304 : ((13898831/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 304, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 304, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 303, cos813o2c k) + cos813o2c 304 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 303) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_303
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 304 - ((27673/40000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_304).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_305 : ((2952493/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 305, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 305, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 304, cos813o2c k) + cos813o2c 305 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 304) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_304
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 305 - ((431867/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_305).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_306 : ((7239163/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 306, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 306, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 305, cos813o2c k) + cos813o2c 306 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 305) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_305
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 306 - ((-284039/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_306).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_307 : ((1347917/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 307, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 307, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 306, cos813o2c k) + cos813o2c 307 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 306) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_306
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 307 - ((-62441/62500 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_307).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_308 : ((13275107/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 308, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 308, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 307, cos813o2c k) + cos813o2c 308 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 307) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_307
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 308 - ((-203963/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_308).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_309 : ((14171711/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 309, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 309, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 308, cos813o2c k) + cos813o2c 309 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 308) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_308
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 309 - ((14011/15625 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_309).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_310 : ((14827927/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 310, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 310, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 309, cos813o2c k) + cos813o2c 310 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 309) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_309
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 310 - ((164079/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_310).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_311 : ((222949/15625 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 311, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 311, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 310, cos813o2c k) + cos813o2c 311 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 310) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_310
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 311 - ((-559091/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_311).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_312 : ((13321767/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 312, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 312, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 311, cos813o2c k) + cos813o2c 312 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 311) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_311
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 312 - ((-946869/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_312).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_313 : ((6689539/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 313, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 313, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 312, cos813o2c k) + cos813o2c 313 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 312) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_312
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 313 - ((57411/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_313).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_314 : ((1435559/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 314, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 314, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 313, cos813o2c k) + cos813o2c 314 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 313) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_313
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 314 - ((244153/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_314).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_315 : ((3707619/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 315, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 315, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 314, cos813o2c k) + cos813o2c 315 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 314) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_314
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 315 - ((237493/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_315).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_316 : ((220587/15625 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 316, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 316, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 315, cos813o2c k) + cos813o2c 316 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 315) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_315
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 316 - ((-89101/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_316).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_317 : ((165541/12500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 317, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 317, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 316, cos813o2c k) + cos813o2c 317 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 316) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_316
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 317 - ((-218547/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_317).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_318 : ((6729021/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 318, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 318, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 317, cos813o2c k) + cos813o2c 318 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 317) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_317
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 318 - ((107431/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_318).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_319 : ((3613727/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 319, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 319, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 318, cos813o2c k) + cos813o2c 319 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 318) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_318
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 319 - ((498483/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_319).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_320 : ((14822429/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 320, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 320, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 319, cos813o2c k) + cos813o2c 320 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 319) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_319
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 320 - ((367621/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_320).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_321 : ((2808811/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 321, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 321, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 320, cos813o2c k) + cos813o2c 321 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 320) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_320
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 321 - ((-389137/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_321).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_322 : ((2642103/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 322, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 322, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 321, cos813o2c k) + cos813o2c 322 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 321) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_321
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 322 - ((-5209/6250 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_322).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_323 : ((13482127/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 323, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 323, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 322, cos813o2c k) + cos813o2c 323 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 322) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_322
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 323 - ((8491/31250 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_323).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_324 : ((2896253/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 324, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 324, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 323, cos813o2c k) + cos813o2c 324 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 323) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_323
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 324 - ((499619/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_324).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_325 : ((14830797/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 325, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 325, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 324, cos813o2c k) + cos813o2c 325 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 324) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_324
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 325 - ((5463/15625 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_325).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_326 : ((7026287/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 326, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 326, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 325, cos813o2c k) + cos813o2c 326 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 325) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_325
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 326 - ((-778123/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_326).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_327 : ((13208369/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 327, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 327, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 326, cos813o2c k) + cos813o2c 327 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 326) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_326
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 327 - ((-168821/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_327).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_328 : ((13442429/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 328, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 328, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 327, cos813o2c k) + cos813o2c 328 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 327) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_327
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 328 - ((2927/12500 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_328).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_329 : ((14437627/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 329, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 329, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 328, cos813o2c k) + cos813o2c 329 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 328) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_328
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 329 - ((497649/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_329).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_330 : ((14858143/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 330, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 330, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 329, cos813o2c k) + cos813o2c 330 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 329) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_329
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 330 - ((52577/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_330).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_331 : ((14143603/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 331, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 331, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 330, cos813o2c k) + cos813o2c 331 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 330) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_330
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 331 - ((-17861/25000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_331).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_332 : ((13243611/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 332, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 332, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 331, cos813o2c k) + cos813o2c 332 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 331) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_331
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 332 - ((-224973/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_332).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_333 : ((3336589/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 333, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 333, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 332, cos813o2c k) + cos813o2c 333 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 332) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_332
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 333 - ((20569/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_333).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_334 : ((2863089/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 334, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 334, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 333, cos813o2c k) + cos813o2c 334 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 333) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_333
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 334 - ((969189/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_334).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_335 : ((465113/31250 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 335, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 335, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 334, cos813o2c k) + cos813o2c 335 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 334) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_334
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 335 - ((568271/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_335).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_336 : ((14312937/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 336, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 336, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 335, cos813o2c k) + cos813o2c 336 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 335) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_335
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 336 - ((-570579/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_336).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_337 : ((13342567/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 337, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 337, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 336, cos813o2c k) + cos813o2c 337 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 336) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_336
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 337 - ((-97027/100000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_337).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_338 : ((6610421/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 338, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 338, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 337, cos813o2c k) + cos813o2c 338 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 337) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_337
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 338 - ((-973/8000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_338).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_339 : ((7051113/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 339, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 339, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 338, cos813o2c k) + cos813o2c 339 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 338) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_338
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 339 - ((220371/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_339).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_340 : ((1857923/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 340, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 340, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 339, cos813o2c k) + cos813o2c 340 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 339) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_339
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 340 - ((380629/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_340).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_341 : ((2908121/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 341, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 341, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 340, cos813o2c k) + cos813o2c 341 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 340) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_340
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 341 - ((-322679/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_341).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_342 : ((13541851/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 342, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 342, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 341, cos813o2c k) + cos813o2c 342 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 341) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_341
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 342 - ((-499327/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_342).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_343 : ((3279899/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 343, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 343, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 342, cos813o2c k) + cos813o2c 343 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 342) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_342
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 343 - ((-84431/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_343).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_344 : ((13799363/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 344, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 344, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 343, cos813o2c k) + cos813o2c 344 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 343) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_343
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 344 - ((679867/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_344).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_345 : ((3684073/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 345, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 345, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 344, cos813o2c k) + cos813o2c 345 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 344) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_344
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 345 - ((937029/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_345).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_346 : ((7386837/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 346, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 346, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 345, cos813o2c k) + cos813o2c 346 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 345) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_345
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 346 - ((18741/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_346).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_347 : ((6933379/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 347, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 347, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 346, cos813o2c k) + cos813o2c 347 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 346) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_346
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 347 - ((-14169/15625 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_347).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_348 : ((13124597/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 348, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 348, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 347, cos813o2c k) + cos813o2c 348 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 347) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_347
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 348 - ((-742061/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_348).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_349 : ((3362209/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 349, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 349, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 348, cos813o2c k) + cos813o2c 349 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 348) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_348
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 349 - ((324339/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_349).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_350 : ((7222871/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 350, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 350, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 349, cos813o2c k) + cos813o2c 350 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 349) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_349
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 350 - ((498503/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_350).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_351 : ((14914871/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 351, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 351, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 350, cos813o2c k) + cos813o2c 351 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 350) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_350
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 351 - ((469229/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_351).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_352 : ((14295327/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 352, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 352, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 351, cos813o2c k) + cos813o2c 352 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 351) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_351
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 352 - ((-154861/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_352).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_353 : ((13326423/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 353, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 353, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 352, cos813o2c k) + cos813o2c 353 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 352) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_352
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 353 - ((-242201/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_353).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_354 : ((13156737/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 354, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 354, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 353, cos813o2c k) + cos813o2c 354 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 353) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_353
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 354 - ((-84793/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_354).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_355 : ((13985037/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 355, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 355, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 354, cos813o2c k) + cos813o2c 355 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 354) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_354
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 355 - ((2071/2500 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_355).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_356 : ((14838019/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 356, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 356, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 355, cos813o2c k) + cos813o2c 356 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 355) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_355
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 356 - ((426541/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_356).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_357 : ((7359913/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 357, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 357, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 356, cos813o2c k) + cos813o2c 357 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 356) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_356
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 357 - ((-118093/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_357).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_358 : ((13769043/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 358, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 358, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 357, cos813o2c k) + cos813o2c 358 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 357) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_357
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 358 - ((-950683/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_358).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_359 : ((2617129/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 359, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 359, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 358, cos813o2c k) + cos813o2c 359 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 358) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_358
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 359 - ((-341649/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_359).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_360 : ((13455063/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 360, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 360, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 359, cos813o2c k) + cos813o2c 360 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 359) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_359
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 360 - ((184759/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_360).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_361 : ((1445287/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 361, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 361, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 360, cos813o2c k) + cos813o2c 361 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 360) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_360
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 361 - ((997907/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_361).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_362 : ((14941829/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 362, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 362, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 361, cos813o2c k) + cos813o2c 362 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 361) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_361
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 362 - ((489059/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_362).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_363 : ((7184283/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 363, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 363, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 362, cos813o2c k) + cos813o2c 363 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 362) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_362
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 363 - ((-573163/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_363).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_364 : ((6690449/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 364, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 364, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 363, cos813o2c k) + cos813o2c 364 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 363) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_363
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 364 - ((-61723/62500 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_364).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_365 : ((13087459/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 365, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 365, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 364, cos813o2c k) + cos813o2c 365 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 364) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_364
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 365 - ((-293339/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_365).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_366 : ((6907359/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 366, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 366, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 365, cos813o2c k) + cos813o2c 366 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 365) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_365
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 366 - ((727359/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_366).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_367 : ((590121/40000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 367, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 367, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 366, cos813o2c k) + cos813o2c 367 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 366) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_366
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 367 - ((938407/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_367).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_368 : ((3716139/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 368, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 368, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 367, cos813o2c k) + cos813o2c 368 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 367) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_367
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 368 - ((111631/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_368).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_369 : ((7013871/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 369, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 369, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 368, cos813o2c k) + cos813o2c 369 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 368) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_368
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 369 - ((-418357/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_369).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_370 : ((6580063/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 370, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 370, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 369, cos813o2c k) + cos813o2c 370 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 369) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_369
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 370 - ((-216879/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_370).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_371 : ((6603483/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 371, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 371, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 370, cos813o2c k) + cos813o2c 371 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 370) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_370
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 371 - ((2347/50000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_371).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_372 : ((14115989/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 372, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 372, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 371, cos813o2c k) + cos813o2c 372 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 371) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_371
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 372 - ((909123/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_372).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_373 : ((7452429/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 373, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 373, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 372, cos813o2c k) + cos813o2c 373 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 372) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_372
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 373 - ((788969/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_373).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_374 : ((7363261/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 374, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 374, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 373, cos813o2c k) + cos813o2c 374 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 373) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_373
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 374 - ((-44559/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_374).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_375 : ((6886457/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 375, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 375, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 374, cos813o2c k) + cos813o2c 375 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 374) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_374
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 375 - ((-238377/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_375).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_376 : ((1305939/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 376, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 376, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 375, cos813o2c k) + cos813o2c 376 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 375) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_375
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 376 - ((-44589/62500 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_376).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_377 : ((1667591/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 377, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 377, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 376, cos813o2c k) + cos813o2c 377 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 376) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_376
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 377 - ((140719/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_377).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_378 : ((3579733/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 378, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 378, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 377, cos813o2c k) + cos813o2c 378 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 377) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_377
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 378 - ((15286/15625 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_378).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_379 : ((14967223/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 379, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 379, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 378, cos813o2c k) + cos813o2c 379 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 378) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_378
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 379 - ((648391/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_379).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_380 : ((7304779/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 380, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 380, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 379, cos813o2c k) + cos813o2c 380 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 379) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_379
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 380 - ((-71513/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_380).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_381 : ((13618803/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 381, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 381, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 380, cos813o2c k) + cos813o2c 381 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 380) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_380
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 381 - ((-198131/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_381).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_382 : ((6509931/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 382, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 382, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 381, cos813o2c k) + cos813o2c 382 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 381) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_381
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 382 - ((-598841/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_382).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_383 : ((4297/320 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 383, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 383, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 382, cos813o2c k) + cos813o2c 383 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 382) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_382
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 383 - ((408363/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_383).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_384 : ((2884793/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 384, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 384, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 383, cos813o2c k) + cos813o2c 384 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 383) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_383
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 384 - ((49797/50000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_384).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_385 : ((3747893/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 385, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 385, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 384, cos813o2c k) + cos813o2c 385 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 384) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_384
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 385 - ((567707/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_385).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_386 : ((14555837/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 386, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 386, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 385, cos813o2c k) + cos813o2c 386 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 385) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_385
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 386 - ((-87127/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_386).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_387 : ((1355807/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 387, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 387, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 386, cos813o2c k) + cos813o2c 387 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 386) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_386
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 387 - ((-997667/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_387).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_388 : ((13001561/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 388, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 388, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 387, cos813o2c k) + cos813o2c 388 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 387) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_387
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 388 - ((-556409/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_388).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_389 : ((13442067/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 389, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 389, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 388, cos813o2c k) + cos813o2c 389 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 388) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_388
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 389 - ((220303/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_389).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_390 : ((451233/31250 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 390, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 390, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 389, cos813o2c k) + cos813o2c 390 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 389) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_389
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 390 - ((997489/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_390).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_391 : ((15004581/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 391, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 391, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 390, cos813o2c k) + cos813o2c 391 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 390) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_390
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 391 - ((22609/40000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_391).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_392 : ((14580699/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 392, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 392, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 391, cos813o2c k) + cos813o2c 392 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 391) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_391
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 392 - ((-211891/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_392).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_393 : ((3396337/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 393, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 393, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 392, cos813o2c k) + cos813o2c 393 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 392) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_392
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 393 - ((-995251/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_393).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_394 : ((1623983/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 394, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 394, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 393, cos813o2c k) + cos813o2c 394 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 393) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_393
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 394 - ((-74173/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_394).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_395 : ((13376701/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 395, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 395, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 394, cos813o2c k) + cos813o2c 395 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 394) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_394
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 395 - ((384937/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_395).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_396 : ((2873139/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 396, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 396, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 395, cos813o2c k) + cos813o2c 396 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 395) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_395
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 396 - ((494547/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_396).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_397 : ((1500477/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 397, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 397, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 396, cos813o2c k) + cos813o2c 397 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 396) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_396
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 397 - ((25567/40000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_397).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_398 : ((7340669/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 398, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 398, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 397, cos813o2c k) + cos813o2c 398 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 397) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_397
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 398 - ((-80833/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_398).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_399 : ((214151/15625 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 399, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 399, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 398, cos813o2c k) + cos813o2c 399 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 398) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_398
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 399 - ((-487787/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_399).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_400 : ((13006017/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 400, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 400, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 399, cos813o2c k) + cos813o2c 400 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 399) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_399
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 400 - ((-699547/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_400).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_401 : ((41387/3125 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 401, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 401, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 400, cos813o2c k) + cos813o2c 401 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 400) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_400
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 401 - ((237923/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_401).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_402 : ((14193559/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 402, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 402, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 401, cos813o2c k) + cos813o2c 402 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 401) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_401
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 402 - ((949819/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_402).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_403 : ((14963553/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 403, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 403, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 402, cos813o2c k) + cos813o2c 403 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 402) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_402
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 403 - ((385047/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_403).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_404 : ((2967073/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 404, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 404, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 403, cos813o2c k) + cos813o2c 404 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 403) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_403
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 404 - ((-16011/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_404).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_405 : ((13929411/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 405, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 405, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 404, cos813o2c k) + cos813o2c 405 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 404) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_404
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 405 - ((-452927/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_405).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_406 : ((3271189/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 406, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 406, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 405, cos813o2c k) + cos813o2c 406 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 405) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_405
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 406 - ((-168911/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_406).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_407 : ((13078913/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 407, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 407, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 406, cos813o2c k) + cos813o2c 407 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 406) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_406
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 407 - ((-5743/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_407).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_408 : ((1391583/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 408, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 408, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 407, cos813o2c k) + cos813o2c 408 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 407) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_407
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 408 - ((837017/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_408).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_409 : ((14830393/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 409, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 409, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 408, cos813o2c k) + cos813o2c 409 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 408) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_408
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 409 - ((914663/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_409).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_410 : ((2998317/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 410, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 410, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 409, cos813o2c k) + cos813o2c 410 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 409) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_409
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 410 - ((40323/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_410).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_411 : ((14254719/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 411, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 411, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 410, cos813o2c k) + cos813o2c 411 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 410) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_410
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 411 - ((-368383/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_411).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_412 : ((6642279/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 412, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 412, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 411, cos813o2c k) + cos813o2c 412 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 411) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_411
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 412 - ((-970061/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_412).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_413 : ((12950929/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 413, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 413, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 412, cos813o2c k) + cos813o2c 413 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 412) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_412
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 413 - ((-333529/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_413).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_414 : ((1693807/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 414, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 414, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 413, cos813o2c k) + cos813o2c 414 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 413) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_413
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 414 - ((599627/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_414).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_415 : ((7274477/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 415, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 415, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 414, cos813o2c k) + cos813o2c 415 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 414) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_414
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 415 - ((499299/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_415).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_416 : ((15062571/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 416, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 416, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 415, cos813o2c k) + cos813o2c 416 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 415) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_415
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 416 - ((513717/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_416).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_417 : ((7319853/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 417, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 417, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 416, cos813o2c k) + cos813o2c 417 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 416) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_416
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 417 - ((-84553/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_417).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_418 : ((13652483/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 418, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 418, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 417, cos813o2c k) + cos813o2c 418 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 417) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_417
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 418 - ((-987123/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_418).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_419 : ((810211/62500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 419, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 419, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 418, cos813o2c k) + cos813o2c 419 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 418) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_418
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 419 - ((-689007/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_419).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_420 : ((13170657/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 420, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 420, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 419, cos813o2c k) + cos813o2c 420 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 419) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_419
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 420 - ((207381/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_420).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_421 : ((3523369/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 421, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 421, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 420, cos813o2c k) + cos813o2c 421 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 420) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_420
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 421 - ((922919/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_421).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_422 : ((7467849/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 422, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 422, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 421, cos813o2c k) + cos813o2c 422 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 421) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_421
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 422 - ((421161/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_422).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_423 : ((748753/50000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 423, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 423, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 422, cos813o2c k) + cos813o2c 423 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 422) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_422
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 423 - ((19731/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_423).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_424 : ((7089559/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 424, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 424, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 423, cos813o2c k) + cos813o2c 424 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 423) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_423
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 424 - ((-397921/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_424).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_425 : ((1653229/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 425, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 425, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 424, cos813o2c k) + cos813o2c 425 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 424) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_424
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 425 - ((-476593/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_425).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_426 : ((6461171/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 426, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 426, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 425, cos813o2c k) + cos813o2c 426 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 425) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_425
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 426 - ((-30339/100000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_426).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_427 : ((6761669/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 427, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 427, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 426, cos813o2c k) + cos813o2c 427 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 426) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_426
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 427 - ((75137/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_427).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_428 : ((907683/62500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 428, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 428, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 427, cos813o2c k) + cos813o2c 428 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 427) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_427
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 428 - ((99969/100000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_428).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_429 : ((7542573/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 429, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 429, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 428, cos813o2c k) + cos813o2c 429 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 428) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_428
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 429 - ((281159/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_429).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_430 : ((14742837/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 430, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 430, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 429, cos813o2c k) + cos813o2c 430 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 429) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_429
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 430 - ((-342209/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_430).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_431 : ((6890471/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 431, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 431, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 430, cos813o2c k) + cos813o2c 431 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 430) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_430
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 431 - ((-192359/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_431).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_432 : ((12993773/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 432, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 432, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 431, cos813o2c k) + cos813o2c 432 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 431) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_431
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 432 - ((-787069/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_432).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_433 : ((3256883/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 433, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 433, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 432, cos813o2c k) + cos813o2c 433 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 432) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_432
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 433 - ((33859/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_433).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_434 : ((1385321/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 434, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 434, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 433, cos813o2c k) + cos813o2c 434 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 433) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_433
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 434 - ((412889/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_434).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_435 : ((7398539/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 435, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 435, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 434, cos813o2c k) + cos813o2c 435 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 434) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_434
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 435 - ((29499/31250 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_435).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_436 : ((15093499/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 436, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 436, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 435, cos813o2c k) + cos813o2c 436 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 435) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_435
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 436 - ((296521/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_436).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_437 : ((1450409/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 437, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 437, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 436, cos813o2c k) + cos813o2c 437 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 436) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_436
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 437 - ((-589309/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_437).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_438 : ((2700811/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 438, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 438, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 437, cos813o2c k) + cos813o2c 438 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 437) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_437
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 438 - ((-199987/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_438).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_439 : ((6447323/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 439, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 439, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 438, cos813o2c k) + cos813o2c 439 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 438) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_438
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 439 - ((-609309/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_439).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_440 : ((13161009/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 440, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 440, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 439, cos813o2c k) + cos813o2c 440 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 439) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_439
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 440 - ((266463/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_440).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_441 : ((1409021/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 441, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 441, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 440, cos813o2c k) + cos813o2c 441 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 440) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_440
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 441 - ((929301/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_441).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_442 : ((46708/3125 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 442, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 442, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 441, cos813o2c k) + cos813o2c 442 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 441) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_441
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 442 - ((17129/20000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_442).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_443 : ((1881993/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 443, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 443, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 442, cos813o2c k) + cos813o2c 443 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 442) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_442
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 443 - ((27371/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_443).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_444 : ((14333717/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 444, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 444, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 443, cos813o2c k) + cos813o2c 444 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 443) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_443
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 444 - ((-722127/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_444).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_445 : ((13344933/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 445, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 445, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 444, cos813o2c k) + cos813o2c 445 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 444) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_444
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 445 - ((-247171/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_445).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_446 : ((12858623/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 446, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 446, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 445, cos813o2c k) + cos813o2c 446 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 445) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_445
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 446 - ((-48621/100000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_446).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_447 : ((13250381/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 447, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 447, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 446, cos813o2c k) + cos813o2c 447 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 446) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_446
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 447 - ((195929/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_447).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_448 : ((7108369/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 448, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 448, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 447, cos813o2c k) + cos813o2c 448 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 447) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_447
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 448 - ((966457/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_448).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_449 : ((750739/50000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 449, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 449, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 448, cos813o2c k) + cos813o2c 449 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 448) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_448
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 449 - ((399071/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_449).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_450 : ((7517271/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 450, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 450, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 449, cos813o2c k) + cos813o2c 450 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 449) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_449
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 450 - ((9931/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_450).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_451 : ((7131061/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 451, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 451, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 450, cos813o2c k) + cos813o2c 451 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 450) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_450
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 451 - ((-4827/6250 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_451).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_452 : ((13284411/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 452, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 452, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 451, cos813o2c k) + cos813o2c 452 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 451) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_451
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 452 - ((-977611/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_452).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_453 : ((12839981/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 453, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 453, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 452, cos813o2c k) + cos813o2c 453 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 452) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_452
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 453 - ((-44433/100000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_453).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_454 : ((13262113/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 454, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 454, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 453, cos813o2c k) + cos813o2c 454 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 453) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_453
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 454 - ((52779/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_454).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_455 : ((355831/25000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 455, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 455, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 454, cos813o2c k) + cos813o2c 455 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 454) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_454
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 455 - ((971227/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_455).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_456 : ((3005607/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 456, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 456, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 455, cos813o2c k) + cos813o2c 456 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 455) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_455
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 456 - ((158979/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_456).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_457 : ((1882041/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 457, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 457, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 456, cos813o2c k) + cos813o2c 457 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 456) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_456
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 457 - ((28393/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_457).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_458 : ((142983/10000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 458, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 458, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 457, cos813o2c k) + cos813o2c 458 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 457) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_457
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 458 - ((-94741/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_458).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_459 : ((332841/25000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 459, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 459, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 458, cos813o2c k) + cos813o2c 459 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 458) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_458
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 459 - ((-12307/12500 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_459).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_460 : ((3206293/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 460, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 460, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 459, cos813o2c k) + cos813o2c 460 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 459) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_459
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 460 - ((-30523/62500 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_460).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_461 : ((13189051/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 461, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 461, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 460, cos813o2c k) + cos813o2c 461 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 460) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_460
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 461 - ((363979/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_461).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_462 : ((1767373/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 462, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 462, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 461, cos813o2c k) + cos813o2c 462 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 461) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_461
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 462 - ((950033/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_462).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_463 : ((14985353/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 463, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 463, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 462, cos813o2c k) + cos813o2c 463 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 462) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_462
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 463 - ((846469/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_463).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_464 : ((15117161/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 464, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 464, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 463, cos813o2c k) + cos813o2c 464 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 463) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_463
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 464 - ((32977/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_464).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_465 : ((1805083/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 465, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 465, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 464, cos813o2c k) + cos813o2c 465 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 464) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_464
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 465 - ((-676397/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_465).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_466 : ((1344159/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 466, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 466, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 465, cos813o2c k) + cos813o2c 466 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 465) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_465
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 466 - ((-499487/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_466).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_467 : ((1604129/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 467, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 467, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 466, cos813o2c k) + cos813o2c 467 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 466) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_466
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 467 - ((-304229/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_467).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_468 : ((6523329/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 468, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 468, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 467, cos813o2c k) + cos813o2c 468 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 467) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_467
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 468 - ((106863/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_468).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_469 : ((2785991/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 469, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 469, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 468, cos813o2c k) + cos813o2c 469 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 468) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_468
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 469 - ((883397/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_469).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_470 : ((7429617/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 470, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 470, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 469, cos813o2c k) + cos813o2c 470 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 469) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_469
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 470 - ((929379/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_470).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_471 : ((3036399/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 471, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 471, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 470, cos813o2c k) + cos813o2c 471 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 470) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_470
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 471 - ((322861/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_471).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_472 : ((3668359/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 472, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 472, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 471, cos813o2c k) + cos813o2c 472 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 471) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_471
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 472 - ((-508459/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_472).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_473 : ((547559/40000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 473, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 473, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 472, cos813o2c k) + cos813o2c 473 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 472) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_472
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 473 - ((-984361/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_473).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_474 : ((1291221/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 474, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 474, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 473, cos813o2c k) + cos813o2c 474 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 473) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_473
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 474 - ((-155333/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_474).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_475 : ((12879461/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 475, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 475, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 474, cos813o2c k) + cos813o2c 475 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 474) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_474
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 475 - ((-32649/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_475).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_476 : ((850751/62500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 476, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 476, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 475, cos813o2c k) + cos813o2c 476 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 475) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_475
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 476 - ((146531/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_476).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_477 : ((14606461/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 477, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 477, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 476, cos813o2c k) + cos813o2c 477 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 476) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_476
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 477 - ((198909/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_477).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_478 : ((1518329/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 478, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 478, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 477, cos813o2c k) + cos813o2c 478 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 477) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_477
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 478 - ((576929/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_478).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_479 : ((2990159/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 479, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 479, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 478, cos813o2c k) + cos813o2c 479 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 478) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_478
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 479 - ((-46479/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_479).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_480 : ((14067639/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 480, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 480, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 479, cos813o2c k) + cos813o2c 480 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 479) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_479
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 480 - ((-55191/62500 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_480).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_481 : ((13130767/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 481, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 481, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 480, cos813o2c k) + cos813o2c 481 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 480) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_480
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 481 - ((-234193/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_481).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_482 : ((3192489/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 482, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 482, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 481, cos813o2c k) + cos813o2c 482 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 481) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_481
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 482 - ((-360711/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_482).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_483 : ((826613/62500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 483, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 483, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 482, cos813o2c k) + cos813o2c 483 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 482) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_482
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 483 - ((28497/62500 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_483).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_484 : ((14192969/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 484, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 484, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 483, cos813o2c k) + cos813o2c 484 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 483) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_483
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 484 - ((967261/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_484).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_485 : ((7514011/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 485, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 485, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 484, cos813o2c k) + cos813o2c 485 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 484) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_484
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 485 - ((835153/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_485).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_486 : ((15178451/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 486, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 486, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 485, cos813o2c k) + cos813o2c 486 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 485) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_485
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 486 - ((150529/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_486).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_487 : ((7273049/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 487, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 487, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 486, cos813o2c k) + cos813o2c 487 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 486) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_486
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 487 - ((-632253/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_487).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_488 : ((108379/8000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 488, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 488, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 487, cos813o2c k) + cos813o2c 488 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 487) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_487
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 488 - ((-998623/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_488).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_489 : ((6418047/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 489, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 489, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 488, cos813o2c k) + cos813o2c 489 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 488) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_488
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 489 - ((-711181/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_489).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_490 : ((12875247/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 490, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 490, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 489, cos813o2c k) + cos813o2c 490 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 489) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_489
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 490 - ((39253/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_490).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_491 : ((13638207/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 491, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 491, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 490, cos813o2c k) + cos813o2c 491 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 490) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_490
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 491 - ((38153/50000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_491).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_492 : ((14630391/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 492, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 492, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 491, cos813o2c k) + cos813o2c 492 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 491) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_491
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 492 - ((248071/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_492).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_493 : ((60849/4000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 493, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 493, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 492, cos813o2c k) + cos813o2c 493 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 492) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_492
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 493 - ((581959/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_493).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_494 : ((15010937/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 494, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 494, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 493, cos813o2c k) + cos813o2c 494 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 493) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_493
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 494 - ((-201213/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_494).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_495 : ((88477/6250 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 495, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 495, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 494, cos813o2c k) + cos813o2c 495 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 494) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_494
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 495 - ((-854517/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_495).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_496 : ((824599/62500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 496, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 496, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 495, cos813o2c k) + cos813o2c 496 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 495) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_495
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 496 - ((-240659/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_496).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_497 : ((636681/50000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 497, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 497, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 496, cos813o2c k) + cos813o2c 497 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 496) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_496
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 497 - ((-57483/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_497).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_498 : ((522651/40000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 498, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 498, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 497, cos813o2c k) + cos813o2c 498 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 497) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_497
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 498 - ((66551/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_498).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_499 : ((6990417/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 499, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 499, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 498, cos813o2c k) + cos813o2c 499 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 498) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_498
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 499 - ((914659/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_499).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum813o2_500 : ((1862837/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 500, cos813o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 500, cos813o2c k)
      = (∑ k ∈ Finset.Icc 11 499, cos813o2c k) + cos813o2c 500 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 499) (by norm_num) cos813o2c
    simpa using h
  have hprev := psum813o2_499
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos813o2c 500 - ((460981/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos813o2_br_500).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

set_option maxHeartbeats 6400000 in
set_option maxRecDepth 16384 in
theorem psum813o2_floor : ∀ j : ℕ, 11 ≤ j → j ≤ 500 →
    ((0 : ℚ) : ℝ) ≤ ∑ k ∈ Finset.Icc 11 j, cos813o2c k := by
  intro j hj1 hj2
  interval_cases j
  · exact le_trans (by norm_num) psum813o2_11
  · exact le_trans (by norm_num) psum813o2_12
  · exact le_trans (by norm_num) psum813o2_13
  · exact le_trans (by norm_num) psum813o2_14
  · exact le_trans (by norm_num) psum813o2_15
  · exact le_trans (by norm_num) psum813o2_16
  · exact le_trans (by norm_num) psum813o2_17
  · exact le_trans (by norm_num) psum813o2_18
  · exact le_trans (by norm_num) psum813o2_19
  · exact le_trans (by norm_num) psum813o2_20
  · exact le_trans (by norm_num) psum813o2_21
  · exact le_trans (by norm_num) psum813o2_22
  · exact le_trans (by norm_num) psum813o2_23
  · exact le_trans (by norm_num) psum813o2_24
  · exact le_trans (by norm_num) psum813o2_25
  · exact le_trans (by norm_num) psum813o2_26
  · exact le_trans (by norm_num) psum813o2_27
  · exact le_trans (by norm_num) psum813o2_28
  · exact le_trans (by norm_num) psum813o2_29
  · exact le_trans (by norm_num) psum813o2_30
  · exact le_trans (by norm_num) psum813o2_31
  · exact le_trans (by norm_num) psum813o2_32
  · exact le_trans (by norm_num) psum813o2_33
  · exact le_trans (by norm_num) psum813o2_34
  · exact le_trans (by norm_num) psum813o2_35
  · exact le_trans (by norm_num) psum813o2_36
  · exact le_trans (by norm_num) psum813o2_37
  · exact le_trans (by norm_num) psum813o2_38
  · exact le_trans (by norm_num) psum813o2_39
  · exact le_trans (by norm_num) psum813o2_40
  · exact le_trans (by norm_num) psum813o2_41
  · exact le_trans (by norm_num) psum813o2_42
  · exact le_trans (by norm_num) psum813o2_43
  · exact le_trans (by norm_num) psum813o2_44
  · exact le_trans (by norm_num) psum813o2_45
  · exact le_trans (by norm_num) psum813o2_46
  · exact le_trans (by norm_num) psum813o2_47
  · exact le_trans (by norm_num) psum813o2_48
  · exact le_trans (by norm_num) psum813o2_49
  · exact le_trans (by norm_num) psum813o2_50
  · exact le_trans (by norm_num) psum813o2_51
  · exact le_trans (by norm_num) psum813o2_52
  · exact le_trans (by norm_num) psum813o2_53
  · exact le_trans (by norm_num) psum813o2_54
  · exact le_trans (by norm_num) psum813o2_55
  · exact le_trans (by norm_num) psum813o2_56
  · exact le_trans (by norm_num) psum813o2_57
  · exact le_trans (by norm_num) psum813o2_58
  · exact le_trans (by norm_num) psum813o2_59
  · exact le_trans (by norm_num) psum813o2_60
  · exact le_trans (by norm_num) psum813o2_61
  · exact le_trans (by norm_num) psum813o2_62
  · exact le_trans (by norm_num) psum813o2_63
  · exact le_trans (by norm_num) psum813o2_64
  · exact le_trans (by norm_num) psum813o2_65
  · exact le_trans (by norm_num) psum813o2_66
  · exact le_trans (by norm_num) psum813o2_67
  · exact le_trans (by norm_num) psum813o2_68
  · exact le_trans (by norm_num) psum813o2_69
  · exact le_trans (by norm_num) psum813o2_70
  · exact le_trans (by norm_num) psum813o2_71
  · exact le_trans (by norm_num) psum813o2_72
  · exact le_trans (by norm_num) psum813o2_73
  · exact le_trans (by norm_num) psum813o2_74
  · exact le_trans (by norm_num) psum813o2_75
  · exact le_trans (by norm_num) psum813o2_76
  · exact le_trans (by norm_num) psum813o2_77
  · exact le_trans (by norm_num) psum813o2_78
  · exact le_trans (by norm_num) psum813o2_79
  · exact le_trans (by norm_num) psum813o2_80
  · exact le_trans (by norm_num) psum813o2_81
  · exact le_trans (by norm_num) psum813o2_82
  · exact le_trans (by norm_num) psum813o2_83
  · exact le_trans (by norm_num) psum813o2_84
  · exact le_trans (by norm_num) psum813o2_85
  · exact le_trans (by norm_num) psum813o2_86
  · exact le_trans (by norm_num) psum813o2_87
  · exact le_trans (by norm_num) psum813o2_88
  · exact le_trans (by norm_num) psum813o2_89
  · exact le_trans (by norm_num) psum813o2_90
  · exact le_trans (by norm_num) psum813o2_91
  · exact le_trans (by norm_num) psum813o2_92
  · exact le_trans (by norm_num) psum813o2_93
  · exact le_trans (by norm_num) psum813o2_94
  · exact le_trans (by norm_num) psum813o2_95
  · exact le_trans (by norm_num) psum813o2_96
  · exact le_trans (by norm_num) psum813o2_97
  · exact le_trans (by norm_num) psum813o2_98
  · exact le_trans (by norm_num) psum813o2_99
  · exact le_trans (by norm_num) psum813o2_100
  · exact le_trans (by norm_num) psum813o2_101
  · exact le_trans (by norm_num) psum813o2_102
  · exact le_trans (by norm_num) psum813o2_103
  · exact le_trans (by norm_num) psum813o2_104
  · exact le_trans (by norm_num) psum813o2_105
  · exact le_trans (by norm_num) psum813o2_106
  · exact le_trans (by norm_num) psum813o2_107
  · exact le_trans (by norm_num) psum813o2_108
  · exact le_trans (by norm_num) psum813o2_109
  · exact le_trans (by norm_num) psum813o2_110
  · exact le_trans (by norm_num) psum813o2_111
  · exact le_trans (by norm_num) psum813o2_112
  · exact le_trans (by norm_num) psum813o2_113
  · exact le_trans (by norm_num) psum813o2_114
  · exact le_trans (by norm_num) psum813o2_115
  · exact le_trans (by norm_num) psum813o2_116
  · exact le_trans (by norm_num) psum813o2_117
  · exact le_trans (by norm_num) psum813o2_118
  · exact le_trans (by norm_num) psum813o2_119
  · exact le_trans (by norm_num) psum813o2_120
  · exact le_trans (by norm_num) psum813o2_121
  · exact le_trans (by norm_num) psum813o2_122
  · exact le_trans (by norm_num) psum813o2_123
  · exact le_trans (by norm_num) psum813o2_124
  · exact le_trans (by norm_num) psum813o2_125
  · exact le_trans (by norm_num) psum813o2_126
  · exact le_trans (by norm_num) psum813o2_127
  · exact le_trans (by norm_num) psum813o2_128
  · exact le_trans (by norm_num) psum813o2_129
  · exact le_trans (by norm_num) psum813o2_130
  · exact le_trans (by norm_num) psum813o2_131
  · exact le_trans (by norm_num) psum813o2_132
  · exact le_trans (by norm_num) psum813o2_133
  · exact le_trans (by norm_num) psum813o2_134
  · exact le_trans (by norm_num) psum813o2_135
  · exact le_trans (by norm_num) psum813o2_136
  · exact le_trans (by norm_num) psum813o2_137
  · exact le_trans (by norm_num) psum813o2_138
  · exact le_trans (by norm_num) psum813o2_139
  · exact le_trans (by norm_num) psum813o2_140
  · exact le_trans (by norm_num) psum813o2_141
  · exact le_trans (by norm_num) psum813o2_142
  · exact le_trans (by norm_num) psum813o2_143
  · exact le_trans (by norm_num) psum813o2_144
  · exact le_trans (by norm_num) psum813o2_145
  · exact le_trans (by norm_num) psum813o2_146
  · exact le_trans (by norm_num) psum813o2_147
  · exact le_trans (by norm_num) psum813o2_148
  · exact le_trans (by norm_num) psum813o2_149
  · exact le_trans (by norm_num) psum813o2_150
  · exact le_trans (by norm_num) psum813o2_151
  · exact le_trans (by norm_num) psum813o2_152
  · exact le_trans (by norm_num) psum813o2_153
  · exact le_trans (by norm_num) psum813o2_154
  · exact le_trans (by norm_num) psum813o2_155
  · exact le_trans (by norm_num) psum813o2_156
  · exact le_trans (by norm_num) psum813o2_157
  · exact le_trans (by norm_num) psum813o2_158
  · exact le_trans (by norm_num) psum813o2_159
  · exact le_trans (by norm_num) psum813o2_160
  · exact le_trans (by norm_num) psum813o2_161
  · exact le_trans (by norm_num) psum813o2_162
  · exact le_trans (by norm_num) psum813o2_163
  · exact le_trans (by norm_num) psum813o2_164
  · exact le_trans (by norm_num) psum813o2_165
  · exact le_trans (by norm_num) psum813o2_166
  · exact le_trans (by norm_num) psum813o2_167
  · exact le_trans (by norm_num) psum813o2_168
  · exact le_trans (by norm_num) psum813o2_169
  · exact le_trans (by norm_num) psum813o2_170
  · exact le_trans (by norm_num) psum813o2_171
  · exact le_trans (by norm_num) psum813o2_172
  · exact le_trans (by norm_num) psum813o2_173
  · exact le_trans (by norm_num) psum813o2_174
  · exact le_trans (by norm_num) psum813o2_175
  · exact le_trans (by norm_num) psum813o2_176
  · exact le_trans (by norm_num) psum813o2_177
  · exact le_trans (by norm_num) psum813o2_178
  · exact le_trans (by norm_num) psum813o2_179
  · exact le_trans (by norm_num) psum813o2_180
  · exact le_trans (by norm_num) psum813o2_181
  · exact le_trans (by norm_num) psum813o2_182
  · exact le_trans (by norm_num) psum813o2_183
  · exact le_trans (by norm_num) psum813o2_184
  · exact le_trans (by norm_num) psum813o2_185
  · exact le_trans (by norm_num) psum813o2_186
  · exact le_trans (by norm_num) psum813o2_187
  · exact le_trans (by norm_num) psum813o2_188
  · exact le_trans (by norm_num) psum813o2_189
  · exact le_trans (by norm_num) psum813o2_190
  · exact le_trans (by norm_num) psum813o2_191
  · exact le_trans (by norm_num) psum813o2_192
  · exact le_trans (by norm_num) psum813o2_193
  · exact le_trans (by norm_num) psum813o2_194
  · exact le_trans (by norm_num) psum813o2_195
  · exact le_trans (by norm_num) psum813o2_196
  · exact le_trans (by norm_num) psum813o2_197
  · exact le_trans (by norm_num) psum813o2_198
  · exact le_trans (by norm_num) psum813o2_199
  · exact le_trans (by norm_num) psum813o2_200
  · exact le_trans (by norm_num) psum813o2_201
  · exact le_trans (by norm_num) psum813o2_202
  · exact le_trans (by norm_num) psum813o2_203
  · exact le_trans (by norm_num) psum813o2_204
  · exact le_trans (by norm_num) psum813o2_205
  · exact le_trans (by norm_num) psum813o2_206
  · exact le_trans (by norm_num) psum813o2_207
  · exact le_trans (by norm_num) psum813o2_208
  · exact le_trans (by norm_num) psum813o2_209
  · exact le_trans (by norm_num) psum813o2_210
  · exact le_trans (by norm_num) psum813o2_211
  · exact le_trans (by norm_num) psum813o2_212
  · exact le_trans (by norm_num) psum813o2_213
  · exact le_trans (by norm_num) psum813o2_214
  · exact le_trans (by norm_num) psum813o2_215
  · exact le_trans (by norm_num) psum813o2_216
  · exact le_trans (by norm_num) psum813o2_217
  · exact le_trans (by norm_num) psum813o2_218
  · exact le_trans (by norm_num) psum813o2_219
  · exact le_trans (by norm_num) psum813o2_220
  · exact le_trans (by norm_num) psum813o2_221
  · exact le_trans (by norm_num) psum813o2_222
  · exact le_trans (by norm_num) psum813o2_223
  · exact le_trans (by norm_num) psum813o2_224
  · exact le_trans (by norm_num) psum813o2_225
  · exact le_trans (by norm_num) psum813o2_226
  · exact le_trans (by norm_num) psum813o2_227
  · exact le_trans (by norm_num) psum813o2_228
  · exact le_trans (by norm_num) psum813o2_229
  · exact le_trans (by norm_num) psum813o2_230
  · exact le_trans (by norm_num) psum813o2_231
  · exact le_trans (by norm_num) psum813o2_232
  · exact le_trans (by norm_num) psum813o2_233
  · exact le_trans (by norm_num) psum813o2_234
  · exact le_trans (by norm_num) psum813o2_235
  · exact le_trans (by norm_num) psum813o2_236
  · exact le_trans (by norm_num) psum813o2_237
  · exact le_trans (by norm_num) psum813o2_238
  · exact le_trans (by norm_num) psum813o2_239
  · exact le_trans (by norm_num) psum813o2_240
  · exact le_trans (by norm_num) psum813o2_241
  · exact le_trans (by norm_num) psum813o2_242
  · exact le_trans (by norm_num) psum813o2_243
  · exact le_trans (by norm_num) psum813o2_244
  · exact le_trans (by norm_num) psum813o2_245
  · exact le_trans (by norm_num) psum813o2_246
  · exact le_trans (by norm_num) psum813o2_247
  · exact le_trans (by norm_num) psum813o2_248
  · exact le_trans (by norm_num) psum813o2_249
  · exact le_trans (by norm_num) psum813o2_250
  · exact le_trans (by norm_num) psum813o2_251
  · exact le_trans (by norm_num) psum813o2_252
  · exact le_trans (by norm_num) psum813o2_253
  · exact le_trans (by norm_num) psum813o2_254
  · exact le_trans (by norm_num) psum813o2_255
  · exact le_trans (by norm_num) psum813o2_256
  · exact le_trans (by norm_num) psum813o2_257
  · exact le_trans (by norm_num) psum813o2_258
  · exact le_trans (by norm_num) psum813o2_259
  · exact le_trans (by norm_num) psum813o2_260
  · exact le_trans (by norm_num) psum813o2_261
  · exact le_trans (by norm_num) psum813o2_262
  · exact le_trans (by norm_num) psum813o2_263
  · exact le_trans (by norm_num) psum813o2_264
  · exact le_trans (by norm_num) psum813o2_265
  · exact le_trans (by norm_num) psum813o2_266
  · exact le_trans (by norm_num) psum813o2_267
  · exact le_trans (by norm_num) psum813o2_268
  · exact le_trans (by norm_num) psum813o2_269
  · exact le_trans (by norm_num) psum813o2_270
  · exact le_trans (by norm_num) psum813o2_271
  · exact le_trans (by norm_num) psum813o2_272
  · exact le_trans (by norm_num) psum813o2_273
  · exact le_trans (by norm_num) psum813o2_274
  · exact le_trans (by norm_num) psum813o2_275
  · exact le_trans (by norm_num) psum813o2_276
  · exact le_trans (by norm_num) psum813o2_277
  · exact le_trans (by norm_num) psum813o2_278
  · exact le_trans (by norm_num) psum813o2_279
  · exact le_trans (by norm_num) psum813o2_280
  · exact le_trans (by norm_num) psum813o2_281
  · exact le_trans (by norm_num) psum813o2_282
  · exact le_trans (by norm_num) psum813o2_283
  · exact le_trans (by norm_num) psum813o2_284
  · exact le_trans (by norm_num) psum813o2_285
  · exact le_trans (by norm_num) psum813o2_286
  · exact le_trans (by norm_num) psum813o2_287
  · exact le_trans (by norm_num) psum813o2_288
  · exact le_trans (by norm_num) psum813o2_289
  · exact le_trans (by norm_num) psum813o2_290
  · exact le_trans (by norm_num) psum813o2_291
  · exact le_trans (by norm_num) psum813o2_292
  · exact le_trans (by norm_num) psum813o2_293
  · exact le_trans (by norm_num) psum813o2_294
  · exact le_trans (by norm_num) psum813o2_295
  · exact le_trans (by norm_num) psum813o2_296
  · exact le_trans (by norm_num) psum813o2_297
  · exact le_trans (by norm_num) psum813o2_298
  · exact le_trans (by norm_num) psum813o2_299
  · exact le_trans (by norm_num) psum813o2_300
  · exact le_trans (by norm_num) psum813o2_301
  · exact le_trans (by norm_num) psum813o2_302
  · exact le_trans (by norm_num) psum813o2_303
  · exact le_trans (by norm_num) psum813o2_304
  · exact le_trans (by norm_num) psum813o2_305
  · exact le_trans (by norm_num) psum813o2_306
  · exact le_trans (by norm_num) psum813o2_307
  · exact le_trans (by norm_num) psum813o2_308
  · exact le_trans (by norm_num) psum813o2_309
  · exact le_trans (by norm_num) psum813o2_310
  · exact le_trans (by norm_num) psum813o2_311
  · exact le_trans (by norm_num) psum813o2_312
  · exact le_trans (by norm_num) psum813o2_313
  · exact le_trans (by norm_num) psum813o2_314
  · exact le_trans (by norm_num) psum813o2_315
  · exact le_trans (by norm_num) psum813o2_316
  · exact le_trans (by norm_num) psum813o2_317
  · exact le_trans (by norm_num) psum813o2_318
  · exact le_trans (by norm_num) psum813o2_319
  · exact le_trans (by norm_num) psum813o2_320
  · exact le_trans (by norm_num) psum813o2_321
  · exact le_trans (by norm_num) psum813o2_322
  · exact le_trans (by norm_num) psum813o2_323
  · exact le_trans (by norm_num) psum813o2_324
  · exact le_trans (by norm_num) psum813o2_325
  · exact le_trans (by norm_num) psum813o2_326
  · exact le_trans (by norm_num) psum813o2_327
  · exact le_trans (by norm_num) psum813o2_328
  · exact le_trans (by norm_num) psum813o2_329
  · exact le_trans (by norm_num) psum813o2_330
  · exact le_trans (by norm_num) psum813o2_331
  · exact le_trans (by norm_num) psum813o2_332
  · exact le_trans (by norm_num) psum813o2_333
  · exact le_trans (by norm_num) psum813o2_334
  · exact le_trans (by norm_num) psum813o2_335
  · exact le_trans (by norm_num) psum813o2_336
  · exact le_trans (by norm_num) psum813o2_337
  · exact le_trans (by norm_num) psum813o2_338
  · exact le_trans (by norm_num) psum813o2_339
  · exact le_trans (by norm_num) psum813o2_340
  · exact le_trans (by norm_num) psum813o2_341
  · exact le_trans (by norm_num) psum813o2_342
  · exact le_trans (by norm_num) psum813o2_343
  · exact le_trans (by norm_num) psum813o2_344
  · exact le_trans (by norm_num) psum813o2_345
  · exact le_trans (by norm_num) psum813o2_346
  · exact le_trans (by norm_num) psum813o2_347
  · exact le_trans (by norm_num) psum813o2_348
  · exact le_trans (by norm_num) psum813o2_349
  · exact le_trans (by norm_num) psum813o2_350
  · exact le_trans (by norm_num) psum813o2_351
  · exact le_trans (by norm_num) psum813o2_352
  · exact le_trans (by norm_num) psum813o2_353
  · exact le_trans (by norm_num) psum813o2_354
  · exact le_trans (by norm_num) psum813o2_355
  · exact le_trans (by norm_num) psum813o2_356
  · exact le_trans (by norm_num) psum813o2_357
  · exact le_trans (by norm_num) psum813o2_358
  · exact le_trans (by norm_num) psum813o2_359
  · exact le_trans (by norm_num) psum813o2_360
  · exact le_trans (by norm_num) psum813o2_361
  · exact le_trans (by norm_num) psum813o2_362
  · exact le_trans (by norm_num) psum813o2_363
  · exact le_trans (by norm_num) psum813o2_364
  · exact le_trans (by norm_num) psum813o2_365
  · exact le_trans (by norm_num) psum813o2_366
  · exact le_trans (by norm_num) psum813o2_367
  · exact le_trans (by norm_num) psum813o2_368
  · exact le_trans (by norm_num) psum813o2_369
  · exact le_trans (by norm_num) psum813o2_370
  · exact le_trans (by norm_num) psum813o2_371
  · exact le_trans (by norm_num) psum813o2_372
  · exact le_trans (by norm_num) psum813o2_373
  · exact le_trans (by norm_num) psum813o2_374
  · exact le_trans (by norm_num) psum813o2_375
  · exact le_trans (by norm_num) psum813o2_376
  · exact le_trans (by norm_num) psum813o2_377
  · exact le_trans (by norm_num) psum813o2_378
  · exact le_trans (by norm_num) psum813o2_379
  · exact le_trans (by norm_num) psum813o2_380
  · exact le_trans (by norm_num) psum813o2_381
  · exact le_trans (by norm_num) psum813o2_382
  · exact le_trans (by norm_num) psum813o2_383
  · exact le_trans (by norm_num) psum813o2_384
  · exact le_trans (by norm_num) psum813o2_385
  · exact le_trans (by norm_num) psum813o2_386
  · exact le_trans (by norm_num) psum813o2_387
  · exact le_trans (by norm_num) psum813o2_388
  · exact le_trans (by norm_num) psum813o2_389
  · exact le_trans (by norm_num) psum813o2_390
  · exact le_trans (by norm_num) psum813o2_391
  · exact le_trans (by norm_num) psum813o2_392
  · exact le_trans (by norm_num) psum813o2_393
  · exact le_trans (by norm_num) psum813o2_394
  · exact le_trans (by norm_num) psum813o2_395
  · exact le_trans (by norm_num) psum813o2_396
  · exact le_trans (by norm_num) psum813o2_397
  · exact le_trans (by norm_num) psum813o2_398
  · exact le_trans (by norm_num) psum813o2_399
  · exact le_trans (by norm_num) psum813o2_400
  · exact le_trans (by norm_num) psum813o2_401
  · exact le_trans (by norm_num) psum813o2_402
  · exact le_trans (by norm_num) psum813o2_403
  · exact le_trans (by norm_num) psum813o2_404
  · exact le_trans (by norm_num) psum813o2_405
  · exact le_trans (by norm_num) psum813o2_406
  · exact le_trans (by norm_num) psum813o2_407
  · exact le_trans (by norm_num) psum813o2_408
  · exact le_trans (by norm_num) psum813o2_409
  · exact le_trans (by norm_num) psum813o2_410
  · exact le_trans (by norm_num) psum813o2_411
  · exact le_trans (by norm_num) psum813o2_412
  · exact le_trans (by norm_num) psum813o2_413
  · exact le_trans (by norm_num) psum813o2_414
  · exact le_trans (by norm_num) psum813o2_415
  · exact le_trans (by norm_num) psum813o2_416
  · exact le_trans (by norm_num) psum813o2_417
  · exact le_trans (by norm_num) psum813o2_418
  · exact le_trans (by norm_num) psum813o2_419
  · exact le_trans (by norm_num) psum813o2_420
  · exact le_trans (by norm_num) psum813o2_421
  · exact le_trans (by norm_num) psum813o2_422
  · exact le_trans (by norm_num) psum813o2_423
  · exact le_trans (by norm_num) psum813o2_424
  · exact le_trans (by norm_num) psum813o2_425
  · exact le_trans (by norm_num) psum813o2_426
  · exact le_trans (by norm_num) psum813o2_427
  · exact le_trans (by norm_num) psum813o2_428
  · exact le_trans (by norm_num) psum813o2_429
  · exact le_trans (by norm_num) psum813o2_430
  · exact le_trans (by norm_num) psum813o2_431
  · exact le_trans (by norm_num) psum813o2_432
  · exact le_trans (by norm_num) psum813o2_433
  · exact le_trans (by norm_num) psum813o2_434
  · exact le_trans (by norm_num) psum813o2_435
  · exact le_trans (by norm_num) psum813o2_436
  · exact le_trans (by norm_num) psum813o2_437
  · exact le_trans (by norm_num) psum813o2_438
  · exact le_trans (by norm_num) psum813o2_439
  · exact le_trans (by norm_num) psum813o2_440
  · exact le_trans (by norm_num) psum813o2_441
  · exact le_trans (by norm_num) psum813o2_442
  · exact le_trans (by norm_num) psum813o2_443
  · exact le_trans (by norm_num) psum813o2_444
  · exact le_trans (by norm_num) psum813o2_445
  · exact le_trans (by norm_num) psum813o2_446
  · exact le_trans (by norm_num) psum813o2_447
  · exact le_trans (by norm_num) psum813o2_448
  · exact le_trans (by norm_num) psum813o2_449
  · exact le_trans (by norm_num) psum813o2_450
  · exact le_trans (by norm_num) psum813o2_451
  · exact le_trans (by norm_num) psum813o2_452
  · exact le_trans (by norm_num) psum813o2_453
  · exact le_trans (by norm_num) psum813o2_454
  · exact le_trans (by norm_num) psum813o2_455
  · exact le_trans (by norm_num) psum813o2_456
  · exact le_trans (by norm_num) psum813o2_457
  · exact le_trans (by norm_num) psum813o2_458
  · exact le_trans (by norm_num) psum813o2_459
  · exact le_trans (by norm_num) psum813o2_460
  · exact le_trans (by norm_num) psum813o2_461
  · exact le_trans (by norm_num) psum813o2_462
  · exact le_trans (by norm_num) psum813o2_463
  · exact le_trans (by norm_num) psum813o2_464
  · exact le_trans (by norm_num) psum813o2_465
  · exact le_trans (by norm_num) psum813o2_466
  · exact le_trans (by norm_num) psum813o2_467
  · exact le_trans (by norm_num) psum813o2_468
  · exact le_trans (by norm_num) psum813o2_469
  · exact le_trans (by norm_num) psum813o2_470
  · exact le_trans (by norm_num) psum813o2_471
  · exact le_trans (by norm_num) psum813o2_472
  · exact le_trans (by norm_num) psum813o2_473
  · exact le_trans (by norm_num) psum813o2_474
  · exact le_trans (by norm_num) psum813o2_475
  · exact le_trans (by norm_num) psum813o2_476
  · exact le_trans (by norm_num) psum813o2_477
  · exact le_trans (by norm_num) psum813o2_478
  · exact le_trans (by norm_num) psum813o2_479
  · exact le_trans (by norm_num) psum813o2_480
  · exact le_trans (by norm_num) psum813o2_481
  · exact le_trans (by norm_num) psum813o2_482
  · exact le_trans (by norm_num) psum813o2_483
  · exact le_trans (by norm_num) psum813o2_484
  · exact le_trans (by norm_num) psum813o2_485
  · exact le_trans (by norm_num) psum813o2_486
  · exact le_trans (by norm_num) psum813o2_487
  · exact le_trans (by norm_num) psum813o2_488
  · exact le_trans (by norm_num) psum813o2_489
  · exact le_trans (by norm_num) psum813o2_490
  · exact le_trans (by norm_num) psum813o2_491
  · exact le_trans (by norm_num) psum813o2_492
  · exact le_trans (by norm_num) psum813o2_493
  · exact le_trans (by norm_num) psum813o2_494
  · exact le_trans (by norm_num) psum813o2_495
  · exact le_trans (by norm_num) psum813o2_496
  · exact le_trans (by norm_num) psum813o2_497
  · exact le_trans (by norm_num) psum813o2_498
  · exact le_trans (by norm_num) psum813o2_499
  · exact le_trans (by norm_num) psum813o2_500

end CriticalLinePhasor.DVP

section AxiomAudit
#print axioms CriticalLinePhasor.DVP.psum813o2_floor
#print axioms CriticalLinePhasor.DVP.psum813o2_500
end AxiomAudit
