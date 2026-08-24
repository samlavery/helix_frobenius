import RequestProject.DVPCos435o2Table

/-!
# The cosine partial-sum floor, `t = 435/2`
-/

open Finset

noncomputable section

namespace CriticalLinePhasor.DVP

/-- The cosine sequence of the `t = 435/2` segment certificate. -/
def cos435o2c (n : ℕ) : ℝ := Real.cos (((435:ℕ):ℝ) * (Real.log n / 2))

theorem psum435o2_11 : ((249811/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 11, cos435o2c k := by
  rw [Finset.Icc_self, Finset.sum_singleton]
  have h : -((1/25000 : ℚ) : ℝ) ≤ cos435o2c 11 - ((249821/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos435o2_br_11).1
  push_cast at h ⊢
  linarith

theorem psum435o2_12 : ((1992797/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 12, cos435o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 12, cos435o2c k)
      = (∑ k ∈ Finset.Icc 11 11, cos435o2c k) + cos435o2c 12 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 11) (by norm_num) cos435o2c
    simpa using h
  have hprev := psum435o2_11
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos435o2c 12 - ((993593/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos435o2_br_12).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum435o2_13 : ((2234137/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 13, cos435o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 13, cos435o2c k)
      = (∑ k ∈ Finset.Icc 11 12, cos435o2c k) + cos435o2c 13 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 12) (by norm_num) cos435o2c
    simpa using h
  have hprev := psum435o2_12
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos435o2c 13 - ((12069/50000 : ℚ) : ℝ) :=
    (abs_le.mp cos435o2_br_13).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum435o2_14 : ((812741/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 14, cos435o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 14, cos435o2c k)
      = (∑ k ∈ Finset.Icc 11 13, cos435o2c k) + cos435o2c 14 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 13) (by norm_num) cos435o2c
    simpa using h
  have hprev := psum435o2_13
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos435o2c 14 - ((-121723/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos435o2_br_14).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum435o2_15 : ((1577767/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 15, cos435o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 15, cos435o2c k)
      = (∑ k ∈ Finset.Icc 11 14, cos435o2c k) + cos435o2c 15 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 14) (by norm_num) cos435o2c
    simpa using h
  have hprev := psum435o2_14
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos435o2c 15 - ((-1907/40000 : ℚ) : ℝ) :=
    (abs_le.mp cos435o2_br_15).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum435o2_16 : ((1283417/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 16, cos435o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 16, cos435o2c k)
      = (∑ k ∈ Finset.Icc 11 15, cos435o2c k) + cos435o2c 16 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 15) (by norm_num) cos435o2c
    simpa using h
  have hprev := psum435o2_15
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos435o2c 16 - ((989107/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos435o2_br_16).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum435o2_17 : ((3457571/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 17, cos435o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 17, cos435o2c k)
      = (∑ k ∈ Finset.Icc 11 16, cos435o2c k) + cos435o2c 17 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 16) (by norm_num) cos435o2c
    simpa using h
  have hprev := psum435o2_16
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos435o2c 17 - ((890777/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos435o2_br_17).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum435o2_18 : ((2200587/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 18, cos435o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 18, cos435o2c k)
      = (∑ k ∈ Finset.Icc 11 17, cos435o2c k) + cos435o2c 18 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 17) (by norm_num) cos435o2c
    simpa using h
  have hprev := psum435o2_17
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos435o2c 18 - ((943643/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos435o2_br_18).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum435o2_19 : ((33081/6250 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 19, cos435o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 19, cos435o2c k)
      = (∑ k ∈ Finset.Icc 11 18, cos435o2c k) + cos435o2c 19 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 18) (by norm_num) cos435o2c
    simpa using h
  have hprev := psum435o2_18
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos435o2c 19 - ((445913/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos435o2_br_19).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum435o2_20 : ((4989089/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 20, cos435o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 20, cos435o2c k)
      = (∑ k ∈ Finset.Icc 11 19, cos435o2c k) + cos435o2c 20 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 19) (by norm_num) cos435o2c
    simpa using h
  have hprev := psum435o2_19
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos435o2c 20 - ((-303831/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos435o2_br_20).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum435o2_21 : ((263709/62500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 21, cos435o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 21, cos435o2c k)
      = (∑ k ∈ Finset.Icc 11 20, cos435o2c k) + cos435o2c 21 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 20) (by norm_num) cos435o2c
    simpa using h
  have hprev := psum435o2_20
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos435o2c 21 - ((-153941/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos435o2_br_21).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum435o2_22 : ((652413/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 22, cos435o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 22, cos435o2c k)
      = (∑ k ∈ Finset.Icc 11 21, cos435o2c k) + cos435o2c 22 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 21) (by norm_num) cos435o2c
    simpa using h
  have hprev := psum435o2_21
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos435o2c 22 - ((1 : ℚ) : ℝ) :=
    (abs_le.mp cos435o2_br_22).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum435o2_23 : ((212449/50000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 23, cos435o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 23, cos435o2c k)
      = (∑ k ∈ Finset.Icc 11 22, cos435o2c k) + cos435o2c 23 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 22) (by norm_num) cos435o2c
    simpa using h
  have hprev := psum435o2_22
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos435o2c 23 - ((-242571/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos435o2_br_23).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum435o2_24 : ((1311507/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 24, cos435o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 24, cos435o2c k)
      = (∑ k ∈ Finset.Icc 11 23, cos435o2c k) + cos435o2c 24 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 23) (by norm_num) cos435o2c
    simpa using h
  have hprev := psum435o2_23
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos435o2c 24 - ((31159/31250 : ℚ) : ℝ) :=
    (abs_le.mp cos435o2_br_24).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum435o2_25 : ((1088567/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 25, cos435o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 25, cos435o2c k)
      = (∑ k ∈ Finset.Icc 11 24, cos435o2c k) + cos435o2c 25 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 24) (by norm_num) cos435o2c
    simpa using h
  have hprev := psum435o2_24
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos435o2c 25 - ((-22293/25000 : ℚ) : ℝ) :=
    (abs_le.mp cos435o2_br_25).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum435o2_26 : ((1139903/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 26, cos435o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 26, cos435o2c k)
      = (∑ k ∈ Finset.Icc 11 25, cos435o2c k) + cos435o2c 26 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 25) (by norm_num) cos435o2c
    simpa using h
  have hprev := psum435o2_25
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos435o2c 26 - ((25673/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos435o2_br_26).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum435o2_27 : ((675761/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 27, cos435o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 27, cos435o2c k)
      = (∑ k ∈ Finset.Icc 11 26, cos435o2c k) + cos435o2c 27 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 26) (by norm_num) cos435o2c
    simpa using h
  have hprev := psum435o2_26
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos435o2c 27 - ((211629/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos435o2_br_27).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum435o2_28 : ((965429/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 28, cos435o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 28, cos435o2c k)
      = (∑ k ∈ Finset.Icc 11 27, cos435o2c k) + cos435o2c 28 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 27) (by norm_num) cos435o2c
    simpa using h
  have hprev := psum435o2_27
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos435o2c 28 - ((-578903/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos435o2_br_28).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum435o2_29 : ((3904401/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 29, cos435o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 29, cos435o2c k)
      = (∑ k ∈ Finset.Icc 11 28, cos435o2c k) + cos435o2c 29 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 28) (by norm_num) cos435o2c
    simpa using h
  have hprev := psum435o2_28
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos435o2c 29 - ((-57669/62500 : ℚ) : ℝ) :=
    (abs_le.mp cos435o2_br_29).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum435o2_30 : ((477477/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 30, cos435o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 30, cos435o2c k)
      = (∑ k ∈ Finset.Icc 11 29, cos435o2c k) + cos435o2c 30 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 29) (by norm_num) cos435o2c
    simpa using h
  have hprev := psum435o2_29
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos435o2c 30 - ((-16909/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos435o2_br_30).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum435o2_31 : ((4511571/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 31, cos435o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 31, cos435o2c k)
      = (∑ k ∈ Finset.Icc 11 30, cos435o2c k) + cos435o2c 31 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 30) (by norm_num) cos435o2c
    simpa using h
  have hprev := psum435o2_30
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos435o2c 31 - ((138359/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos435o2_br_31).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum435o2_32 : ((85852/15625 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 32, cos435o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 32, cos435o2c k)
      = (∑ k ∈ Finset.Icc 11 31, cos435o2c k) + cos435o2c 32 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 31) (by norm_num) cos435o2c
    simpa using h
  have hprev := psum435o2_31
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos435o2c 32 - ((982997/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos435o2_br_32).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum435o2_33 : ((6469289/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 33, cos435o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 33, cos435o2c k)
      = (∑ k ∈ Finset.Icc 11 32, cos435o2c k) + cos435o2c 33 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 32) (by norm_num) cos435o2c
    simpa using h
  have hprev := psum435o2_32
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos435o2c 33 - ((974801/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos435o2_br_33).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum435o2_34 : ((3688099/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 34, cos435o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 34, cos435o2c k)
      = (∑ k ∈ Finset.Icc 11 33, cos435o2c k) + cos435o2c 34 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 33) (by norm_num) cos435o2c
    simpa using h
  have hprev := psum435o2_33
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos435o2c 34 - ((906949/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos435o2_br_34).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum435o2_35 : ((8273799/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 35, cos435o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 35, cos435o2c k)
      = (∑ k ∈ Finset.Icc 11 34, cos435o2c k) + cos435o2c 35 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 34) (by norm_num) cos435o2c
    simpa using h
  have hprev := psum435o2_34
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos435o2c 35 - ((897641/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos435o2_br_35).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum435o2_36 : ((9228979/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 36, cos435o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 36, cos435o2c k)
      = (∑ k ∈ Finset.Icc 11 35, cos435o2c k) + cos435o2c 36 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 35) (by norm_num) cos435o2c
    simpa using h
  have hprev := psum435o2_35
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos435o2c 36 - ((47761/50000 : ℚ) : ℝ) :=
    (abs_le.mp cos435o2_br_36).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum435o2_37 : ((10228663/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 37, cos435o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 37, cos435o2c k)
      = (∑ k ∈ Finset.Icc 11 36, cos435o2c k) + cos435o2c 37 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 36) (by norm_num) cos435o2c
    simpa using h
  have hprev := psum435o2_36
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos435o2c 37 - ((249931/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos435o2_br_37).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum435o2_38 : ((5551569/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 38, cos435o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 38, cos435o2c k)
      = (∑ k ∈ Finset.Icc 11 37, cos435o2c k) + cos435o2c 38 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 37) (by norm_num) cos435o2c
    simpa using h
  have hprev := psum435o2_37
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos435o2c 38 - ((174903/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos435o2_br_38).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum435o2_39 : ((5760403/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 39, cos435o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 39, cos435o2c k)
      = (∑ k ∈ Finset.Icc 11 38, cos435o2c k) + cos435o2c 39 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 38) (by norm_num) cos435o2c
    simpa using h
  have hprev := psum435o2_38
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos435o2c 39 - ((104427/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos435o2_br_39).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum435o2_40 : ((2236393/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 40, cos435o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 40, cos435o2c k)
      = (∑ k ∈ Finset.Icc 11 39, cos435o2c k) + cos435o2c 40 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 39) (by norm_num) cos435o2c
    simpa using h
  have hprev := psum435o2_39
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos435o2c 40 - ((-338801/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos435o2_br_40).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum435o2_41 : ((10230391/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 41, cos435o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 41, cos435o2c k)
      = (∑ k ∈ Finset.Icc 11 40, cos435o2c k) + cos435o2c 41 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 40) (by norm_num) cos435o2c
    simpa using h
  have hprev := psum435o2_40
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos435o2c 41 - ((-475767/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos435o2_br_41).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum435o2_42 : ((4742371/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 42, cos435o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 42, cos435o2c k)
      = (∑ k ∈ Finset.Icc 11 41, cos435o2c k) + cos435o2c 42 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 41) (by norm_num) cos435o2c
    simpa using h
  have hprev := psum435o2_41
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos435o2c 42 - ((-745609/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos435o2_br_42).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum435o2_43 : ((2450731/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 43, cos435o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 43, cos435o2c k)
      = (∑ k ∈ Finset.Icc 11 42, cos435o2c k) + cos435o2c 43 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 42) (by norm_num) cos435o2c
    simpa using h
  have hprev := psum435o2_42
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos435o2c 43 - ((159111/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos435o2_br_43).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum435o2_44 : ((2160447/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 44, cos435o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 44, cos435o2c k)
      = (∑ k ∈ Finset.Icc 11 43, cos435o2c k) + cos435o2c 44 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 43) (by norm_num) cos435o2c
    simpa using h
  have hprev := psum435o2_43
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos435o2c 44 - ((999351/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos435o2_br_44).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum435o2_45 : ((10941163/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 45, cos435o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 45, cos435o2c k)
      = (∑ k ∈ Finset.Icc 11 44, cos435o2c k) + cos435o2c 45 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 44) (by norm_num) cos435o2c
    simpa using h
  have hprev := psum435o2_44
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos435o2c 45 - ((17371/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos435o2_br_45).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum435o2_46 : ((4981281/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 46, cos435o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 46, cos435o2c k)
      = (∑ k ∈ Finset.Icc 11 45, cos435o2c k) + cos435o2c 46 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 45) (by norm_num) cos435o2c
    simpa using h
  have hprev := psum435o2_45
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos435o2c 46 - ((-978561/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos435o2_br_46).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum435o2_47 : ((9790707/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 47, cos435o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 47, cos435o2c k)
      = (∑ k ∈ Finset.Icc 11 46, cos435o2c k) + cos435o2c 47 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 46) (by norm_num) cos435o2c
    simpa using h
  have hprev := psum435o2_46
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos435o2c 47 - ((-34363/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos435o2_br_47).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum435o2_48 : ((10789891/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 48, cos435o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 48, cos435o2c k)
      = (∑ k ∈ Finset.Icc 11 47, cos435o2c k) + cos435o2c 48 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 47) (by norm_num) cos435o2c
    simpa using h
  have hprev := psum435o2_47
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos435o2c 48 - ((124903/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos435o2_br_48).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum435o2_49 : ((5301323/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 49, cos435o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 49, cos435o2c k)
      = (∑ k ∈ Finset.Icc 11 48, cos435o2c k) + cos435o2c 49 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 48) (by norm_num) cos435o2c
    simpa using h
  have hprev := psum435o2_48
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos435o2c 49 - ((-37441/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos435o2_br_49).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum435o2_50 : ((1945641/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 50, cos435o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 50, cos435o2c k)
      = (∑ k ∈ Finset.Icc 11 49, cos435o2c k) + cos435o2c 50 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 49) (by norm_num) cos435o2c
    simpa using h
  have hprev := psum435o2_49
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos435o2c 50 - ((-874401/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos435o2_br_50).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum435o2_51 : ((2103769/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 51, cos435o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 51, cos435o2c k)
      = (∑ k ∈ Finset.Icc 11 50, cos435o2c k) + cos435o2c 51 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 50) (by norm_num) cos435o2c
    simpa using h
  have hprev := psum435o2_50
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos435o2c 51 - ((19767/25000 : ℚ) : ℝ) :=
    (abs_le.mp cos435o2_br_51).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum435o2_52 : ((10687913/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 52, cos435o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 52, cos435o2c k)
      = (∑ k ∈ Finset.Icc 11 51, cos435o2c k) + cos435o2c 52 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 51) (by norm_num) cos435o2c
    simpa using h
  have hprev := psum435o2_51
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos435o2c 52 - ((42277/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos435o2_br_52).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum435o2_53 : ((976661/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 53, cos435o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 53, cos435o2c k)
      = (∑ k ∈ Finset.Icc 11 52, cos435o2c k) + cos435o2c 53 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 52) (by norm_num) cos435o2c
    simpa using h
  have hprev := psum435o2_52
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos435o2c 53 - ((-921263/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos435o2_br_53).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum435o2_54 : ((2126433/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 54, cos435o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 54, cos435o2c k)
      = (∑ k ∈ Finset.Icc 11 53, cos435o2c k) + cos435o2c 54 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 53) (by norm_num) cos435o2c
    simpa using h
  have hprev := psum435o2_53
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos435o2c 54 - ((173119/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos435o2_br_54).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum435o2_55 : ((2609099/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 55, cos435o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 55, cos435o2c k)
      = (∑ k ∈ Finset.Icc 11 54, cos435o2c k) + cos435o2c 55 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 54) (by norm_num) cos435o2c
    simpa using h
  have hprev := psum435o2_54
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos435o2c 55 - ((-195729/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos435o2_br_55).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum435o2_56 : ((9887973/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 56, cos435o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 56, cos435o2c k)
      = (∑ k ∈ Finset.Icc 11 55, cos435o2c k) + cos435o2c 56 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 55) (by norm_num) cos435o2c
    simpa using h
  have hprev := psum435o2_55
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos435o2c 56 - ((-548383/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos435o2_br_56).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum435o2_57 : ((10848351/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 57, cos435o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 57, cos435o2c k)
      = (∑ k ∈ Finset.Icc 11 56, cos435o2c k) + cos435o2c 57 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 56) (by norm_num) cos435o2c
    simpa using h
  have hprev := psum435o2_56
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos435o2c 57 - ((480209/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos435o2_br_57).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum435o2_58 : ((4956001/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 58, cos435o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 58, cos435o2c k)
      = (∑ k ∈ Finset.Icc 11 57, cos435o2c k) + cos435o2c 58 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 57) (by norm_num) cos435o2c
    simpa using h
  have hprev := psum435o2_57
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos435o2c 58 - ((-936309/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos435o2_br_58).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum435o2_59 : ((2101113/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 59, cos435o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 59, cos435o2c k)
      = (∑ k ∈ Finset.Icc 11 58, cos435o2c k) + cos435o2c 59 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 58) (by norm_num) cos435o2c
    simpa using h
  have hprev := psum435o2_58
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos435o2c 59 - ((593603/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos435o2_br_59).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum435o2_60 : ((10384247/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 60, cos435o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 60, cos435o2c k)
      = (∑ k ∈ Finset.Icc 11 59, cos435o2c k) + cos435o2c 60 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 59) (by norm_num) cos435o2c
    simpa using h
  have hprev := psum435o2_59
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos435o2c 60 - ((-60639/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos435o2_br_60).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum435o2_61 : ((10058317/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 61, cos435o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 61, cos435o2c k)
      = (∑ k ∈ Finset.Icc 11 60, cos435o2c k) + cos435o2c 61 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 60) (by norm_num) cos435o2c
    simpa using h
  have hprev := psum435o2_60
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos435o2c 61 - ((-32589/100000 : ℚ) : ℝ) :=
    (abs_le.mp cos435o2_br_61).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum435o2_62 : ((5361461/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 62, cos435o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 62, cos435o2c k)
      = (∑ k ∈ Finset.Icc 11 61, cos435o2c k) + cos435o2c 62 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 61) (by norm_num) cos435o2c
    simpa using h
  have hprev := psum435o2_61
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos435o2c 62 - ((132929/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos435o2_br_62).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum435o2_63 : ((1969569/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 63, cos435o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 63, cos435o2c k)
      = (∑ k ∈ Finset.Icc 11 62, cos435o2c k) + cos435o2c 63 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 62) (by norm_num) cos435o2c
    simpa using h
  have hprev := psum435o2_62
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos435o2c 63 - ((-875037/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos435o2_br_63).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum435o2_64 : ((10823347/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 64, cos435o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 64, cos435o2c k)
      = (∑ k ∈ Finset.Icc 11 63, cos435o2c k) + cos435o2c 64 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 63) (by norm_num) cos435o2c
    simpa using h
  have hprev := psum435o2_63
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos435o2c 64 - ((487771/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos435o2_br_64).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum435o2_65 : ((9823347/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 65, cos435o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 65, cos435o2c k)
      = (∑ k ∈ Finset.Icc 11 64, cos435o2c k) + cos435o2c 65 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 64) (by norm_num) cos435o2c
    simpa using h
  have hprev := psum435o2_64
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos435o2c 65 - ((-24999/25000 : ℚ) : ℝ) :=
    (abs_le.mp cos435o2_br_65).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum435o2_66 : ((135071/12500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 66, cos435o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 66, cos435o2c k)
      = (∑ k ∈ Finset.Icc 11 65, cos435o2c k) + cos435o2c 66 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 65) (by norm_num) cos435o2c
    simpa using h
  have hprev := psum435o2_65
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos435o2c 66 - ((982373/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos435o2_br_66).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum435o2_67 : ((2463881/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 67, cos435o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 67, cos435o2c k)
      = (∑ k ∈ Finset.Icc 11 66, cos435o2c k) + cos435o2c 67 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 66) (by norm_num) cos435o2c
    simpa using h
  have hprev := psum435o2_66
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos435o2c 67 - ((-237529/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos435o2_br_67).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum435o2_68 : ((1347171/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 68, cos435o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 68, cos435o2c k)
      = (∑ k ∈ Finset.Icc 11 67, cos435o2c k) + cos435o2c 68 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 67) (by norm_num) cos435o2c
    simpa using h
  have hprev := psum435o2_67
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos435o2c 68 - ((230471/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos435o2_br_68).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum435o2_69 : ((9869/1000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 69, cos435o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 69, cos435o2c k)
      = (∑ k ∈ Finset.Icc 11 68, cos435o2c k) + cos435o2c 69 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 68) (by norm_num) cos435o2c
    simpa using h
  have hprev := psum435o2_68
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos435o2c 69 - ((-113541/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos435o2_br_69).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum435o2_70 : ((5391131/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 70, cos435o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 70, cos435o2c k)
      = (∑ k ∈ Finset.Icc 11 69, cos435o2c k) + cos435o2c 70 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 69) (by norm_num) cos435o2c
    simpa using h
  have hprev := psum435o2_69
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos435o2c 70 - ((456651/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos435o2_br_70).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum435o2_71 : ((9847399/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 71, cos435o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 71, cos435o2c k)
      = (∑ k ∈ Finset.Icc 11 70, cos435o2c k) + cos435o2c 71 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 70) (by norm_num) cos435o2c
    simpa using h
  have hprev := psum435o2_70
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos435o2c 71 - ((-934823/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos435o2_br_71).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum435o2_72 : ((10812853/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 72, cos435o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 72, cos435o2c k)
      = (∑ k ∈ Finset.Icc 11 71, cos435o2c k) + cos435o2c 72 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 71) (by norm_num) cos435o2c
    simpa using h
  have hprev := psum435o2_71
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos435o2c 72 - ((482747/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos435o2_br_72).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum435o2_73 : ((1964047/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 73, cos435o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 73, cos435o2c k)
      = (∑ k ∈ Finset.Icc 11 72, cos435o2c k) + cos435o2c 73 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 72) (by norm_num) cos435o2c
    simpa using h
  have hprev := psum435o2_72
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos435o2c 73 - ((-496289/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos435o2_br_73).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum435o2_74 : ((169037/15625 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 74, cos435o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 74, cos435o2c k)
      = (∑ k ∈ Finset.Icc 11 73, cos435o2c k) + cos435o2c 74 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 73) (by norm_num) cos435o2c
    simpa using h
  have hprev := psum435o2_73
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos435o2c 74 - ((998173/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos435o2_br_74).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum435o2_75 : ((394319/40000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 75, cos435o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 75, cos435o2c k)
      = (∑ k ∈ Finset.Icc 11 74, cos435o2c k) + cos435o2c 75 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 74) (by norm_num) cos435o2c
    simpa using h
  have hprev := psum435o2_74
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos435o2c 75 - ((-960353/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos435o2_br_75).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum435o2_76 : ((5356973/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 76, cos435o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 76, cos435o2c k)
      = (∑ k ∈ Finset.Icc 11 75, cos435o2c k) + cos435o2c 76 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 75) (by norm_num) cos435o2c
    simpa using h
  have hprev := psum435o2_75
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos435o2c 76 - ((856011/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos435o2_br_76).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum435o2_77 : ((10047713/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 77, cos435o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 77, cos435o2c k)
      = (∑ k ∈ Finset.Icc 11 76, cos435o2c k) + cos435o2c 77 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 76) (by norm_num) cos435o2c
    simpa using h
  have hprev := psum435o2_76
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos435o2c 77 - ((-666193/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos435o2_br_77).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum435o2_78 : ((10431549/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 78, cos435o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 78, cos435o2c k)
      = (∑ k ∈ Finset.Icc 11 77, cos435o2c k) + cos435o2c 78 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 77) (by norm_num) cos435o2c
    simpa using h
  have hprev := psum435o2_77
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos435o2c 78 - ((95969/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos435o2_br_78).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum435o2_79 : ((10408381/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 79, cos435o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 79, cos435o2c k)
      = (∑ k ∈ Finset.Icc 11 78, cos435o2c k) + cos435o2c 79 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 78) (by norm_num) cos435o2c
    simpa using h
  have hprev := psum435o2_78
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos435o2c 79 - ((-2891/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos435o2_br_79).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum435o2_80 : ((10035031/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 80, cos435o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 80, cos435o2c k)
      = (∑ k ∈ Finset.Icc 11 79, cos435o2c k) + cos435o2c 80 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 79) (by norm_num) cos435o2c
    simpa using h
  have hprev := psum435o2_79
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos435o2c 80 - ((-37331/100000 : ℚ) : ℝ) :=
    (abs_le.mp cos435o2_br_80).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum435o2_81 : ((2153537/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 81, cos435o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 81, cos435o2c k)
      = (∑ k ∈ Finset.Icc 11 80, cos435o2c k) + cos435o2c 81 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 80) (by norm_num) cos435o2c
    simpa using h
  have hprev := psum435o2_80
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos435o2c 81 - ((366347/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos435o2_br_81).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum435o2_82 : ((2451351/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 82, cos435o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 82, cos435o2c k)
      = (∑ k ∈ Finset.Icc 11 81, cos435o2c k) + cos435o2c 82 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 81) (by norm_num) cos435o2c
    simpa using h
  have hprev := psum435o2_81
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos435o2c 82 - ((-962241/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos435o2_br_82).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum435o2_83 : ((5389571/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 83, cos435o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 83, cos435o2c k)
      = (∑ k ∈ Finset.Icc 11 82, cos435o2c k) + cos435o2c 83 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 82) (by norm_num) cos435o2c
    simpa using h
  have hprev := psum435o2_82
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos435o2c 83 - ((486889/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos435o2_br_83).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum435o2_84 : ((5029307/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 84, cos435o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 84, cos435o2c k)
      = (∑ k ∈ Finset.Icc 11 83, cos435o2c k) + cos435o2c 84 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 83) (by norm_num) cos435o2c
    simpa using h
  have hprev := psum435o2_83
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos435o2c 84 - ((-90061/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos435o2_br_84).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum435o2_85 : ((1029327/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 85, cos435o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 85, cos435o2c k)
      = (∑ k ∈ Finset.Icc 11 84, cos435o2c k) + cos435o2c 85 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 84) (by norm_num) cos435o2c
    simpa using h
  have hprev := psum435o2_84
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos435o2c 85 - ((29337/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos435o2_br_85).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum435o2_86 : ((10646259/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 86, cos435o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 86, cos435o2c k)
      = (∑ k ∈ Finset.Icc 11 85, cos435o2c k) + cos435o2c 86 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 85) (by norm_num) cos435o2c
    simpa using h
  have hprev := psum435o2_85
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos435o2c 86 - ((353029/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos435o2_br_86).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum435o2_87 : ((1962269/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 87, cos435o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 87, cos435o2c k)
      = (∑ k ∈ Finset.Icc 11 86, cos435o2c k) + cos435o2c 87 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 86) (by norm_num) cos435o2c
    simpa using h
  have hprev := psum435o2_86
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos435o2c 87 - ((-417437/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos435o2_br_87).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum435o2_88 : ((2161729/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 88, cos435o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 88, cos435o2c k)
      = (∑ k ∈ Finset.Icc 11 87, cos435o2c k) + cos435o2c 88 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 87) (by norm_num) cos435o2c
    simpa using h
  have hprev := psum435o2_87
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos435o2c 88 - ((49867/50000 : ℚ) : ℝ) :=
    (abs_le.mp cos435o2_br_88).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum435o2_89 : ((10081643/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 89, cos435o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 89, cos435o2c k)
      = (∑ k ∈ Finset.Icc 11 88, cos435o2c k) + cos435o2c 89 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 88) (by norm_num) cos435o2c
    simpa using h
  have hprev := psum435o2_88
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos435o2c 89 - ((-363481/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos435o2_br_89).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum435o2_90 : ((10183911/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 90, cos435o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 90, cos435o2c k)
      = (∑ k ∈ Finset.Icc 11 89, cos435o2c k) + cos435o2c 90 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 89) (by norm_num) cos435o2c
    simpa using h
  have hprev := psum435o2_89
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos435o2c 90 - ((25577/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos435o2_br_90).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum435o2_91 : ((10777663/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 91, cos435o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 91, cos435o2c k)
      = (∑ k ∈ Finset.Icc 11 90, cos435o2c k) + cos435o2c 91 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 90) (by norm_num) cos435o2c
    simpa using h
  have hprev := psum435o2_90
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos435o2c 91 - ((9278/15625 : ℚ) : ℝ) :=
    (abs_le.mp cos435o2_br_91).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum435o2_92 : ((2448031/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 92, cos435o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 92, cos435o2c k)
      = (∑ k ∈ Finset.Icc 11 91, cos435o2c k) + cos435o2c 92 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 91) (by norm_num) cos435o2c
    simpa using h
  have hprev := psum435o2_91
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos435o2c 92 - ((-985499/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos435o2_br_92).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum435o2_93 : ((10606129/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 93, cos435o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 93, cos435o2c k)
      = (∑ k ∈ Finset.Icc 11 92, cos435o2c k) + cos435o2c 93 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 92) (by norm_num) cos435o2c
    simpa using h
  have hprev := psum435o2_92
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos435o2c 93 - ((162809/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos435o2_br_93).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum435o2_94 : ((10470787/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 94, cos435o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 94, cos435o2c k)
      = (∑ k ∈ Finset.Icc 11 93, cos435o2c k) + cos435o2c 94 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 93) (by norm_num) cos435o2c
    simpa using h
  have hprev := psum435o2_93
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos435o2c 94 - ((-67651/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos435o2_br_94).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum435o2_95 : ((9823271/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 95, cos435o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 95, cos435o2c k)
      = (∑ k ∈ Finset.Icc 11 94, cos435o2c k) + cos435o2c 95 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 94) (by norm_num) cos435o2c
    simpa using h
  have hprev := psum435o2_94
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos435o2c 95 - ((-161869/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos435o2_br_95).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum435o2_96 : ((2705807/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 96, cos435o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 96, cos435o2c k)
      = (∑ k ∈ Finset.Icc 11 95, cos435o2c k) + cos435o2c 96 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 95) (by norm_num) cos435o2c
    simpa using h
  have hprev := psum435o2_95
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos435o2c 96 - ((999997/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos435o2_br_96).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum435o2_97 : ((2547521/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 97, cos435o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 97, cos435o2c k)
      = (∑ k ∈ Finset.Icc 11 96, cos435o2c k) + cos435o2c 97 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 96) (by norm_num) cos435o2c
    simpa using h
  have hprev := psum435o2_96
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos435o2c 97 - ((-39569/62500 : ℚ) : ℝ) :=
    (abs_le.mp cos435o2_br_97).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum435o2_98 : ((9966697/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 98, cos435o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 98, cos435o2c k)
      = (∑ k ∈ Finset.Icc 11 97, cos435o2c k) + cos435o2c 98 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 97) (by norm_num) cos435o2c
    simpa using h
  have hprev := psum435o2_97
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos435o2c 98 - ((-223347/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos435o2_br_98).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum435o2_99 : ((10882937/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 99, cos435o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 99, cos435o2c k)
      = (∑ k ∈ Finset.Icc 11 98, cos435o2c k) + cos435o2c 99 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 98) (by norm_num) cos435o2c
    simpa using h
  have hprev := psum435o2_98
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos435o2c 99 - ((22907/25000 : ℚ) : ℝ) :=
    (abs_le.mp cos435o2_br_99).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum435o2_100 : ((5013509/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 100, cos435o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 100, cos435o2c k)
      = (∑ k ∈ Finset.Icc 11 99, cos435o2c k) + cos435o2c 100 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 99) (by norm_num) cos435o2c
    simpa using h
  have hprev := psum435o2_99
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos435o2c 100 - ((-855879/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos435o2_br_100).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum435o2_101 : ((1259603/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 101, cos435o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 101, cos435o2c k)
      = (∑ k ∈ Finset.Icc 11 100, cos435o2c k) + cos435o2c 101 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 100) (by norm_num) cos435o2c
    simpa using h
  have hprev := psum435o2_100
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos435o2c 101 - ((24923/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos435o2_br_101).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum435o2_102 : ((1088953/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 102, cos435o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 102, cos435o2c k)
      = (∑ k ∈ Finset.Icc 11 101, cos435o2c k) + cos435o2c 102 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 101) (by norm_num) cos435o2c
    simpa using h
  have hprev := psum435o2_101
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos435o2c 102 - ((406373/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos435o2_br_102).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum435o2_103 : ((4983767/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 103, cos435o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 103, cos435o2c k)
      = (∑ k ∈ Finset.Icc 11 102, cos435o2c k) + cos435o2c 103 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 102) (by norm_num) cos435o2c
    simpa using h
  have hprev := psum435o2_102
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos435o2c 103 - ((-230489/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos435o2_br_103).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum435o2_104 : ((5050037/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 104, cos435o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 104, cos435o2c k)
      = (∑ k ∈ Finset.Icc 11 103, cos435o2c k) + cos435o2c 104 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 103) (by norm_num) cos435o2c
    simpa using h
  have hprev := psum435o2_103
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos435o2c 104 - ((6629/50000 : ℚ) : ℝ) :=
    (abs_le.mp cos435o2_br_104).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum435o2_105 : ((1090001/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 105, cos435o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 105, cos435o2c k)
      = (∑ k ∈ Finset.Icc 11 104, cos435o2c k) + cos435o2c 105 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 104) (by norm_num) cos435o2c
    simpa using h
  have hprev := psum435o2_104
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos435o2c 105 - ((99997/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos435o2_br_105).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum435o2_106 : ((1998741/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 106, cos435o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 106, cos435o2c k)
      = (∑ k ∈ Finset.Icc 11 105, cos435o2c k) + cos435o2c 106 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 105) (by norm_num) cos435o2c
    simpa using h
  have hprev := psum435o2_105
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos435o2c 106 - ((-181253/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos435o2_br_106).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum435o2_107 : ((10028709/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 107, cos435o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 107, cos435o2c k)
      = (∑ k ∈ Finset.Icc 11 106, cos435o2c k) + cos435o2c 107 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 106) (by norm_num) cos435o2c
    simpa using h
  have hprev := psum435o2_106
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos435o2c 107 - ((8761/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos435o2_br_107).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum435o2_108 : ((10912163/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 108, cos435o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 108, cos435o2c k)
      = (∑ k ∈ Finset.Icc 11 107, cos435o2c k) + cos435o2c 108 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 107) (by norm_num) cos435o2c
    simpa using h
  have hprev := psum435o2_107
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos435o2c 108 - ((441747/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos435o2_br_108).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum435o2_109 : ((1011571/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 109, cos435o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 109, cos435o2c k)
      = (∑ k ∈ Finset.Icc 11 108, cos435o2c k) + cos435o2c 109 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 108) (by norm_num) cos435o2c
    simpa using h
  have hprev := psum435o2_108
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos435o2c 109 - ((-796413/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos435o2_br_109).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum435o2_110 : ((1976773/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 110, cos435o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 110, cos435o2c k)
      = (∑ k ∈ Finset.Icc 11 109, cos435o2c k) + cos435o2c 110 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 109) (by norm_num) cos435o2c
    simpa using h
  have hprev := psum435o2_109
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos435o2c 110 - ((-46361/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos435o2_br_110).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum435o2_111 : ((2717617/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 111, cos435o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 111, cos435o2c k)
      = (∑ k ∈ Finset.Icc 11 110, cos435o2c k) + cos435o2c 111 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 110) (by norm_num) cos435o2c
    simpa using h
  have hprev := psum435o2_110
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos435o2c 111 - ((986643/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos435o2_br_111).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum435o2_112 : ((5176647/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 112, cos435o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 112, cos435o2c k)
      = (∑ k ∈ Finset.Icc 11 111, cos435o2c k) + cos435o2c 112 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 111) (by norm_num) cos435o2c
    simpa using h
  have hprev := psum435o2_111
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos435o2c 112 - ((-258567/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos435o2_br_112).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum435o2_113 : ((4868201/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 113, cos435o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 113, cos435o2c k)
      = (∑ k ∈ Finset.Icc 11 112, cos435o2c k) + cos435o2c 113 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 112) (by norm_num) cos435o2c
    simpa using h
  have hprev := psum435o2_112
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos435o2c 113 - ((-154213/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos435o2_br_113).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum435o2_114 : ((133573/12500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 114, cos435o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 114, cos435o2c k)
      = (∑ k ∈ Finset.Icc 11 113, cos435o2c k) + cos435o2c 114 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 113) (by norm_num) cos435o2c
    simpa using h
  have hprev := psum435o2_113
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos435o2c 114 - ((474739/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos435o2_br_114).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum435o2_115 : ((2669061/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 115, cos435o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 115, cos435o2c k)
      = (∑ k ∈ Finset.Icc 11 114, cos435o2c k) + cos435o2c 115 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 114) (by norm_num) cos435o2c
    simpa using h
  have hprev := psum435o2_114
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos435o2c 115 - ((-2389/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos435o2_br_115).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum435o2_116 : ((243189/25000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 116, cos435o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 116, cos435o2c k)
      = (∑ k ∈ Finset.Icc 11 115, cos435o2c k) + cos435o2c 116 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 115) (by norm_num) cos435o2c
    simpa using h
  have hprev := psum435o2_115
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos435o2c 116 - ((-237161/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos435o2_br_116).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum435o2_117 : ((10306971/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 117, cos435o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 117, cos435o2c k)
      = (∑ k ∈ Finset.Icc 11 116, cos435o2c k) + cos435o2c 117 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 116) (by norm_num) cos435o2c
    simpa using h
  have hprev := psum435o2_116
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos435o2c 117 - ((579451/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos435o2_br_117).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum435o2_118 : ((2732461/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 118, cos435o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 118, cos435o2c k)
      = (∑ k ∈ Finset.Icc 11 117, cos435o2c k) + cos435o2c 118 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 117) (by norm_num) cos435o2c
    simpa using h
  have hprev := psum435o2_117
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos435o2c 118 - ((622913/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos435o2_br_118).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum435o2_119 : ((1251477/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 119, cos435o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 119, cos435o2c k)
      = (∑ k ∈ Finset.Icc 11 118, cos435o2c k) + cos435o2c 119 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 118) (by norm_num) cos435o2c
    simpa using h
  have hprev := psum435o2_118
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos435o2c 119 - ((-229497/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos435o2_br_119).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum435o2_120 : ((985393/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 120, cos435o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 120, cos435o2c k)
      = (∑ k ∈ Finset.Icc 11 119, cos435o2c k) + cos435o2c 120 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 119) (by norm_num) cos435o2c
    simpa using h
  have hprev := psum435o2_119
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos435o2c 120 - ((-78923/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos435o2_br_120).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum435o2_121 : ((10851027/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 121, cos435o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 121, cos435o2c k)
      = (∑ k ∈ Finset.Icc 11 120, cos435o2c k) + cos435o2c 121 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 120) (by norm_num) cos435o2c
    simpa using h
  have hprev := psum435o2_120
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos435o2c 121 - ((997137/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos435o2_br_121).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum435o2_122 : ((10560227/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 122, cos435o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 122, cos435o2c k)
      = (∑ k ∈ Finset.Icc 11 121, cos435o2c k) + cos435o2c 122 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 121) (by norm_num) cos435o2c
    simpa using h
  have hprev := psum435o2_121
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos435o2c 122 - ((-7269/25000 : ℚ) : ℝ) :=
    (abs_le.mp cos435o2_br_122).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum435o2_123 : ((9682481/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 123, cos435o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 123, cos435o2c k)
      = (∑ k ∈ Finset.Icc 11 122, cos435o2c k) + cos435o2c 123 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 122) (by norm_num) cos435o2c
    simpa using h
  have hprev := psum435o2_122
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos435o2c 123 - ((-438853/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos435o2_br_123).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum435o2_124 : ((2063809/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 124, cos435o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 124, cos435o2c k)
      = (∑ k ∈ Finset.Icc 11 123, cos435o2c k) + cos435o2c 124 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 123) (by norm_num) cos435o2c
    simpa using h
  have hprev := psum435o2_123
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos435o2c 124 - ((159151/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos435o2_br_124).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum435o2_125 : ((10966659/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 125, cos435o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 125, cos435o2c k)
      = (∑ k ∈ Finset.Icc 11 124, cos435o2c k) + cos435o2c 125 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 124) (by norm_num) cos435o2c
    simpa using h
  have hprev := psum435o2_124
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos435o2c 125 - ((323827/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos435o2_br_125).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum435o2_126 : ((10110051/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 126, cos435o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 126, cos435o2c k)
      = (∑ k ∈ Finset.Icc 11 125, cos435o2c k) + cos435o2c 126 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 125) (by norm_num) cos435o2c
    simpa using h
  have hprev := psum435o2_125
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos435o2c 126 - ((-107071/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos435o2_br_126).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum435o2_127 : ((9726447/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 127, cos435o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 127, cos435o2c k)
      = (∑ k ∈ Finset.Icc 11 126, cos435o2c k) + cos435o2c 127 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 126) (by norm_num) cos435o2c
    simpa using h
  have hprev := psum435o2_126
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos435o2c 127 - ((-95891/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos435o2_br_127).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum435o2_128 : ((668323/62500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 128, cos435o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 128, cos435o2c k)
      = (∑ k ∈ Finset.Icc 11 127, cos435o2c k) + cos435o2c 128 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 127) (by norm_num) cos435o2c
    simpa using h
  have hprev := psum435o2_127
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos435o2c 128 - ((966761/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos435o2_br_128).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum435o2_129 : ((5414711/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 129, cos435o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 129, cos435o2c k)
      = (∑ k ∈ Finset.Icc 11 128, cos435o2c k) + cos435o2c 129 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 128) (by norm_num) cos435o2c
    simpa using h
  have hprev := psum435o2_128
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos435o2c 129 - ((68147/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos435o2_br_129).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum435o2_130 : ((9829773/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 130, cos435o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 130, cos435o2c k)
      = (∑ k ∈ Finset.Icc 11 129, cos435o2c k) + cos435o2c 130 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 129) (by norm_num) cos435o2c
    simpa using h
  have hprev := psum435o2_129
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos435o2c 130 - ((-999609/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos435o2_br_130).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum435o2_131 : ((618599/62500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 131, cos435o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 131, cos435o2c k)
      = (∑ k ∈ Finset.Icc 11 130, cos435o2c k) + cos435o2c 131 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 130) (by norm_num) cos435o2c
    simpa using h
  have hprev := psum435o2_130
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos435o2c 131 - ((67851/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos435o2_br_131).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum435o2_132 : ((10886149/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 132, cos435o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 132, cos435o2c k)
      = (∑ k ∈ Finset.Icc 11 131, cos435o2c k) + cos435o2c 132 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 131) (by norm_num) cos435o2c
    simpa using h
  have hprev := psum435o2_131
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos435o2c 132 - ((197721/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos435o2_br_132).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum435o2_133 : ((10666097/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 133, cos435o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 133, cos435o2c k)
      = (∑ k ∈ Finset.Icc 11 132, cos435o2c k) + cos435o2c 133 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 132) (by norm_num) cos435o2c
    simpa using h
  have hprev := psum435o2_132
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos435o2c 133 - ((-55003/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos435o2_br_133).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum435o2_134 : ((970507/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 134, cos435o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 134, cos435o2c k)
      = (∑ k ∈ Finset.Icc 11 133, cos435o2c k) + cos435o2c 134 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 133) (by norm_num) cos435o2c
    simpa using h
  have hprev := psum435o2_133
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos435o2c 134 - ((-960987/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos435o2_br_134).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum435o2_135 : ((10025809/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 135, cos435o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 135, cos435o2c k)
      = (∑ k ∈ Finset.Icc 11 134, cos435o2c k) + cos435o2c 135 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 134) (by norm_num) cos435o2c
    simpa using h
  have hprev := psum435o2_134
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos435o2c 135 - ((320779/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos435o2_br_135).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum435o2_136 : ((10961339/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 136, cos435o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 136, cos435o2c k)
      = (∑ k ∈ Finset.Icc 11 135, cos435o2c k) + cos435o2c 136 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 135) (by norm_num) cos435o2c
    simpa using h
  have hprev := psum435o2_135
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos435o2c 136 - ((93557/100000 : ℚ) : ℝ) :=
    (abs_le.mp cos435o2_br_136).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum435o2_137 : ((10587077/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 137, cos435o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 137, cos435o2c k)
      = (∑ k ∈ Finset.Icc 11 136, cos435o2c k) + cos435o2c 137 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 136) (by norm_num) cos435o2c
    simpa using h
  have hprev := psum435o2_136
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos435o2c 137 - ((-187111/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos435o2_br_137).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum435o2_138 : ((9663877/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 138, cos435o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 138, cos435o2c k)
      = (∑ k ∈ Finset.Icc 11 137, cos435o2c k) + cos435o2c 138 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 137) (by norm_num) cos435o2c
    simpa using h
  have hprev := psum435o2_137
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos435o2c 138 - ((-23079/25000 : ℚ) : ℝ) :=
    (abs_le.mp cos435o2_br_138).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum435o2_139 : ((100479/10000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 139, cos435o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 139, cos435o2c k)
      = (∑ k ∈ Finset.Icc 11 138, cos435o2c k) + cos435o2c 139 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 138) (by norm_num) cos435o2c
    simpa using h
  have hprev := psum435o2_138
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos435o2c 139 - ((384063/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos435o2_br_139).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum435o2_140 : ((5487789/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 140, cos435o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 140, cos435o2c k)
      = (∑ k ∈ Finset.Icc 11 139, cos435o2c k) + cos435o2c 140 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 139) (by norm_num) cos435o2c
    simpa using h
  have hprev := psum435o2_139
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos435o2c 140 - ((463859/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos435o2_br_140).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum435o2_141 : ((5311733/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 141, cos435o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 141, cos435o2c k)
      = (∑ k ∈ Finset.Icc 11 140, cos435o2c k) + cos435o2c 141 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 140) (by norm_num) cos435o2c
    simpa using h
  have hprev := psum435o2_140
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos435o2c 141 - ((-44009/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos435o2_br_141).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum435o2_142 : ((302379/31250 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 142, cos435o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 142, cos435o2c k)
      = (∑ k ∈ Finset.Icc 11 141, cos435o2c k) + cos435o2c 142 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 141) (by norm_num) cos435o2c
    simpa using h
  have hprev := psum435o2_141
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos435o2c 142 - ((-473649/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos435o2_br_142).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum435o2_143 : ((4977007/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 143, cos435o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 143, cos435o2c k)
      = (∑ k ∈ Finset.Icc 11 142, cos435o2c k) + cos435o2c 143 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 142) (by norm_num) cos435o2c
    simpa using h
  have hprev := psum435o2_142
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos435o2c 143 - ((138963/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos435o2_br_143).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum435o2_144 : ((1092843/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 144, cos435o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 144, cos435o2c k)
      = (∑ k ∈ Finset.Icc 11 143, cos435o2c k) + cos435o2c 144 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 143) (by norm_num) cos435o2c
    simpa using h
  have hprev := psum435o2_143
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos435o2c 144 - ((121807/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos435o2_br_144).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum435o2_145 : ((5384081/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 145, cos435o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 145, cos435o2c k)
      = (∑ k ∈ Finset.Icc 11 144, cos435o2c k) + cos435o2c 145 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 144) (by norm_num) cos435o2c
    simpa using h
  have hprev := psum435o2_144
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos435o2c 145 - ((-40057/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos435o2_br_145).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum435o2_146 : ((9771731/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 146, cos435o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 146, cos435o2c k)
      = (∑ k ∈ Finset.Icc 11 145, cos435o2c k) + cos435o2c 146 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 145) (by norm_num) cos435o2c
    simpa using h
  have hprev := psum435o2_145
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos435o2c 146 - ((-996391/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos435o2_br_146).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum435o2_147 : ((9770509/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 147, cos435o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 147, cos435o2c k)
      = (∑ k ∈ Finset.Icc 11 146, cos435o2c k) + cos435o2c 147 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 146) (by norm_num) cos435o2c
    simpa using h
  have hprev := psum435o2_146
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos435o2c 147 - ((-591/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos435o2_br_147).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum435o2_148 : ((1076573/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 148, cos435o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 148, cos435o2c k)
      = (∑ k ∈ Finset.Icc 11 147, cos435o2c k) + cos435o2c 148 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 147) (by norm_num) cos435o2c
    simpa using h
  have hprev := psum435o2_147
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos435o2c 148 - ((995261/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos435o2_br_148).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum435o2_149 : ((10967811/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 149, cos435o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 149, cos435o2c k)
      = (∑ k ∈ Finset.Icc 11 148, cos435o2c k) + cos435o2c 149 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 148) (by norm_num) cos435o2c
    simpa using h
  have hprev := psum435o2_148
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos435o2c 149 - ((202121/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos435o2_br_149).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum435o2_150 : ((10018373/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 150, cos435o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 150, cos435o2c k)
      = (∑ k ∈ Finset.Icc 11 149, cos435o2c k) + cos435o2c 150 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 149) (by norm_num) cos435o2c
    simpa using h
  have hprev := psum435o2_149
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos435o2c 150 - ((-474699/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos435o2_br_150).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum435o2_151 : ((9587803/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 151, cos435o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 151, cos435o2c k)
      = (∑ k ∈ Finset.Icc 11 150, cos435o2c k) + cos435o2c 151 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 150) (by norm_num) cos435o2c
    simpa using h
  have hprev := psum435o2_150
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos435o2c 151 - ((-43053/100000 : ℚ) : ℝ) :=
    (abs_le.mp cos435o2_br_151).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum435o2_152 : ((10424103/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 152, cos435o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 152, cos435o2c k)
      = (∑ k ∈ Finset.Icc 11 151, cos435o2c k) + cos435o2c 152 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 151) (by norm_num) cos435o2c
    simpa using h
  have hprev := psum435o2_151
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos435o2c 152 - ((41817/50000 : ℚ) : ℝ) :=
    (abs_le.mp cos435o2_br_152).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum435o2_153 : ((5543519/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 153, cos435o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 153, cos435o2c k)
      = (∑ k ∈ Finset.Icc 11 152, cos435o2c k) + cos435o2c 153 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 152) (by norm_num) cos435o2c
    simpa using h
  have hprev := psum435o2_152
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos435o2c 153 - ((26519/40000 : ℚ) : ℝ) :=
    (abs_le.mp cos435o2_br_153).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum435o2_154 : ((2089759/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 154, cos435o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 154, cos435o2c k)
      = (∑ k ∈ Finset.Icc 11 153, cos435o2c k) + cos435o2c 154 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 153) (by norm_num) cos435o2c
    simpa using h
  have hprev := psum435o2_153
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos435o2c 154 - ((-638203/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos435o2_br_154).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum435o2_155 : ((958551/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 155, cos435o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 155, cos435o2c k)
      = (∑ k ∈ Finset.Icc 11 154, cos435o2c k) + cos435o2c 155 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 154) (by norm_num) cos435o2c
    simpa using h
  have hprev := psum435o2_154
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos435o2c 155 - ((-172649/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos435o2_br_155).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum435o2_156 : ((993499/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 156, cos435o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 156, cos435o2c k)
      = (∑ k ∈ Finset.Icc 11 155, cos435o2c k) + cos435o2c 156 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 155) (by norm_num) cos435o2c
    simpa using h
  have hprev := psum435o2_155
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos435o2c 156 - ((4369/12500 : ℚ) : ℝ) :=
    (abs_le.mp cos435o2_br_156).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum435o2_157 : ((5459747/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 157, cos435o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 157, cos435o2c k)
      = (∑ k ∈ Finset.Icc 11 156, cos435o2c k) + cos435o2c 157 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 156) (by norm_num) cos435o2c
    simpa using h
  have hprev := psum435o2_156
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos435o2c 157 - ((30767/31250 : ℚ) : ℝ) :=
    (abs_le.mp cos435o2_br_157).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum435o2_158 : ((2186651/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 158, cos435o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 158, cos435o2c k)
      = (∑ k ∈ Finset.Icc 11 157, cos435o2c k) + cos435o2c 158 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 157) (by norm_num) cos435o2c
    simpa using h
  have hprev := psum435o2_157
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos435o2c 158 - ((13801/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos435o2_br_158).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum435o2_159 : ((2488919/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 159, cos435o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 159, cos435o2c k)
      = (∑ k ∈ Finset.Icc 11 158, cos435o2c k) + cos435o2c 159 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 158) (by norm_num) cos435o2c
    simpa using h
  have hprev := psum435o2_158
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos435o2c 159 - ((-977539/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos435o2_br_159).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum435o2_160 : ((9548327/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 160, cos435o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 160, cos435o2c k)
      = (∑ k ∈ Finset.Icc 11 159, cos435o2c k) + cos435o2c 160 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 159) (by norm_num) cos435o2c
    simpa using h
  have hprev := psum435o2_159
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos435o2c 160 - ((-407309/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos435o2_br_160).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum435o2_161 : ((10353259/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 161, cos435o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 161, cos435o2c k)
      = (∑ k ∈ Finset.Icc 11 160, cos435o2c k) + cos435o2c 161 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 160) (by norm_num) cos435o2c
    simpa using h
  have hprev := psum435o2_160
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos435o2c 161 - ((201243/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos435o2_br_161).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum435o2_162 : ((5555271/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 162, cos435o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 162, cos435o2c k)
      = (∑ k ∈ Finset.Icc 11 161, cos435o2c k) + cos435o2c 162 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 161) (by norm_num) cos435o2c
    simpa using h
  have hprev := psum435o2_161
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos435o2c 162 - ((757323/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos435o2_br_162).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum435o2_163 : ((10649371/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 163, cos435o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 163, cos435o2c k)
      = (∑ k ∈ Finset.Icc 11 162, cos435o2c k) + cos435o2c 163 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 162) (by norm_num) cos435o2c
    simpa using h
  have hprev := psum435o2_162
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos435o2c 163 - ((-461131/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos435o2_br_163).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum435o2_164 : ((151214/15625 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 164, cos435o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 164, cos435o2c k)
      = (∑ k ∈ Finset.Icc 11 163, cos435o2c k) + cos435o2c 164 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 163) (by norm_num) cos435o2c
    simpa using h
  have hprev := psum435o2_163
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos435o2c 164 - ((-194327/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos435o2_br_164).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum435o2_165 : ((2416947/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 165, cos435o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 165, cos435o2c k)
      = (∑ k ∈ Finset.Icc 11 164, cos435o2c k) + cos435o2c 165 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 164) (by norm_num) cos435o2c
    simpa using h
  have hprev := psum435o2_164
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos435o2c 165 - ((-2467/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos435o2_br_165).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum435o2_166 : ((1329057/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 166, cos435o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 166, cos435o2c k)
      = (∑ k ∈ Finset.Icc 11 165, cos435o2c k) + cos435o2c 166 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 165) (by norm_num) cos435o2c
    simpa using h
  have hprev := psum435o2_165
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos435o2c 166 - ((241177/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos435o2_br_166).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum435o2_167 : ((5569377/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 167, cos435o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 167, cos435o2c k)
      = (∑ k ∈ Finset.Icc 11 166, cos435o2c k) + cos435o2c 167 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 166) (by norm_num) cos435o2c
    simpa using h
  have hprev := psum435o2_166
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos435o2c 167 - ((253169/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos435o2_br_167).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum435o2_168 : ((1044433/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 168, cos435o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 168, cos435o2c k)
      = (∑ k ∈ Finset.Icc 11 167, cos435o2c k) + cos435o2c 168 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 167) (by norm_num) cos435o2c
    simpa using h
  have hprev := psum435o2_167
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos435o2c 168 - ((-43399/62500 : ℚ) : ℝ) :=
    (abs_le.mp cos435o2_br_168).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum435o2_169 : ((1195103/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 169, cos435o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 169, cos435o2c k)
      = (∑ k ∈ Finset.Icc 11 168, cos435o2c k) + cos435o2c 169 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 168) (by norm_num) cos435o2c
    simpa using h
  have hprev := psum435o2_168
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos435o2c 169 - ((-441733/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos435o2_br_169).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum435o2_170 : ((2439857/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 170, cos435o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 170, cos435o2c k)
      = (∑ k ∈ Finset.Icc 11 169, cos435o2c k) + cos435o2c 170 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 169) (by norm_num) cos435o2c
    simpa using h
  have hprev := psum435o2_169
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos435o2c 170 - ((49661/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos435o2_br_170).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum435o2_171 : ((10754863/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 171, cos435o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 171, cos435o2c k)
      = (∑ k ∈ Finset.Icc 11 170, cos435o2c k) + cos435o2c 171 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 170) (by norm_num) cos435o2c
    simpa using h
  have hprev := psum435o2_170
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos435o2c 171 - ((39819/40000 : ℚ) : ℝ) :=
    (abs_le.mp cos435o2_br_171).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum435o2_172 : ((11142157/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 172, cos435o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 172, cos435o2c k)
      = (∑ k ∈ Finset.Icc 11 171, cos435o2c k) + cos435o2c 172 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 171) (by norm_num) cos435o2c
    simpa using h
  have hprev := psum435o2_171
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos435o2c 172 - ((193667/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos435o2_br_172).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum435o2_173 : ((2076447/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 173, cos435o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 173, cos435o2c k)
      = (∑ k ∈ Finset.Icc 11 172, cos435o2c k) + cos435o2c 173 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 172) (by norm_num) cos435o2c
    simpa using h
  have hprev := psum435o2_172
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos435o2c 173 - ((-379941/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos435o2_br_173).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum435o2_174 : ((1905511/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 174, cos435o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 174, cos435o2c k)
      = (∑ k ∈ Finset.Icc 11 173, cos435o2c k) + cos435o2c 174 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 173) (by norm_num) cos435o2c
    simpa using h
  have hprev := psum435o2_173
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos435o2c 174 - ((-10683/12500 : ℚ) : ℝ) :=
    (abs_le.mp cos435o2_br_174).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum435o2_175 : ((9747277/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 175, cos435o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 175, cos435o2c k)
      = (∑ k ∈ Finset.Icc 11 174, cos435o2c k) + cos435o2c 175 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 174) (by norm_num) cos435o2c
    simpa using h
  have hprev := psum435o2_174
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos435o2c 175 - ((109881/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos435o2_br_175).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum435o2_176 : ((10741203/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 176, cos435o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 176, cos435o2c k)
      = (∑ k ∈ Finset.Icc 11 175, cos435o2c k) + cos435o2c 176 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 175) (by norm_num) cos435o2c
    simpa using h
  have hprev := psum435o2_175
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos435o2c 176 - ((496983/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos435o2_br_176).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum435o2_177 : ((11174683/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 177, cos435o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 177, cos435o2c k)
      = (∑ k ∈ Finset.Icc 11 176, cos435o2c k) + cos435o2c 177 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 176) (by norm_num) cos435o2c
    simpa using h
  have hprev := psum435o2_176
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos435o2c 177 - ((5419/12500 : ℚ) : ℝ) :=
    (abs_le.mp cos435o2_br_177).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum435o2_178 : ((10473531/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 178, cos435o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 178, cos435o2c k)
      = (∑ k ∈ Finset.Icc 11 177, cos435o2c k) + cos435o2c 178 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 177) (by norm_num) cos435o2c
    simpa using h
  have hprev := psum435o2_177
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos435o2c 178 - ((-87639/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos435o2_br_178).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum435o2_179 : ((1195289/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 179, cos435o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 179, cos435o2c k)
      = (∑ k ∈ Finset.Icc 11 178, cos435o2c k) + cos435o2c 179 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 178) (by norm_num) cos435o2c
    simpa using h
  have hprev := psum435o2_178
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos435o2c 179 - ((-911179/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos435o2_br_179).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum435o2_180 : ((9627781/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 180, cos435o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 180, cos435o2c k)
      = (∑ k ∈ Finset.Icc 11 179, cos435o2c k) + cos435o2c 180 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 179) (by norm_num) cos435o2c
    simpa using h
  have hprev := psum435o2_179
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos435o2c 180 - ((65509/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos435o2_br_180).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum435o2_181 : ((2116601/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 181, cos435o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 181, cos435o2c k)
      = (∑ k ∈ Finset.Icc 11 180, cos435o2c k) + cos435o2c 181 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 180) (by norm_num) cos435o2c
    simpa using h
  have hprev := psum435o2_180
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos435o2c 181 - ((14926/15625 : ℚ) : ℝ) :=
    (abs_le.mp cos435o2_br_181).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum435o2_182 : ((11206069/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 182, cos435o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 182, cos435o2c k)
      = (∑ k ∈ Finset.Icc 11 181, cos435o2c k) + cos435o2c 182 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 181) (by norm_num) cos435o2c
    simpa using h
  have hprev := psum435o2_181
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos435o2c 182 - ((9736/15625 : ℚ) : ℝ) :=
    (abs_le.mp cos435o2_br_182).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum435o2_183 : ((5354971/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 183, cos435o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 183, cos435o2c k)
      = (∑ k ∈ Finset.Icc 11 182, cos435o2c k) + cos435o2c 183 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 182) (by norm_num) cos435o2c
    simpa using h
  have hprev := psum435o2_182
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos435o2c 183 - ((-496087/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos435o2_br_183).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum435o2_184 : ((971881/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 184, cos435o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 184, cos435o2c k)
      = (∑ k ∈ Finset.Icc 11 183, cos435o2c k) + cos435o2c 184 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 183) (by norm_num) cos435o2c
    simpa using h
  have hprev := psum435o2_183
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos435o2c 184 - ((-247773/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos435o2_br_184).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum435o2_185 : ((9463287/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 185, cos435o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 185, cos435o2c k)
      = (∑ k ∈ Finset.Icc 11 184, cos435o2c k) + cos435o2c 185 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 184) (by norm_num) cos435o2c
    simpa using h
  have hprev := psum435o2_184
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos435o2c 185 - ((-255483/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos435o2_br_185).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum435o2_186 : ((2563823/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 186, cos435o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 186, cos435o2c k)
      = (∑ k ∈ Finset.Icc 11 185, cos435o2c k) + cos435o2c 186 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 185) (by norm_num) cos435o2c
    simpa using h
  have hprev := psum435o2_185
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos435o2c 186 - ((158409/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos435o2_br_186).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum435o2_187 : ((2782049/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 187, cos435o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 187, cos435o2c k)
      = (∑ k ∈ Finset.Icc 11 186, cos435o2c k) + cos435o2c 187 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 186) (by norm_num) cos435o2c
    simpa using h
  have hprev := psum435o2_186
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos435o2c 187 - ((54559/62500 : ℚ) : ℝ) :=
    (abs_le.mp cos435o2_br_187).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum435o2_188 : ((11029529/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 188, cos435o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 188, cos435o2c k)
      = (∑ k ∈ Finset.Icc 11 187, cos435o2c k) + cos435o2c 188 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 187) (by norm_num) cos435o2c
    simpa using h
  have hprev := psum435o2_187
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos435o2c 188 - ((-98627/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos435o2_br_188).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum435o2_189 : ((10079673/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 189, cos435o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 189, cos435o2c k)
      = (∑ k ∈ Finset.Icc 11 188, cos435o2c k) + cos435o2c 189 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 188) (by norm_num) cos435o2c
    simpa using h
  have hprev := psum435o2_188
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos435o2c 189 - ((-118727/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos435o2_br_189).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum435o2_190 : ((470223/50000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 190, cos435o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 190, cos435o2c k)
      = (∑ k ∈ Finset.Icc 11 189, cos435o2c k) + cos435o2c 190 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 189) (by norm_num) cos435o2c
    simpa using h
  have hprev := psum435o2_189
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos435o2c 190 - ((-675173/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos435o2_br_190).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum435o2_191 : ((9794341/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 191, cos435o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 191, cos435o2c k)
      = (∑ k ∈ Finset.Icc 11 190, cos435o2c k) + cos435o2c 191 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 190) (by norm_num) cos435o2c
    simpa using h
  have hprev := psum435o2_190
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos435o2c 191 - ((389921/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos435o2_br_191).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum435o2_192 : ((5396853/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 192, cos435o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 192, cos435o2c k)
      = (∑ k ∈ Finset.Icc 11 191, cos435o2c k) + cos435o2c 192 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 191) (by norm_num) cos435o2c
    simpa using h
  have hprev := psum435o2_191
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos435o2c 192 - ((199881/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos435o2_br_192).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum435o2_193 : ((11251373/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 193, cos435o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 193, cos435o2c k)
      = (∑ k ∈ Finset.Icc 11 192, cos435o2c k) + cos435o2c 193 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 192) (by norm_num) cos435o2c
    simpa using h
  have hprev := psum435o2_192
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos435o2c 193 - ((457707/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos435o2_br_193).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum435o2_194 : ((5323621/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 194, cos435o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 194, cos435o2c k)
      = (∑ k ∈ Finset.Icc 11 193, cos435o2c k) + cos435o2c 194 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 193) (by norm_num) cos435o2c
    simpa using h
  have hprev := psum435o2_193
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos435o2c 194 - ((-604091/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos435o2_br_194).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum435o2_195 : ((1933273/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 195, cos435o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 195, cos435o2c k)
      = (∑ k ∈ Finset.Icc 11 194, cos435o2c k) + cos435o2c 195 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 194) (by norm_num) cos435o2c
    simpa using h
  have hprev := psum435o2_194
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos435o2c 195 - ((-980837/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos435o2_br_195).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum435o2_196 : ((470357/50000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 196, cos435o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 196, cos435o2c k)
      = (∑ k ∈ Finset.Icc 11 195, cos435o2c k) + cos435o2c 196 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 195) (by norm_num) cos435o2c
    simpa using h
  have hprev := psum435o2_195
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos435o2c 196 - ((-51837/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos435o2_br_196).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum435o2_197 : ((1269359/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 197, cos435o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 197, cos435o2c k)
      = (∑ k ∈ Finset.Icc 11 196, cos435o2c k) + cos435o2c 197 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 196) (by norm_num) cos435o2c
    simpa using h
  have hprev := psum435o2_196
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos435o2c 197 - ((186943/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos435o2_br_197).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum435o2_198 : ((11085277/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 198, cos435o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 198, cos435o2c k)
      = (∑ k ∈ Finset.Icc 11 197, cos435o2c k) + cos435o2c 198 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 197) (by norm_num) cos435o2c
    simpa using h
  have hprev := psum435o2_197
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos435o2c 198 - ((186089/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos435o2_br_198).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum435o2_199 : ((5592487/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 199, cos435o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 199, cos435o2c k)
      = (∑ k ∈ Finset.Icc 11 198, cos435o2c k) + cos435o2c 199 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 198) (by norm_num) cos435o2c
    simpa using h
  have hprev := psum435o2_198
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos435o2c 199 - ((99737/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos435o2_br_199).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum435o2_200 : ((2069747/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 200, cos435o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 200, cos435o2c k)
      = (∑ k ∈ Finset.Icc 11 199, cos435o2c k) + cos435o2c 200 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 199) (by norm_num) cos435o2c
    simpa using h
  have hprev := psum435o2_199
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos435o2c 200 - ((-836199/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos435o2_br_200).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum435o2_201 : ((9473193/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 201, cos435o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 201, cos435o2c k)
      = (∑ k ∈ Finset.Icc 11 200, cos435o2c k) + cos435o2c 201 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 200) (by norm_num) cos435o2c
    simpa using h
  have hprev := psum435o2_200
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos435o2c 201 - ((-437751/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos435o2_br_201).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum435o2_202 : ((4743033/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 202, cos435o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 202, cos435o2c k)
      = (∑ k ∈ Finset.Icc 11 201, cos435o2c k) + cos435o2c 202 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 201) (by norm_num) cos435o2c
    simpa using h
  have hprev := psum435o2_201
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos435o2c 202 - ((12913/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos435o2_br_202).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum435o2_203 : ((10371259/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 203, cos435o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 203, cos435o2c k)
      = (∑ k ∈ Finset.Icc 11 202, cos435o2c k) + cos435o2c 203 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 202) (by norm_num) cos435o2c
    simpa using h
  have hprev := psum435o2_202
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos435o2c 203 - ((885233/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos435o2_br_203).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum435o2_204 : ((2240987/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 204, cos435o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 204, cos435o2c k)
      = (∑ k ∈ Finset.Icc 11 203, cos435o2c k) + cos435o2c 204 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 203) (by norm_num) cos435o2c
    simpa using h
  have hprev := psum435o2_203
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos435o2c 204 - ((208429/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos435o2_br_204).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum435o2_205 : ((5563601/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 205, cos435o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 205, cos435o2c k)
      = (∑ k ∈ Finset.Icc 11 204, cos435o2c k) + cos435o2c 205 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 204) (by norm_num) cos435o2c
    simpa using h
  have hprev := psum435o2_204
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos435o2c 205 - ((-77693/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos435o2_br_205).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum435o2_206 : ((2044027/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 206, cos435o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 206, cos435o2c k)
      = (∑ k ∈ Finset.Icc 11 205, cos435o2c k) + cos435o2c 206 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 205) (by norm_num) cos435o2c
    simpa using h
  have hprev := psum435o2_205
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos435o2c 206 - ((-907027/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos435o2_br_206).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum435o2_207 : ((9405427/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 207, cos435o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 207, cos435o2c k)
      = (∑ k ∈ Finset.Icc 11 206, cos435o2c k) + cos435o2c 207 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 206) (by norm_num) cos435o2c
    simpa using h
  have hprev := psum435o2_206
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos435o2c 207 - ((-203667/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos435o2_br_207).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum435o2_208 : ((59383/6250 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 208, cos435o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 208, cos435o2c k)
      = (∑ k ∈ Finset.Icc 11 207, cos435o2c k) + cos435o2c 208 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 207) (by norm_num) cos435o2c
    simpa using h
  have hprev := psum435o2_207
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos435o2c 208 - ((95893/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos435o2_br_208).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum435o2_209 : ((2081909/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 209, cos435o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 209, cos435o2c k)
      = (∑ k ∈ Finset.Icc 11 208, cos435o2c k) + cos435o2c 209 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 208) (by norm_num) cos435o2c
    simpa using h
  have hprev := psum435o2_208
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos435o2c 209 - ((181661/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos435o2_br_209).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum435o2_210 : ((1123109/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 210, cos435o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 210, cos435o2c k)
      = (∑ k ∈ Finset.Icc 11 209, cos435o2c k) + cos435o2c 210 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 209) (by norm_num) cos435o2c
    simpa using h
  have hprev := psum435o2_209
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos435o2c 210 - ((164317/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos435o2_br_210).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum435o2_211 : ((2790509/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 211, cos435o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 211, cos435o2c k)
      = (∑ k ∈ Finset.Icc 11 210, cos435o2c k) + cos435o2c 211 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 210) (by norm_num) cos435o2c
    simpa using h
  have hprev := psum435o2_210
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos435o2c 211 - ((-34507/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos435o2_br_211).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum435o2_212 : ((10271957/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 212, cos435o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 212, cos435o2c k)
      = (∑ k ∈ Finset.Icc 11 211, cos435o2c k) + cos435o2c 212 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 211) (by norm_num) cos435o2c
    simpa using h
  have hprev := psum435o2_211
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos435o2c 212 - ((-890039/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos435o2_br_212).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum435o2_213 : ((235487/25000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 213, cos435o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 213, cos435o2c k)
      = (∑ k ∈ Finset.Icc 11 212, cos435o2c k) + cos435o2c 213 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 212) (by norm_num) cos435o2c
    simpa using h
  have hprev := psum435o2_212
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos435o2c 213 - ((-852437/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos435o2_br_213).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum435o2_214 : ((235439/25000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 214, cos435o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 214, cos435o2c k)
      = (∑ k ∈ Finset.Icc 11 213, cos435o2c k) + cos435o2c 214 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 213) (by norm_num) cos435o2c
    simpa using h
  have hprev := psum435o2_213
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos435o2c 214 - ((-47/25000 : ℚ) : ℝ) :=
    (abs_le.mp cos435o2_br_214).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum435o2_215 : ((1026547/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 215, cos435o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 215, cos435o2c k)
      = (∑ k ∈ Finset.Icc 11 214, cos435o2c k) + cos435o2c 215 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 214) (by norm_num) cos435o2c
    simpa using h
  have hprev := psum435o2_214
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos435o2c 215 - ((16959/20000 : ℚ) : ℝ) :=
    (abs_le.mp cos435o2_br_215).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum435o2_216 : ((5582809/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 216, cos435o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 216, cos435o2c k)
      = (∑ k ∈ Finset.Icc 11 215, cos435o2c k) + cos435o2c 216 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 215) (by norm_num) cos435o2c
    simpa using h
  have hprev := psum435o2_215
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos435o2c 216 - ((225047/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos435o2_br_216).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum435o2_217 : ((11280911/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 217, cos435o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 217, cos435o2c k)
      = (∑ k ∈ Finset.Icc 11 216, cos435o2c k) + cos435o2c 217 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 216) (by norm_num) cos435o2c
    simpa using h
  have hprev := psum435o2_216
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos435o2c 217 - ((115333/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos435o2_br_217).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum435o2_218 : ((1050733/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 218, cos435o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 218, cos435o2c k)
      = (∑ k ∈ Finset.Icc 11 217, cos435o2c k) + cos435o2c 218 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 217) (by norm_num) cos435o2c
    simpa using h
  have hprev := psum435o2_217
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos435o2c 218 - ((-773541/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos435o2_br_218).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum435o2_219 : ((4777333/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 219, cos435o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 219, cos435o2c k)
      = (∑ k ∈ Finset.Icc 11 218, cos435o2c k) + cos435o2c 219 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 218) (by norm_num) cos435o2c
    simpa using h
  have hprev := psum435o2_218
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos435o2c 219 - ((-59539/62500 : ℚ) : ℝ) :=
    (abs_le.mp cos435o2_br_219).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum435o2_220 : ((4643531/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 220, cos435o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 220, cos435o2c k)
      = (∑ k ∈ Finset.Icc 11 219, cos435o2c k) + cos435o2c 220 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 219) (by norm_num) cos435o2c
    simpa using h
  have hprev := psum435o2_219
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos435o2c 220 - ((-66891/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos435o2_br_220).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum435o2_221 : ((9943049/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 221, cos435o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 221, cos435o2c k)
      = (∑ k ∈ Finset.Icc 11 220, cos435o2c k) + cos435o2c 221 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 220) (by norm_num) cos435o2c
    simpa using h
  have hprev := psum435o2_220
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos435o2c 221 - ((656027/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos435o2_br_221).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum435o2_222 : ((10934997/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 222, cos435o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 222, cos435o2c k)
      = (∑ k ∈ Finset.Icc 11 221, cos435o2c k) + cos435o2c 222 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 221) (by norm_num) cos435o2c
    simpa using h
  have hprev := psum435o2_221
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos435o2c 222 - ((247997/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos435o2_br_222).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum435o2_223 : ((11384803/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 223, cos435o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 223, cos435o2c k)
      = (∑ k ∈ Finset.Icc 11 222, cos435o2c k) + cos435o2c 223 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 222) (by norm_num) cos435o2c
    simpa using h
  have hprev := psum435o2_222
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos435o2c 223 - ((224923/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos435o2_br_223).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum435o2_224 : ((2179917/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 224, cos435o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 224, cos435o2c k)
      = (∑ k ∈ Finset.Icc 11 223, cos435o2c k) + cos435o2c 224 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 223) (by norm_num) cos435o2c
    simpa using h
  have hprev := psum435o2_223
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos435o2c 224 - ((-242589/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos435o2_br_224).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum435o2_225 : ((2476023/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 225, cos435o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 225, cos435o2c k)
      = (∑ k ∈ Finset.Icc 11 224, cos435o2c k) + cos435o2c 225 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 224) (by norm_num) cos435o2c
    simpa using h
  have hprev := psum435o2_224
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos435o2c 225 - ((-995453/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos435o2_br_225).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum435o2_226 : ((9258551/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 226, cos435o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 226, cos435o2c k)
      = (∑ k ∈ Finset.Icc 11 225, cos435o2c k) + cos435o2c 226 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 225) (by norm_num) cos435o2c
    simpa using h
  have hprev := psum435o2_225
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos435o2c 226 - ((-645501/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos435o2_br_226).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum435o2_227 : ((9514233/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 227, cos435o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 227, cos435o2c k)
      = (∑ k ∈ Finset.Icc 11 226, cos435o2c k) + cos435o2c 227 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 226) (by norm_num) cos435o2c
    simpa using h
  have hprev := psum435o2_226
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos435o2c 227 - ((127861/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos435o2_br_227).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum435o2_228 : ((2612859/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 228, cos435o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 228, cos435o2c k)
      = (∑ k ∈ Finset.Icc 11 227, cos435o2c k) + cos435o2c 228 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 227) (by norm_num) cos435o2c
    simpa using h
  have hprev := psum435o2_227
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos435o2c 228 - ((937243/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos435o2_br_228).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum435o2_229 : ((11279147/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 229, cos435o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 229, cos435o2c k)
      = (∑ k ∈ Finset.Icc 11 228, cos435o2c k) + cos435o2c 229 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 228) (by norm_num) cos435o2c
    simpa using h
  have hprev := psum435o2_228
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos435o2c 229 - ((827751/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos435o2_br_229).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum435o2_230 : ((11306479/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 230, cos435o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 230, cos435o2c k)
      = (∑ k ∈ Finset.Icc 11 229, cos435o2c k) + cos435o2c 230 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 229) (by norm_num) cos435o2c
    simpa using h
  have hprev := psum435o2_229
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos435o2c 230 - ((6843/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos435o2_br_230).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum435o2_231 : ((10513129/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 231, cos435o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 231, cos435o2c k)
      = (∑ k ∈ Finset.Icc 11 230, cos435o2c k) + cos435o2c 231 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 230) (by norm_num) cos435o2c
    simpa using h
  have hprev := psum435o2_230
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos435o2c 231 - ((-79331/100000 : ℚ) : ℝ) :=
    (abs_le.mp cos435o2_br_231).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum435o2_232 : ((9553411/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 232, cos435o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 232, cos435o2c k)
      = (∑ k ∈ Finset.Icc 11 231, cos435o2c k) + cos435o2c 232 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 231) (by norm_num) cos435o2c
    simpa using h
  have hprev := psum435o2_231
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos435o2c 232 - ((-479839/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos435o2_br_232).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum435o2_233 : ((2302533/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 233, cos435o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 233, cos435o2c k)
      = (∑ k ∈ Finset.Icc 11 232, cos435o2c k) + cos435o2c 233 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 232) (by norm_num) cos435o2c
    simpa using h
  have hprev := psum435o2_232
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos435o2c 233 - ((-343239/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos435o2_br_233).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum435o2_234 : ((1951811/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 234, cos435o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 234, cos435o2c k)
      = (∑ k ∈ Finset.Icc 11 233, cos435o2c k) + cos435o2c 234 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 233) (by norm_num) cos435o2c
    simpa using h
  have hprev := psum435o2_233
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos435o2c 234 - ((548963/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos435o2_br_234).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum435o2_235 : ((10757083/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 235, cos435o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 235, cos435o2c k)
      = (∑ k ∈ Finset.Icc 11 234, cos435o2c k) + cos435o2c 235 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 234) (by norm_num) cos435o2c
    simpa using h
  have hprev := psum435o2_234
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos435o2c 235 - ((249517/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos435o2_br_235).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum435o2_236 : ((356513/31250 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 236, cos435o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 236, cos435o2c k)
      = (∑ k ∈ Finset.Icc 11 235, cos435o2c k) + cos435o2c 236 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 235) (by norm_num) cos435o2c
    simpa using h
  have hprev := psum435o2_235
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos435o2c 236 - ((651373/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos435o2_br_236).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum435o2_237 : ((11199659/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 237, cos435o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 237, cos435o2c k)
      = (∑ k ∈ Finset.Icc 11 236, cos435o2c k) + cos435o2c 237 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 236) (by norm_num) cos435o2c
    simpa using h
  have hprev := psum435o2_236
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos435o2c 237 - ((-208717/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos435o2_br_237).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum435o2_238 : ((10296901/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 238, cos435o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 238, cos435o2c k)
      = (∑ k ∈ Finset.Icc 11 237, cos435o2c k) + cos435o2c 238 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 237) (by norm_num) cos435o2c
    simpa using h
  have hprev := psum435o2_237
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos435o2c 238 - ((-451359/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos435o2_br_238).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum435o2_239 : ((9404031/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 239, cos435o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 239, cos435o2c k)
      = (∑ k ∈ Finset.Icc 11 238, cos435o2c k) + cos435o2c 239 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 238) (by norm_num) cos435o2c
    simpa using h
  have hprev := psum435o2_238
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos435o2c 239 - ((-89283/100000 : ℚ) : ℝ) :=
    (abs_le.mp cos435o2_br_239).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum435o2_240 : ((143903/15625 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 240, cos435o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 240, cos435o2c k)
      = (∑ k ∈ Finset.Icc 11 239, cos435o2c k) + cos435o2c 240 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 239) (by norm_num) cos435o2c
    simpa using h
  have hprev := psum435o2_239
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos435o2c 240 - ((-194199/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos435o2_br_240).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum435o2_241 : ((986077/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 241, cos435o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 241, cos435o2c k)
      = (∑ k ∈ Finset.Icc 11 240, cos435o2c k) + cos435o2c 241 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 240) (by norm_num) cos435o2c
    simpa using h
  have hprev := psum435o2_240
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos435o2c 241 - ((325509/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos435o2_br_241).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum435o2_242 : ((10859979/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 242, cos435o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 242, cos435o2c k)
      = (∑ k ∈ Finset.Icc 11 241, cos435o2c k) + cos435o2c 242 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 241) (by norm_num) cos435o2c
    simpa using h
  have hprev := psum435o2_241
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos435o2c 242 - ((999249/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos435o2_br_242).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum435o2_243 : ((11453229/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 243, cos435o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 243, cos435o2c k)
      = (∑ k ∈ Finset.Icc 11 242, cos435o2c k) + cos435o2c 243 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 242) (by norm_num) cos435o2c
    simpa using h
  have hprev := psum435o2_242
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos435o2c 243 - ((59329/100000 : ℚ) : ℝ) :=
    (abs_le.mp cos435o2_br_243).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum435o2_244 : ((2239591/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 244, cos435o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 244, cos435o2c k)
      = (∑ k ∈ Finset.Icc 11 243, cos435o2c k) + cos435o2c 244 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 243) (by norm_num) cos435o2c
    simpa using h
  have hprev := psum435o2_243
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos435o2c 244 - ((-127617/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos435o2_br_244).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum435o2_245 : ((321441/31250 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 245, cos435o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 245, cos435o2c k)
      = (∑ k ∈ Finset.Icc 11 244, cos435o2c k) + cos435o2c 245 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 244) (by norm_num) cos435o2c
    simpa using h
  have hprev := psum435o2_244
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos435o2c 245 - ((-911803/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos435o2_br_245).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum435o2_246 : ((9391271/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 246, cos435o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 246, cos435o2c k)
      = (∑ k ∈ Finset.Icc 11 245, cos435o2c k) + cos435o2c 246 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 245) (by norm_num) cos435o2c
    simpa using h
  have hprev := psum435o2_245
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos435o2c 246 - ((-894801/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos435o2_br_246).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum435o2_247 : ((9167509/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 247, cos435o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 247, cos435o2c k)
      = (∑ k ∈ Finset.Icc 11 246, cos435o2c k) + cos435o2c 247 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 246) (by norm_num) cos435o2c
    simpa using h
  have hprev := psum435o2_246
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos435o2c 247 - ((-111861/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos435o2_br_247).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum435o2_248 : ((1955033/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 248, cos435o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 248, cos435o2c k)
      = (∑ k ∈ Finset.Icc 11 247, cos435o2c k) + cos435o2c 248 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 247) (by norm_num) cos435o2c
    simpa using h
  have hprev := psum435o2_247
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos435o2c 248 - ((37981/62500 : ℚ) : ℝ) :=
    (abs_le.mp cos435o2_br_248).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum435o2_249 : ((5387113/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 249, cos435o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 249, cos435o2c k)
      = (∑ k ∈ Finset.Icc 11 248, cos435o2c k) + cos435o2c 249 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 248) (by norm_num) cos435o2c
    simpa using h
  have hprev := psum435o2_248
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos435o2c 249 - ((999101/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos435o2_br_249).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum435o2_250 : ((2862383/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 250, cos435o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 250, cos435o2c k)
      = (∑ k ∈ Finset.Icc 11 249, cos435o2c k) + cos435o2c 250 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 249) (by norm_num) cos435o2c
    simpa using h
  have hprev := psum435o2_249
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos435o2c 250 - ((337673/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos435o2_br_250).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

set_option maxHeartbeats 3200000 in
/-- **The Abel floor at `t = 435/2`.** -/
theorem psum435o2_floor : ∀ j : ℕ, 11 ≤ j → j ≤ 250 →
    ((0 : ℚ) : ℝ) ≤ ∑ k ∈ Finset.Icc 11 j, cos435o2c k := by
  intro j hj1 hj2
  interval_cases j
  · exact le_trans (by norm_num) psum435o2_11
  · exact le_trans (by norm_num) psum435o2_12
  · exact le_trans (by norm_num) psum435o2_13
  · exact le_trans (by norm_num) psum435o2_14
  · exact le_trans (by norm_num) psum435o2_15
  · exact le_trans (by norm_num) psum435o2_16
  · exact le_trans (by norm_num) psum435o2_17
  · exact le_trans (by norm_num) psum435o2_18
  · exact le_trans (by norm_num) psum435o2_19
  · exact le_trans (by norm_num) psum435o2_20
  · exact le_trans (by norm_num) psum435o2_21
  · exact le_trans (by norm_num) psum435o2_22
  · exact le_trans (by norm_num) psum435o2_23
  · exact le_trans (by norm_num) psum435o2_24
  · exact le_trans (by norm_num) psum435o2_25
  · exact le_trans (by norm_num) psum435o2_26
  · exact le_trans (by norm_num) psum435o2_27
  · exact le_trans (by norm_num) psum435o2_28
  · exact le_trans (by norm_num) psum435o2_29
  · exact le_trans (by norm_num) psum435o2_30
  · exact le_trans (by norm_num) psum435o2_31
  · exact le_trans (by norm_num) psum435o2_32
  · exact le_trans (by norm_num) psum435o2_33
  · exact le_trans (by norm_num) psum435o2_34
  · exact le_trans (by norm_num) psum435o2_35
  · exact le_trans (by norm_num) psum435o2_36
  · exact le_trans (by norm_num) psum435o2_37
  · exact le_trans (by norm_num) psum435o2_38
  · exact le_trans (by norm_num) psum435o2_39
  · exact le_trans (by norm_num) psum435o2_40
  · exact le_trans (by norm_num) psum435o2_41
  · exact le_trans (by norm_num) psum435o2_42
  · exact le_trans (by norm_num) psum435o2_43
  · exact le_trans (by norm_num) psum435o2_44
  · exact le_trans (by norm_num) psum435o2_45
  · exact le_trans (by norm_num) psum435o2_46
  · exact le_trans (by norm_num) psum435o2_47
  · exact le_trans (by norm_num) psum435o2_48
  · exact le_trans (by norm_num) psum435o2_49
  · exact le_trans (by norm_num) psum435o2_50
  · exact le_trans (by norm_num) psum435o2_51
  · exact le_trans (by norm_num) psum435o2_52
  · exact le_trans (by norm_num) psum435o2_53
  · exact le_trans (by norm_num) psum435o2_54
  · exact le_trans (by norm_num) psum435o2_55
  · exact le_trans (by norm_num) psum435o2_56
  · exact le_trans (by norm_num) psum435o2_57
  · exact le_trans (by norm_num) psum435o2_58
  · exact le_trans (by norm_num) psum435o2_59
  · exact le_trans (by norm_num) psum435o2_60
  · exact le_trans (by norm_num) psum435o2_61
  · exact le_trans (by norm_num) psum435o2_62
  · exact le_trans (by norm_num) psum435o2_63
  · exact le_trans (by norm_num) psum435o2_64
  · exact le_trans (by norm_num) psum435o2_65
  · exact le_trans (by norm_num) psum435o2_66
  · exact le_trans (by norm_num) psum435o2_67
  · exact le_trans (by norm_num) psum435o2_68
  · exact le_trans (by norm_num) psum435o2_69
  · exact le_trans (by norm_num) psum435o2_70
  · exact le_trans (by norm_num) psum435o2_71
  · exact le_trans (by norm_num) psum435o2_72
  · exact le_trans (by norm_num) psum435o2_73
  · exact le_trans (by norm_num) psum435o2_74
  · exact le_trans (by norm_num) psum435o2_75
  · exact le_trans (by norm_num) psum435o2_76
  · exact le_trans (by norm_num) psum435o2_77
  · exact le_trans (by norm_num) psum435o2_78
  · exact le_trans (by norm_num) psum435o2_79
  · exact le_trans (by norm_num) psum435o2_80
  · exact le_trans (by norm_num) psum435o2_81
  · exact le_trans (by norm_num) psum435o2_82
  · exact le_trans (by norm_num) psum435o2_83
  · exact le_trans (by norm_num) psum435o2_84
  · exact le_trans (by norm_num) psum435o2_85
  · exact le_trans (by norm_num) psum435o2_86
  · exact le_trans (by norm_num) psum435o2_87
  · exact le_trans (by norm_num) psum435o2_88
  · exact le_trans (by norm_num) psum435o2_89
  · exact le_trans (by norm_num) psum435o2_90
  · exact le_trans (by norm_num) psum435o2_91
  · exact le_trans (by norm_num) psum435o2_92
  · exact le_trans (by norm_num) psum435o2_93
  · exact le_trans (by norm_num) psum435o2_94
  · exact le_trans (by norm_num) psum435o2_95
  · exact le_trans (by norm_num) psum435o2_96
  · exact le_trans (by norm_num) psum435o2_97
  · exact le_trans (by norm_num) psum435o2_98
  · exact le_trans (by norm_num) psum435o2_99
  · exact le_trans (by norm_num) psum435o2_100
  · exact le_trans (by norm_num) psum435o2_101
  · exact le_trans (by norm_num) psum435o2_102
  · exact le_trans (by norm_num) psum435o2_103
  · exact le_trans (by norm_num) psum435o2_104
  · exact le_trans (by norm_num) psum435o2_105
  · exact le_trans (by norm_num) psum435o2_106
  · exact le_trans (by norm_num) psum435o2_107
  · exact le_trans (by norm_num) psum435o2_108
  · exact le_trans (by norm_num) psum435o2_109
  · exact le_trans (by norm_num) psum435o2_110
  · exact le_trans (by norm_num) psum435o2_111
  · exact le_trans (by norm_num) psum435o2_112
  · exact le_trans (by norm_num) psum435o2_113
  · exact le_trans (by norm_num) psum435o2_114
  · exact le_trans (by norm_num) psum435o2_115
  · exact le_trans (by norm_num) psum435o2_116
  · exact le_trans (by norm_num) psum435o2_117
  · exact le_trans (by norm_num) psum435o2_118
  · exact le_trans (by norm_num) psum435o2_119
  · exact le_trans (by norm_num) psum435o2_120
  · exact le_trans (by norm_num) psum435o2_121
  · exact le_trans (by norm_num) psum435o2_122
  · exact le_trans (by norm_num) psum435o2_123
  · exact le_trans (by norm_num) psum435o2_124
  · exact le_trans (by norm_num) psum435o2_125
  · exact le_trans (by norm_num) psum435o2_126
  · exact le_trans (by norm_num) psum435o2_127
  · exact le_trans (by norm_num) psum435o2_128
  · exact le_trans (by norm_num) psum435o2_129
  · exact le_trans (by norm_num) psum435o2_130
  · exact le_trans (by norm_num) psum435o2_131
  · exact le_trans (by norm_num) psum435o2_132
  · exact le_trans (by norm_num) psum435o2_133
  · exact le_trans (by norm_num) psum435o2_134
  · exact le_trans (by norm_num) psum435o2_135
  · exact le_trans (by norm_num) psum435o2_136
  · exact le_trans (by norm_num) psum435o2_137
  · exact le_trans (by norm_num) psum435o2_138
  · exact le_trans (by norm_num) psum435o2_139
  · exact le_trans (by norm_num) psum435o2_140
  · exact le_trans (by norm_num) psum435o2_141
  · exact le_trans (by norm_num) psum435o2_142
  · exact le_trans (by norm_num) psum435o2_143
  · exact le_trans (by norm_num) psum435o2_144
  · exact le_trans (by norm_num) psum435o2_145
  · exact le_trans (by norm_num) psum435o2_146
  · exact le_trans (by norm_num) psum435o2_147
  · exact le_trans (by norm_num) psum435o2_148
  · exact le_trans (by norm_num) psum435o2_149
  · exact le_trans (by norm_num) psum435o2_150
  · exact le_trans (by norm_num) psum435o2_151
  · exact le_trans (by norm_num) psum435o2_152
  · exact le_trans (by norm_num) psum435o2_153
  · exact le_trans (by norm_num) psum435o2_154
  · exact le_trans (by norm_num) psum435o2_155
  · exact le_trans (by norm_num) psum435o2_156
  · exact le_trans (by norm_num) psum435o2_157
  · exact le_trans (by norm_num) psum435o2_158
  · exact le_trans (by norm_num) psum435o2_159
  · exact le_trans (by norm_num) psum435o2_160
  · exact le_trans (by norm_num) psum435o2_161
  · exact le_trans (by norm_num) psum435o2_162
  · exact le_trans (by norm_num) psum435o2_163
  · exact le_trans (by norm_num) psum435o2_164
  · exact le_trans (by norm_num) psum435o2_165
  · exact le_trans (by norm_num) psum435o2_166
  · exact le_trans (by norm_num) psum435o2_167
  · exact le_trans (by norm_num) psum435o2_168
  · exact le_trans (by norm_num) psum435o2_169
  · exact le_trans (by norm_num) psum435o2_170
  · exact le_trans (by norm_num) psum435o2_171
  · exact le_trans (by norm_num) psum435o2_172
  · exact le_trans (by norm_num) psum435o2_173
  · exact le_trans (by norm_num) psum435o2_174
  · exact le_trans (by norm_num) psum435o2_175
  · exact le_trans (by norm_num) psum435o2_176
  · exact le_trans (by norm_num) psum435o2_177
  · exact le_trans (by norm_num) psum435o2_178
  · exact le_trans (by norm_num) psum435o2_179
  · exact le_trans (by norm_num) psum435o2_180
  · exact le_trans (by norm_num) psum435o2_181
  · exact le_trans (by norm_num) psum435o2_182
  · exact le_trans (by norm_num) psum435o2_183
  · exact le_trans (by norm_num) psum435o2_184
  · exact le_trans (by norm_num) psum435o2_185
  · exact le_trans (by norm_num) psum435o2_186
  · exact le_trans (by norm_num) psum435o2_187
  · exact le_trans (by norm_num) psum435o2_188
  · exact le_trans (by norm_num) psum435o2_189
  · exact le_trans (by norm_num) psum435o2_190
  · exact le_trans (by norm_num) psum435o2_191
  · exact le_trans (by norm_num) psum435o2_192
  · exact le_trans (by norm_num) psum435o2_193
  · exact le_trans (by norm_num) psum435o2_194
  · exact le_trans (by norm_num) psum435o2_195
  · exact le_trans (by norm_num) psum435o2_196
  · exact le_trans (by norm_num) psum435o2_197
  · exact le_trans (by norm_num) psum435o2_198
  · exact le_trans (by norm_num) psum435o2_199
  · exact le_trans (by norm_num) psum435o2_200
  · exact le_trans (by norm_num) psum435o2_201
  · exact le_trans (by norm_num) psum435o2_202
  · exact le_trans (by norm_num) psum435o2_203
  · exact le_trans (by norm_num) psum435o2_204
  · exact le_trans (by norm_num) psum435o2_205
  · exact le_trans (by norm_num) psum435o2_206
  · exact le_trans (by norm_num) psum435o2_207
  · exact le_trans (by norm_num) psum435o2_208
  · exact le_trans (by norm_num) psum435o2_209
  · exact le_trans (by norm_num) psum435o2_210
  · exact le_trans (by norm_num) psum435o2_211
  · exact le_trans (by norm_num) psum435o2_212
  · exact le_trans (by norm_num) psum435o2_213
  · exact le_trans (by norm_num) psum435o2_214
  · exact le_trans (by norm_num) psum435o2_215
  · exact le_trans (by norm_num) psum435o2_216
  · exact le_trans (by norm_num) psum435o2_217
  · exact le_trans (by norm_num) psum435o2_218
  · exact le_trans (by norm_num) psum435o2_219
  · exact le_trans (by norm_num) psum435o2_220
  · exact le_trans (by norm_num) psum435o2_221
  · exact le_trans (by norm_num) psum435o2_222
  · exact le_trans (by norm_num) psum435o2_223
  · exact le_trans (by norm_num) psum435o2_224
  · exact le_trans (by norm_num) psum435o2_225
  · exact le_trans (by norm_num) psum435o2_226
  · exact le_trans (by norm_num) psum435o2_227
  · exact le_trans (by norm_num) psum435o2_228
  · exact le_trans (by norm_num) psum435o2_229
  · exact le_trans (by norm_num) psum435o2_230
  · exact le_trans (by norm_num) psum435o2_231
  · exact le_trans (by norm_num) psum435o2_232
  · exact le_trans (by norm_num) psum435o2_233
  · exact le_trans (by norm_num) psum435o2_234
  · exact le_trans (by norm_num) psum435o2_235
  · exact le_trans (by norm_num) psum435o2_236
  · exact le_trans (by norm_num) psum435o2_237
  · exact le_trans (by norm_num) psum435o2_238
  · exact le_trans (by norm_num) psum435o2_239
  · exact le_trans (by norm_num) psum435o2_240
  · exact le_trans (by norm_num) psum435o2_241
  · exact le_trans (by norm_num) psum435o2_242
  · exact le_trans (by norm_num) psum435o2_243
  · exact le_trans (by norm_num) psum435o2_244
  · exact le_trans (by norm_num) psum435o2_245
  · exact le_trans (by norm_num) psum435o2_246
  · exact le_trans (by norm_num) psum435o2_247
  · exact le_trans (by norm_num) psum435o2_248
  · exact le_trans (by norm_num) psum435o2_249
  · exact le_trans (by norm_num) psum435o2_250

end CriticalLinePhasor.DVP

section AxiomAudit
#print axioms CriticalLinePhasor.DVP.psum435o2_floor
#print axioms CriticalLinePhasor.DVP.psum435o2_250
end AxiomAudit
