import RequestProject.DVPCos309o2Table

/-!
# The cosine partial-sum floor, `t = 309/2`
-/

open Finset

noncomputable section

namespace CriticalLinePhasor.DVP

/-- The cosine sequence of the `t = 309/2` segment certificate. -/
def cos309o2c (n : ℕ) : ℝ := Real.cos (((309:ℕ):ℝ) * (Real.log n / 2))

theorem psum309o2_11 : ((972911/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 11, cos309o2c k := by
  rw [Finset.Icc_self, Finset.sum_singleton]
  have h : -((1/25000 : ℚ) : ℝ) ≤ cos309o2c 11 - ((972951/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos309o2_br_11).1
  push_cast at h ⊢
  linarith

theorem psum309o2_12 : ((1772707/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 12, cos309o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 12, cos309o2c k)
      = (∑ k ∈ Finset.Icc 11 11, cos309o2c k) + cos309o2c 12 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 11) (by norm_num) cos309o2c
    simpa using h
  have hprev := psum309o2_11
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos309o2c 12 - ((199959/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos309o2_br_12).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum309o2_13 : ((668927/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 13, cos309o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 13, cos309o2c k)
      = (∑ k ∈ Finset.Icc 11 12, cos309o2c k) + cos309o2c 13 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 12) (by norm_num) cos309o2c
    simpa using h
  have hprev := psum309o2_12
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos309o2c 13 - ((903041/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos309o2_br_13).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum309o2_14 : ((172891/50000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 14, cos309o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 14, cos309o2c k)
      = (∑ k ∈ Finset.Icc 11 13, cos309o2c k) + cos309o2c 14 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 13) (by norm_num) cos309o2c
    simpa using h
  have hprev := psum309o2_13
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos309o2c 14 - ((97769/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos309o2_br_14).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum309o2_15 : ((2611557/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 15, cos309o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 15, cos309o2c k)
      = (∑ k ∈ Finset.Icc 11 14, cos309o2c k) + cos309o2c 15 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 14) (by norm_num) cos309o2c
    simpa using h
  have hprev := psum309o2_14
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos309o2c 15 - ((-846223/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos309o2_br_15).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum309o2_16 : ((1528823/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 16, cos309o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 16, cos309o2c k)
      = (∑ k ∈ Finset.Icc 11 15, cos309o2c k) + cos309o2c 16 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 15) (by norm_num) cos309o2c
    simpa using h
  have hprev := psum309o2_15
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos309o2c 16 - ((446129/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos309o2_br_16).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum309o2_17 : ((640027/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 17, cos309o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 17, cos309o2c k)
      = (∑ k ∈ Finset.Icc 11 16, cos309o2c k) + cos309o2c 17 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 16) (by norm_num) cos309o2c
    simpa using h
  have hprev := psum309o2_16
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos309o2c 17 - ((-248749/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos309o2_br_17).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum309o2_18 : ((1728883/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 18, cos309o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 18, cos309o2c k)
      = (∑ k ∈ Finset.Icc 11 17, cos309o2c k) + cos309o2c 18 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 17) (by norm_num) cos309o2c
    simpa using h
  have hprev := psum309o2_17
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos309o2c 18 - ((448849/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos309o2_br_18).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum309o2_19 : ((132051/50000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 19, cos309o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 19, cos309o2c k)
      = (∑ k ∈ Finset.Icc 11 18, cos309o2c k) + cos309o2c 19 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 18) (by norm_num) cos309o2c
    simpa using h
  have hprev := psum309o2_18
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos309o2c 19 - ((-408353/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos309o2_br_19).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum309o2_20 : ((84927/40000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 20, cos309o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 20, cos309o2c k)
      = (∑ k ∈ Finset.Icc 11 19, cos309o2c k) + cos309o2c 20 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 19) (by norm_num) cos309o2c
    simpa using h
  have hprev := psum309o2_19
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos309o2c 20 - ((-103561/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos309o2_br_20).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum309o2_21 : ((693859/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 21, cos309o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 21, cos309o2c k)
      = (∑ k ∈ Finset.Icc 11 20, cos309o2c k) + cos309o2c 21 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 20) (by norm_num) cos309o2c
    simpa using h
  have hprev := psum309o2_20
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos309o2c 21 - ((652301/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos309o2_br_21).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum309o2_22 : ((3774429/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 22, cos309o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 22, cos309o2c k)
      = (∑ k ∈ Finset.Icc 11 21, cos309o2c k) + cos309o2c 22 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 21) (by norm_num) cos309o2c
    simpa using h
  have hprev := psum309o2_21
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos309o2c 22 - ((999033/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos309o2_br_22).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum309o2_23 : ((916649/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 23, cos309o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 23, cos309o2c k)
      = (∑ k ∈ Finset.Icc 11 22, cos309o2c k) + cos309o2c 23 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 22) (by norm_num) cos309o2c
    simpa using h
  have hprev := psum309o2_22
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos309o2c 23 - ((101107/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos309o2_br_23).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum309o2_24 : ((324271/62500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 24, cos309o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 24, cos309o2c k)
      = (∑ k ∈ Finset.Icc 11 23, cos309o2c k) + cos309o2c 24 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 23) (by norm_num) cos309o2c
    simpa using h
  have hprev := psum309o2_23
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos309o2c 24 - ((605131/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos309o2_br_24).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum309o2_25 : ((5774299/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 25, cos309o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 25, cos309o2c k)
      = (∑ k ∈ Finset.Icc 11 24, cos309o2c k) + cos309o2c 25 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 24) (by norm_num) cos309o2c
    simpa using h
  have hprev := psum309o2_24
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos309o2c 25 - ((586003/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos309o2_br_25).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum309o2_26 : ((203917/31250 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 26, cos309o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 26, cos309o2c k)
      = (∑ k ∈ Finset.Icc 11 25, cos309o2c k) + cos309o2c 26 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 25) (by norm_num) cos309o2c
    simpa using h
  have hprev := psum309o2_25
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos309o2c 26 - ((150217/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos309o2_br_26).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum309o2_27 : ((7489399/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 27, cos309o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 27, cos309o2c k)
      = (∑ k ∈ Finset.Icc 11 26, cos309o2c k) + cos309o2c 27 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 26) (by norm_num) cos309o2c
    simpa using h
  have hprev := psum309o2_26
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos309o2c 27 - ((192819/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos309o2_br_27).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum309o2_28 : ((8412127/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 28, cos309o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 28, cos309o2c k)
      = (∑ k ∈ Finset.Icc 11 27, cos309o2c k) + cos309o2c 28 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 27) (by norm_num) cos309o2c
    simpa using h
  have hprev := psum309o2_27
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos309o2c 28 - ((57673/62500 : ℚ) : ℝ) :=
    (abs_le.mp cos309o2_br_28).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum309o2_29 : ((2180149/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 29, cos309o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 29, cos309o2c k)
      = (∑ k ∈ Finset.Icc 11 28, cos309o2c k) + cos309o2c 29 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 28) (by norm_num) cos309o2c
    simpa using h
  have hprev := psum309o2_28
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos309o2c 29 - ((308509/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos309o2_br_29).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum309o2_30 : ((4026181/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 30, cos309o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 30, cos309o2c k)
      = (∑ k ∈ Finset.Icc 11 29, cos309o2c k) + cos309o2c 30 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 29) (by norm_num) cos309o2c
    simpa using h
  have hprev := psum309o2_29
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos309o2c 30 - ((-334097/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos309o2_br_30).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum309o2_31 : ((1424593/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 31, cos309o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 31, cos309o2c k)
      = (∑ k ∈ Finset.Icc 11 30, cos309o2c k) + cos309o2c 31 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 30) (by norm_num) cos309o2c
    simpa using h
  have hprev := psum309o2_30
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos309o2c 31 - ((-929357/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos309o2_br_31).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum309o2_32 : ((7307209/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 32, cos309o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 32, cos309o2c k)
      = (∑ k ∈ Finset.Icc 11 31, cos309o2c k) + cos309o2c 32 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 31) (by norm_num) cos309o2c
    simpa using h
  have hprev := psum309o2_31
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos309o2c 32 - ((46071/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos309o2_br_32).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum309o2_33 : ((1037111/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 33, cos309o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 33, cos309o2c k)
      = (∑ k ∈ Finset.Icc 11 32, cos309o2c k) + cos309o2c 33 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 32) (by norm_num) cos309o2c
    simpa using h
  have hprev := psum309o2_32
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos309o2c 33 - ((989719/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos309o2_br_33).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum309o2_34 : ((805563/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 34, cos309o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 34, cos309o2c k)
      = (∑ k ∈ Finset.Icc 11 33, cos309o2c k) + cos309o2c 34 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 33) (by norm_num) cos309o2c
    simpa using h
  have hprev := psum309o2_33
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos309o2c 34 - ((-120609/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos309o2_br_34).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum309o2_35 : ((895927/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 35, cos309o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 35, cos309o2c k)
      = (∑ k ∈ Finset.Icc 11 34, cos309o2c k) + cos309o2c 35 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 34) (by norm_num) cos309o2c
    simpa using h
  have hprev := psum309o2_34
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos309o2c 35 - ((-444087/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos309o2_br_35).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum309o2_36 : ((3955149/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 36, cos309o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 36, cos309o2c k)
      = (∑ k ∈ Finset.Icc 11 35, cos309o2c k) + cos309o2c 36 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 35) (by norm_num) cos309o2c
    simpa using h
  have hprev := psum309o2_35
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos309o2c 36 - ((371461/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos309o2_br_36).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum309o2_37 : ((8161659/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 37, cos309o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 37, cos309o2c k)
      = (∑ k ∈ Finset.Icc 11 36, cos309o2c k) + cos309o2c 37 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 36) (by norm_num) cos309o2c
    simpa using h
  have hprev := psum309o2_36
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos309o2c 37 - ((251401/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos309o2_br_37).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum309o2_38 : ((7218207/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 38, cos309o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 38, cos309o2c k)
      = (∑ k ∈ Finset.Icc 11 37, cos309o2c k) + cos309o2c 38 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 37) (by norm_num) cos309o2c
    simpa using h
  have hprev := psum309o2_37
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos309o2c 38 - ((-235853/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos309o2_br_38).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum309o2_39 : ((161583/20000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 39, cos309o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 39, cos309o2c k)
      = (∑ k ∈ Finset.Icc 11 38, cos309o2c k) + cos309o2c 39 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 38) (by norm_num) cos309o2c
    simpa using h
  have hprev := psum309o2_38
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos309o2c 39 - ((860983/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos309o2_br_39).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum309o2_40 : ((3907543/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 40, cos309o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 40, cos309o2c k)
      = (∑ k ∈ Finset.Icc 11 39, cos309o2c k) + cos309o2c 40 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 39) (by norm_num) cos309o2c
    simpa using h
  have hprev := psum309o2_39
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos309o2c 40 - ((-33003/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos309o2_br_40).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum309o2_41 : ((115936/15625 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 41, cos309o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 41, cos309o2c k)
      = (∑ k ∈ Finset.Icc 11 40, cos309o2c k) + cos309o2c 41 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 40) (by norm_num) cos309o2c
    simpa using h
  have hprev := psum309o2_40
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos309o2c 41 - ((-197571/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos309o2_br_41).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum309o2_42 : ((8254631/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 42, cos309o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 42, cos309o2c k)
      = (∑ k ∈ Finset.Icc 11 41, cos309o2c k) + cos309o2c 42 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 41) (by norm_num) cos309o2c
    simpa using h
  have hprev := psum309o2_41
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos309o2c 42 - ((834767/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos309o2_br_42).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum309o2_43 : ((907321/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 43, cos309o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 43, cos309o2c k)
      = (∑ k ∈ Finset.Icc 11 42, cos309o2c k) + cos309o2c 43 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 42) (by norm_num) cos309o2c
    simpa using h
  have hprev := psum309o2_42
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos309o2c 43 - ((-996023/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos309o2_br_43).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum309o2_44 : ((8207427/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 44, cos309o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 44, cos309o2c k)
      = (∑ k ∈ Finset.Icc 11 43, cos309o2c k) + cos309o2c 44 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 43) (by norm_num) cos309o2c
    simpa using h
  have hprev := psum309o2_43
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos309o2c 44 - ((948899/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos309o2_br_44).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum309o2_45 : ((296489/40000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 45, cos309o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 45, cos309o2c k)
      = (∑ k ∈ Finset.Icc 11 44, cos309o2c k) + cos309o2c 45 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 44) (by norm_num) cos309o2c
    simpa using h
  have hprev := psum309o2_44
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos309o2c 45 - ((-397581/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos309o2_br_45).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum309o2_46 : ((250917/31250 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 46, cos309o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 46, cos309o2c k)
      = (∑ k ∈ Finset.Icc 11 45, cos309o2c k) + cos309o2c 46 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 45) (by norm_num) cos309o2c
    simpa using h
  have hprev := psum309o2_45
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos309o2c 46 - ((617159/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos309o2_br_46).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum309o2_47 : ((472749/62500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 47, cos309o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 47, cos309o2c k)
      = (∑ k ∈ Finset.Icc 11 46, cos309o2c k) + cos309o2c 47 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 46) (by norm_num) cos309o2c
    simpa using h
  have hprev := psum309o2_46
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos309o2c 47 - ((-11633/25000 : ℚ) : ℝ) :=
    (abs_le.mp cos309o2_br_47).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum309o2_48 : ((1982051/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 48, cos309o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 48, cos309o2c k)
      = (∑ k ∈ Finset.Icc 11 47, cos309o2c k) + cos309o2c 48 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 47) (by norm_num) cos309o2c
    simpa using h
  have hprev := psum309o2_47
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos309o2c 48 - ((18213/50000 : ℚ) : ℝ) :=
    (abs_le.mp cos309o2_br_48).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum309o2_49 : ((760529/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 49, cos309o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 49, cos309o2c k)
      = (∑ k ∈ Finset.Icc 11 48, cos309o2c k) + cos309o2c 49 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 48) (by norm_num) cos309o2c
    simpa using h
  have hprev := psum309o2_48
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos309o2c 49 - ((-161437/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos309o2_br_49).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum309o2_50 : ((7947231/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 50, cos309o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 50, cos309o2c k)
      = (∑ k ∈ Finset.Icc 11 49, cos309o2c k) + cos309o2c 50 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 49) (by norm_num) cos309o2c
    simpa using h
  have hprev := psum309o2_49
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos309o2c 50 - ((341981/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos309o2_br_50).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum309o2_51 : ((3764653/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 51, cos309o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 51, cos309o2c k)
      = (∑ k ∈ Finset.Icc 11 50, cos309o2c k) + cos309o2c 51 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 50) (by norm_num) cos309o2c
    simpa using h
  have hprev := psum309o2_50
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos309o2c 51 - ((-83577/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos309o2_br_51).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum309o2_52 : ((1614219/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 52, cos309o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 52, cos309o2c k)
      = (∑ k ∈ Finset.Icc 11 51, cos309o2c k) + cos309o2c 52 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 51) (by norm_num) cos309o2c
    simpa using h
  have hprev := psum309o2_51
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos309o2c 52 - ((541829/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos309o2_br_52).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum309o2_53 : ((7374017/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 53, cos309o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 53, cos309o2c k)
      = (∑ k ∈ Finset.Icc 11 52, cos309o2c k) + cos309o2c 53 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 52) (by norm_num) cos309o2c
    simpa using h
  have hprev := psum309o2_52
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos309o2c 53 - ((-348519/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos309o2_br_53).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum309o2_54 : ((164573/20000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 54, cos309o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 54, cos309o2c k)
      = (∑ k ∈ Finset.Icc 11 53, cos309o2c k) + cos309o2c 54 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 53) (by norm_num) cos309o2c
    simpa using h
  have hprev := psum309o2_53
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos309o2c 54 - ((854673/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos309o2_br_54).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum309o2_55 : ((7257087/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 55, cos309o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 55, cos309o2c k)
      = (∑ k ∈ Finset.Icc 11 54, cos309o2c k) + cos309o2c 55 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 54) (by norm_num) cos309o2c
    simpa using h
  have hprev := psum309o2_54
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos309o2c 55 - ((-971523/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos309o2_br_55).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum309o2_56 : ((515627/62500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 56, cos309o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 56, cos309o2c k)
      = (∑ k ∈ Finset.Icc 11 55, cos309o2c k) + cos309o2c 56 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 55) (by norm_num) cos309o2c
    simpa using h
  have hprev := psum309o2_55
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos309o2c 56 - ((198597/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos309o2_br_56).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum309o2_57 : ((7384929/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 57, cos309o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 57, cos309o2c k)
      = (∑ k ∈ Finset.Icc 11 56, cos309o2c k) + cos309o2c 57 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 56) (by norm_num) cos309o2c
    simpa using h
  have hprev := psum309o2_56
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos309o2c 57 - ((-865063/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos309o2_br_57).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum309o2_58 : ((1588369/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 58, cos309o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 58, cos309o2c k)
      = (∑ k ∈ Finset.Icc 11 57, cos309o2c k) + cos309o2c 58 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 57) (by norm_num) cos309o2c
    simpa using h
  have hprev := psum309o2_57
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos309o2c 58 - ((139239/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos309o2_br_58).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum309o2_59 : ((3925859/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 59, cos309o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 59, cos309o2c k)
      = (∑ k ∈ Finset.Icc 11 58, cos309o2c k) + cos309o2c 59 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 58) (by norm_num) cos309o2c
    simpa using h
  have hprev := psum309o2_58
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos309o2c 59 - ((-90087/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos309o2_br_59).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum309o2_60 : ((7412497/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 60, cos309o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 60, cos309o2c k)
      = (∑ k ∈ Finset.Icc 11 59, cos309o2c k) + cos309o2c 60 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 59) (by norm_num) cos309o2c
    simpa using h
  have hprev := psum309o2_59
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos309o2c 60 - ((-439181/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos309o2_br_60).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum309o2_61 : ((66209/8000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 61, cos309o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 61, cos309o2c k)
      = (∑ k ∈ Finset.Icc 11 60, cos309o2c k) + cos309o2c 61 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 60) (by norm_num) cos309o2c
    simpa using h
  have hprev := psum309o2_60
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos309o2c 61 - ((215917/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos309o2_br_61).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum309o2_62 : ((3640593/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 62, cos309o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 62, cos309o2c k)
      = (∑ k ∈ Finset.Icc 11 61, cos309o2c k) + cos309o2c 62 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 61) (by norm_num) cos309o2c
    simpa using h
  have hprev := psum309o2_61
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos309o2c 62 - ((-994899/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos309o2_br_62).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum309o2_63 : ((7998651/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 63, cos309o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 63, cos309o2c k)
      = (∑ k ∈ Finset.Icc 11 62, cos309o2c k) + cos309o2c 63 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 62) (by norm_num) cos309o2c
    simpa using h
  have hprev := psum309o2_62
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos309o2c 63 - ((143501/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos309o2_br_63).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum309o2_64 : ((3953503/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 64, cos309o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 64, cos309o2c k)
      = (∑ k ∈ Finset.Icc 11 63, cos309o2c k) + cos309o2c 64 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 63) (by norm_num) cos309o2c
    simpa using h
  have hprev := psum309o2_63
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos309o2c 64 - ((-18321/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos309o2_br_64).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum309o2_65 : ((1459647/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 65, cos309o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 65, cos309o2c k)
      = (∑ k ∈ Finset.Icc 11 64, cos309o2c k) + cos309o2c 65 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 64) (by norm_num) cos309o2c
    simpa using h
  have hprev := psum309o2_64
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos309o2c 65 - ((-608731/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos309o2_br_65).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum309o2_66 : ((8289287/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 66, cos309o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 66, cos309o2c k)
      = (∑ k ∈ Finset.Icc 11 65, cos309o2c k) + cos309o2c 66 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 65) (by norm_num) cos309o2c
    simpa using h
  have hprev := psum309o2_65
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos309o2c 66 - ((247773/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos309o2_br_66).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum309o2_67 : ((939327/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 67, cos309o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 67, cos309o2c k)
      = (∑ k ∈ Finset.Icc 11 66, cos309o2c k) + cos309o2c 67 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 66) (by norm_num) cos309o2c
    simpa using h
  have hprev := psum309o2_66
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos309o2c 67 - ((-774631/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos309o2_br_67).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum309o2_68 : ((3774021/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 68, cos309o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 68, cos309o2c k)
      = (∑ k ∈ Finset.Icc 11 67, cos309o2c k) + cos309o2c 68 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 67) (by norm_num) cos309o2c
    simpa using h
  have hprev := psum309o2_67
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos309o2c 68 - ((16733/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos309o2_br_68).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum309o2_69 : ((8301/1000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 69, cos309o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 69, cos309o2c k)
      = (∑ k ∈ Finset.Icc 11 68, cos309o2c k) + cos309o2c 69 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 68) (by norm_num) cos309o2c
    simpa using h
  have hprev := psum309o2_68
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos309o2c 69 - ((376499/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos309o2_br_69).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum309o2_70 : ((7320963/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 70, cos309o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 70, cos309o2c k)
      = (∑ k ∈ Finset.Icc 11 69, cos309o2c k) + cos309o2c 70 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 69) (by norm_num) cos309o2c
    simpa using h
  have hprev := psum309o2_69
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos309o2c 70 - ((-979997/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos309o2_br_70).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum309o2_71 : ((7729027/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 71, cos309o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 71, cos309o2c k)
      = (∑ k ∈ Finset.Icc 11 70, cos309o2c k) + cos309o2c 71 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 70) (by norm_num) cos309o2c
    simpa using h
  have hprev := psum309o2_70
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos309o2c 71 - ((51013/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos309o2_br_71).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum309o2_72 : ((1032557/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 72, cos309o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 72, cos309o2c k)
      = (∑ k ∈ Finset.Icc 11 71, cos309o2c k) + cos309o2c 72 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 71) (by norm_num) cos309o2c
    simpa using h
  have hprev := psum309o2_71
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos309o2c 72 - ((531469/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos309o2_br_72).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum309o2_73 : ((113444/15625 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 73, cos309o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 73, cos309o2c k)
      = (∑ k ∈ Finset.Icc 11 72, cos309o2c k) + cos309o2c 73 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 72) (by norm_num) cos309o2c
    simpa using h
  have hprev := psum309o2_72
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos309o2c 73 - ((-1 : ℚ) : ℝ) :=
    (abs_le.mp cos309o2_br_73).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum309o2_74 : ((1941737/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 74, cos309o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 74, cos309o2c k)
      = (∑ k ∈ Finset.Icc 11 73, cos309o2c k) + cos309o2c 74 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 73) (by norm_num) cos309o2c
    simpa using h
  have hprev := psum309o2_73
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos309o2c 74 - ((126643/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos309o2_br_74).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum309o2_75 : ((1034757/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 75, cos309o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 75, cos309o2c k)
      = (∑ k ∈ Finset.Icc 11 74, cos309o2c k) + cos309o2c 75 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 74) (by norm_num) cos309o2c
    simpa using h
  have hprev := psum309o2_74
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos309o2c 75 - ((127787/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos309o2_br_75).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum309o2_76 : ((113748/15625 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 76, cos309o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 76, cos309o2c k)
      = (∑ k ∈ Finset.Icc 11 75, cos309o2c k) + cos309o2c 76 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 75) (by norm_num) cos309o2c
    simpa using h
  have hprev := psum309o2_75
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos309o2c 76 - ((-15596/15625 : ℚ) : ℝ) :=
    (abs_le.mp cos309o2_br_76).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum309o2_77 : ((7658087/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 77, cos309o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 77, cos309o2c k)
      = (∑ k ∈ Finset.Icc 11 76, cos309o2c k) + cos309o2c 77 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 76) (by norm_num) cos309o2c
    simpa using h
  have hprev := psum309o2_76
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos309o2c 77 - ((75651/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos309o2_br_77).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum309o2_78 : ((4173523/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 78, cos309o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 78, cos309o2c k)
      = (∑ k ∈ Finset.Icc 11 77, cos309o2c k) + cos309o2c 78 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 77) (by norm_num) cos309o2c
    simpa using h
  have hprev := psum309o2_77
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos309o2c 78 - ((688999/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos309o2_br_78).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum309o2_79 : ((3706037/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 79, cos309o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 79, cos309o2c k)
      = (∑ k ∈ Finset.Icc 11 78, cos309o2c k) + cos309o2c 79 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 78) (by norm_num) cos309o2c
    simpa using h
  have hprev := psum309o2_78
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos309o2c 79 - ((-233733/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos309o2_br_79).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum309o2_80 : ((1484387/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 80, cos309o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 80, cos309o2c k)
      = (∑ k ∈ Finset.Icc 11 79, cos309o2c k) + cos309o2c 80 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 79) (by norm_num) cos309o2c
    simpa using h
  have hprev := psum309o2_79
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos309o2c 80 - ((9901/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos309o2_br_80).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum309o2_81 : ((8358361/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 81, cos309o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 81, cos309o2c k)
      = (∑ k ∈ Finset.Icc 11 80, cos309o2c k) + cos309o2c 81 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 80) (by norm_num) cos309o2c
    simpa using h
  have hprev := psum309o2_80
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos309o2c 81 - ((468233/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos309o2_br_81).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum309o2_82 : ((3863477/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 82, cos309o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 82, cos309o2c k)
      = (∑ k ∈ Finset.Icc 11 81, cos309o2c k) + cos309o2c 82 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 81) (by norm_num) cos309o2c
    simpa using h
  have hprev := psum309o2_81
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos309o2c 82 - ((-631367/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos309o2_br_82).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum309o2_83 : ((179357/25000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 83, cos309o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 83, cos309o2c k)
      = (∑ k ∈ Finset.Icc 11 82, cos309o2c k) + cos309o2c 83 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 82) (by norm_num) cos309o2c
    simpa using h
  have hprev := psum309o2_82
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos309o2c 83 - ((-276317/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos309o2_br_83).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum309o2_84 : ((1625557/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 84, cos309o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 84, cos309o2c k)
      = (∑ k ∈ Finset.Icc 11 83, cos309o2c k) + cos309o2c 84 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 83) (by norm_num) cos309o2c
    simpa using h
  have hprev := psum309o2_83
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos309o2c 84 - ((190709/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos309o2_br_84).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum309o2_85 : ((8176103/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 85, cos309o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 85, cos309o2c k)
      = (∑ k ∈ Finset.Icc 11 84, cos309o2c k) + cos309o2c 85 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 84) (by norm_num) cos309o2c
    simpa using h
  have hprev := psum309o2_84
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos309o2c 85 - ((24179/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos309o2_br_85).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum309o2_86 : ((7193657/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 86, cos309o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 86, cos309o2c k)
      = (∑ k ∈ Finset.Icc 11 85, cos309o2c k) + cos309o2c 86 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 85) (by norm_num) cos309o2c
    simpa using h
  have hprev := psum309o2_85
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos309o2c 86 - ((-491203/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos309o2_br_86).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum309o2_87 : ((7586001/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 87, cos309o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 87, cos309o2c k)
      = (∑ k ∈ Finset.Icc 11 86, cos309o2c k) + cos309o2c 87 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 86) (by norm_num) cos309o2c
    simpa using h
  have hprev := psum309o2_86
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos309o2c 87 - ((6131/15625 : ℚ) : ℝ) :=
    (abs_le.mp cos309o2_br_87).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum309o2_88 : ((4206167/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 88, cos309o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 88, cos309o2c k)
      = (∑ k ∈ Finset.Icc 11 87, cos309o2c k) + cos309o2c 88 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 87) (by norm_num) cos309o2c
    simpa using h
  have hprev := psum309o2_87
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos309o2c 88 - ((826373/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos309o2_br_88).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum309o2_89 : ((7713911/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 89, cos309o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 89, cos309o2c k)
      = (∑ k ∈ Finset.Icc 11 88, cos309o2c k) + cos309o2c 89 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 88) (by norm_num) cos309o2c
    simpa using h
  have hprev := psum309o2_88
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos309o2c 89 - ((-698383/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos309o2_br_89).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum309o2_90 : ((7114927/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 90, cos309o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 90, cos309o2c k)
      = (∑ k ∈ Finset.Icc 11 89, cos309o2c k) + cos309o2c 90 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 89) (by norm_num) cos309o2c
    simpa using h
  have hprev := psum309o2_89
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos309o2c 90 - ((-18717/31250 : ℚ) : ℝ) :=
    (abs_le.mp cos309o2_br_90).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum309o2_91 : ((3994843/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 91, cos309o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 91, cos309o2c k)
      = (∑ k ∈ Finset.Icc 11 90, cos309o2c k) + cos309o2c 91 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 90) (by norm_num) cos309o2c
    simpa using h
  have hprev := psum309o2_90
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos309o2c 91 - ((874799/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos309o2_br_91).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum309o2_92 : ((523001/62500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 92, cos309o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 92, cos309o2c k)
      = (∑ k ∈ Finset.Icc 11 91, cos309o2c k) + cos309o2c 92 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 91) (by norm_num) cos309o2c
    simpa using h
  have hprev := psum309o2_91
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos309o2c 92 - ((37837/100000 : ℚ) : ℝ) :=
    (abs_le.mp cos309o2_br_92).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum309o2_93 : ((3704659/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 93, cos309o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 93, cos309o2c k)
      = (∑ k ∈ Finset.Icc 11 92, cos309o2c k) + cos309o2c 93 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 92) (by norm_num) cos309o2c
    simpa using h
  have hprev := psum309o2_92
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos309o2c 93 - ((-479329/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos309o2_br_93).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum309o2_94 : ((900479/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 94, cos309o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 94, cos309o2c k)
      = (∑ k ∈ Finset.Icc 11 93, cos309o2c k) + cos309o2c 94 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 93) (by norm_num) cos309o2c
    simpa using h
  have hprev := psum309o2_93
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos309o2c 94 - ((-102723/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos309o2_br_94).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum309o2_95 : ((512101/62500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 95, cos309o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 95, cos309o2c k)
      = (∑ k ∈ Finset.Icc 11 94, cos309o2c k) + cos309o2c 95 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 94) (by norm_num) cos309o2c
    simpa using h
  have hprev := psum309o2_94
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos309o2c 95 - ((15466/15625 : ℚ) : ℝ) :=
    (abs_le.mp cos309o2_br_95).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum309o2_96 : ((8289191/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 96, cos309o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 96, cos309o2c k)
      = (∑ k ∈ Finset.Icc 11 95, cos309o2c k) + cos309o2c 96 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 95) (by norm_num) cos309o2c
    simpa using h
  have hprev := psum309o2_95
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos309o2c 96 - ((19123/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos309o2_br_96).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum309o2_97 : ((227853/31250 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 97, cos309o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 97, cos309o2c k)
      = (∑ k ∈ Finset.Icc 11 96, cos309o2c k) + cos309o2c 97 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 96) (by norm_num) cos309o2c
    simpa using h
  have hprev := psum309o2_96
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos309o2c 97 - ((-199571/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos309o2_br_97).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum309o2_98 : ((7239607/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 98, cos309o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 98, cos309o2c k)
      = (∑ k ∈ Finset.Icc 11 97, cos309o2c k) + cos309o2c 98 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 97) (by norm_num) cos309o2c
    simpa using h
  have hprev := psum309o2_97
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos309o2c 98 - ((-51649/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos309o2_br_98).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum309o2_99 : ((4119057/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 99, cos309o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 99, cos309o2c k)
      = (∑ k ∈ Finset.Icc 11 98, cos309o2c k) + cos309o2c 99 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 98) (by norm_num) cos309o2c
    simpa using h
  have hprev := psum309o2_98
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos309o2c 99 - ((998547/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos309o2_br_99).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum309o2_100 : ((207749/25000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 100, cos309o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 100, cos309o2c k)
      = (∑ k ∈ Finset.Icc 11 99, cos309o2c k) + cos309o2c 100 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 99) (by norm_num) cos309o2c
    simpa using h
  have hprev := psum309o2_99
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos309o2c 100 - ((35943/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos309o2_br_100).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum309o2_101 : ((731547/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 101, cos309o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 101, cos309o2c k)
      = (∑ k ∈ Finset.Icc 11 100, cos309o2c k) + cos309o2c 101 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 100) (by norm_num) cos309o2c
    simpa using h
  have hprev := psum309o2_100
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos309o2c 101 - ((-19889/20000 : ℚ) : ℝ) :=
    (abs_le.mp cos309o2_br_101).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum309o2_102 : ((1432403/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 102, cos309o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 102, cos309o2c k)
      = (∑ k ∈ Finset.Icc 11 101, cos309o2c k) + cos309o2c 102 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 101) (by norm_num) cos309o2c
    simpa using h
  have hprev := psum309o2_101
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos309o2c 102 - ((-30683/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos309o2_br_102).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum309o2_103 : ((4069207/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 103, cos309o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 103, cos309o2c k)
      = (∑ k ∈ Finset.Icc 11 102, cos309o2c k) + cos309o2c 103 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 102) (by norm_num) cos309o2c
    simpa using h
  have hprev := psum309o2_102
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos309o2c 103 - ((976439/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos309o2_br_103).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum309o2_104 : ((4214813/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 104, cos309o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 104, cos309o2c k)
      = (∑ k ∈ Finset.Icc 11 103, cos309o2c k) + cos309o2c 104 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 103) (by norm_num) cos309o2c
    simpa using h
  have hprev := psum309o2_103
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos309o2c 104 - ((72813/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos309o2_br_104).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum309o2_105 : ((7503859/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 105, cos309o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 105, cos309o2c k)
      = (∑ k ∈ Finset.Icc 11 104, cos309o2c k) + cos309o2c 105 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 104) (by norm_num) cos309o2c
    simpa using h
  have hprev := psum309o2_104
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos309o2c 105 - ((-925727/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos309o2_br_105).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum309o2_106 : ((1757377/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 106, cos309o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 106, cos309o2c k)
      = (∑ k ∈ Finset.Icc 11 105, cos309o2c k) + cos309o2c 106 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 105) (by norm_num) cos309o2c
    simpa using h
  have hprev := psum309o2_105
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos309o2c 106 - ((-474311/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos309o2_br_106).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum309o2_107 : ((490417/62500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 107, cos309o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 107, cos309o2c k)
      = (∑ k ∈ Finset.Icc 11 106, cos309o2c k) + cos309o2c 107 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 106) (by norm_num) cos309o2c
    simpa using h
  have hprev := psum309o2_106
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos309o2c 107 - ((204301/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos309o2_br_107).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum309o2_108 : ((213167/25000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 108, cos309o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 108, cos309o2c k)
      = (∑ k ∈ Finset.Icc 11 107, cos309o2c k) + cos309o2c 108 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 107) (by norm_num) cos309o2c
    simpa using h
  have hprev := psum309o2_107
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos309o2c 108 - ((42503/62500 : ℚ) : ℝ) :=
    (abs_le.mp cos309o2_br_108).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum309o2_109 : ((987607/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 109, cos309o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 109, cos309o2c k)
      = (∑ k ∈ Finset.Icc 11 108, cos309o2c k) + cos309o2c 109 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 108) (by norm_num) cos309o2c
    simpa using h
  have hprev := psum309o2_108
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos309o2c 109 - ((-78223/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos309o2_br_109).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum309o2_110 : ((703117/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 110, cos309o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 110, cos309o2c k)
      = (∑ k ∈ Finset.Icc 11 109, cos309o2c k) + cos309o2c 110 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 109) (by norm_num) cos309o2c
    simpa using h
  have hprev := psum309o2_109
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos309o2c 110 - ((-434823/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos309o2_br_110).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum309o2_111 : ((3684063/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 111, cos309o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 111, cos309o2c k)
      = (∑ k ∈ Finset.Icc 11 110, cos309o2c k) + cos309o2c 111 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 110) (by norm_num) cos309o2c
    simpa using h
  have hprev := psum309o2_110
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos309o2c 111 - ((84249/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos309o2_br_111).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum309o2_112 : ((8355539/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 112, cos309o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 112, cos309o2c k)
      = (∑ k ∈ Finset.Icc 11 111, cos309o2c k) + cos309o2c 112 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 111) (by norm_num) cos309o2c
    simpa using h
  have hprev := psum309o2_111
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos309o2c 112 - ((987453/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos309o2_br_112).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum309o2_113 : ((4197179/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 113, cos309o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 113, cos309o2c k)
      = (∑ k ∈ Finset.Icc 11 112, cos309o2c k) + cos309o2c 113 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 112) (by norm_num) cos309o2c
    simpa using h
  have hprev := psum309o2_112
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos309o2c 113 - ((38859/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos309o2_br_113).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum309o2_114 : ((3712509/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 114, cos309o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 114, cos309o2c k)
      = (∑ k ∈ Finset.Icc 11 113, cos309o2c k) + cos309o2c 114 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 113) (by norm_num) cos309o2c
    simpa using h
  have hprev := psum309o2_113
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos309o2c 114 - ((-9693/10000 : ℚ) : ℝ) :=
    (abs_le.mp cos309o2_br_114).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum309o2_115 : ((697221/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 115, cos309o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 115, cos309o2c k)
      = (∑ k ∈ Finset.Icc 11 114, cos309o2c k) + cos309o2c 115 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 114) (by norm_num) cos309o2c
    simpa using h
  have hprev := psum309o2_114
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos309o2c 115 - ((-14149/31250 : ℚ) : ℝ) :=
    (abs_le.mp cos309o2_br_115).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum309o2_116 : ((3867537/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 116, cos309o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 116, cos309o2c k)
      = (∑ k ∈ Finset.Icc 11 115, cos309o2c k) + cos309o2c 116 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 115) (by norm_num) cos309o2c
    simpa using h
  have hprev := psum309o2_115
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos309o2c 116 - ((95363/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos309o2_br_116).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum309o2_117 : ((2136763/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 117, cos309o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 117, cos309o2c k)
      = (∑ k ∈ Finset.Icc 11 116, cos309o2c k) + cos309o2c 117 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 116) (by norm_num) cos309o2c
    simpa using h
  have hprev := psum309o2_116
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos309o2c 117 - ((406009/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos309o2_br_117).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum309o2_118 : ((4093957/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 118, cos309o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 118, cos309o2c k)
      = (∑ k ∈ Finset.Icc 11 117, cos309o2c k) + cos309o2c 118 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 117) (by norm_num) cos309o2c
    simpa using h
  have hprev := psum309o2_117
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos309o2c 118 - ((-179549/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos309o2_br_118).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum309o2_119 : ((71929/10000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 119, cos309o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 119, cos309o2c k)
      = (∑ k ∈ Finset.Icc 11 118, cos309o2c k) + cos309o2c 119 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 118) (by norm_num) cos309o2c
    simpa using h
  have hprev := psum309o2_118
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos309o2c 119 - ((-497487/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos309o2_br_119).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum309o2_120 : ((3508099/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 120, cos309o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 120, cos309o2c k)
      = (∑ k ∈ Finset.Icc 11 119, cos309o2c k) + cos309o2c 120 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 119) (by norm_num) cos309o2c
    simpa using h
  have hprev := psum309o2_119
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos309o2c 120 - ((-88331/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos309o2_br_120).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum309o2_121 : ((7909429/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 121, cos309o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 121, cos309o2c k)
      = (∑ k ∈ Finset.Icc 11 120, cos309o2c k) + cos309o2c 121 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 120) (by norm_num) cos309o2c
    simpa using h
  have hprev := psum309o2_120
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos309o2c 121 - ((893271/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos309o2_br_121).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum309o2_122 : ((4301111/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 122, cos309o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 122, cos309o2c k)
      = (∑ k ∈ Finset.Icc 11 121, cos309o2c k) + cos309o2c 122 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 121) (by norm_num) cos309o2c
    simpa using h
  have hprev := psum309o2_121
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos309o2c 122 - ((692833/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos309o2_br_122).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum309o2_123 : ((8126429/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 123, cos309o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 123, cos309o2c k)
      = (∑ k ∈ Finset.Icc 11 122, cos309o2c k) + cos309o2c 123 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 122) (by norm_num) cos309o2c
    simpa using h
  have hprev := psum309o2_122
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos309o2c 123 - ((-475753/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos309o2_br_123).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum309o2_124 : ((1785461/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 124, cos309o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 124, cos309o2c k)
      = (∑ k ∈ Finset.Icc 11 123, cos309o2c k) + cos309o2c 124 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 123) (by norm_num) cos309o2c
    simpa using h
  have hprev := psum309o2_123
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos309o2c 124 - ((-196909/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos309o2_br_124).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum309o2_125 : ((6988629/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 125, cos309o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 125, cos309o2c k)
      = (∑ k ∈ Finset.Icc 11 124, cos309o2c k) + cos309o2c 125 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 124) (by norm_num) cos309o2c
    simpa using h
  have hprev := psum309o2_124
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos309o2c 125 - ((-6127/40000 : ℚ) : ℝ) :=
    (abs_le.mp cos309o2_br_125).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum309o2_126 : ((3934637/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 126, cos309o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 126, cos309o2c k)
      = (∑ k ∈ Finset.Icc 11 125, cos309o2c k) + cos309o2c 126 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 125) (by norm_num) cos309o2c
    simpa using h
  have hprev := psum309o2_125
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos309o2c 126 - ((176137/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos309o2_br_126).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum309o2_127 : ((4307921/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 127, cos309o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 127, cos309o2c k)
      = (∑ k ∈ Finset.Icc 11 126, cos309o2c k) + cos309o2c 127 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 126) (by norm_num) cos309o2c
    simpa using h
  have hprev := psum309o2_126
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos309o2c 127 - ((46663/62500 : ℚ) : ℝ) :=
    (abs_le.mp cos309o2_br_127).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum309o2_128 : ((4127641/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 128, cos309o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 128, cos309o2c k)
      = (∑ k ∈ Finset.Icc 11 127, cos309o2c k) + cos309o2c 128 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 127) (by norm_num) cos309o2c
    simpa using h
  have hprev := psum309o2_127
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos309o2c 128 - ((-9013/25000 : ℚ) : ℝ) :=
    (abs_le.mp cos309o2_br_128).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum309o2_129 : ((3627621/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 129, cos309o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 129, cos309o2c k)
      = (∑ k ∈ Finset.Icc 11 128, cos309o2c k) + cos309o2c 129 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 128) (by norm_num) cos309o2c
    simpa using h
  have hprev := psum309o2_128
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos309o2c 129 - ((-1 : ℚ) : ℝ) :=
    (abs_le.mp cos309o2_br_129).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum309o2_130 : ((6886727/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 130, cos309o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 130, cos309o2c k)
      = (∑ k ∈ Finset.Icc 11 129, cos309o2c k) + cos309o2c 130 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 129) (by norm_num) cos309o2c
    simpa using h
  have hprev := psum309o2_129
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos309o2c 130 - ((-14739/40000 : ℚ) : ℝ) :=
    (abs_le.mp cos309o2_br_130).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum309o2_131 : ((7608591/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 131, cos309o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 131, cos309o2c k)
      = (∑ k ∈ Finset.Icc 11 130, cos309o2c k) + cos309o2c 131 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 130) (by norm_num) cos309o2c
    simpa using h
  have hprev := psum309o2_130
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos309o2c 131 - ((45119/62500 : ℚ) : ℝ) :=
    (abs_le.mp cos309o2_br_131).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum309o2_132 : ((8525407/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 132, cos309o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 132, cos309o2c k)
      = (∑ k ∈ Finset.Icc 11 131, cos309o2c k) + cos309o2c 132 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 131) (by norm_num) cos309o2c
    simpa using h
  have hprev := psum309o2_131
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos309o2c 132 - ((114607/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos309o2_br_132).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum309o2_133 : ((8519457/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 133, cos309o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 133, cos309o2c k)
      = (∑ k ∈ Finset.Icc 11 132, cos309o2c k) + cos309o2c 133 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 132) (by norm_num) cos309o2c
    simpa using h
  have hprev := psum309o2_132
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos309o2c 133 - ((-591/100000 : ℚ) : ℝ) :=
    (abs_le.mp cos309o2_br_133).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum309o2_134 : ((3800667/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 134, cos309o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 134, cos309o2c k)
      = (∑ k ∈ Finset.Icc 11 133, cos309o2c k) + cos309o2c 134 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 133) (by norm_num) cos309o2c
    simpa using h
  have hprev := psum309o2_133
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos309o2c 134 - ((-918083/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos309o2_br_134).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum309o2_135 : ((6863581/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 135, cos309o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 135, cos309o2c k)
      = (∑ k ∈ Finset.Icc 11 134, cos309o2c k) + cos309o2c 135 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 134) (by norm_num) cos309o2c
    simpa using h
  have hprev := psum309o2_134
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos309o2c 135 - ((-737713/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos309o2_br_135).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum309o2_136 : ((3584561/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 136, cos309o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 136, cos309o2c k)
      = (∑ k ∈ Finset.Icc 11 135, cos309o2c k) + cos309o2c 136 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 135) (by norm_num) cos309o2c
    simpa using h
  have hprev := psum309o2_135
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos309o2c 136 - ((305581/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos309o2_br_136).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum309o2_137 : ((4080427/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 137, cos309o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 137, cos309o2c k)
      = (∑ k ∈ Finset.Icc 11 136, cos309o2c k) + cos309o2c 137 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 136) (by norm_num) cos309o2c
    simpa using h
  have hprev := psum309o2_136
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos309o2c 137 - ((247943/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos309o2_br_137).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum309o2_138 : ((8705093/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 138, cos309o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 138, cos309o2c k)
      = (∑ k ∈ Finset.Icc 11 137, cos309o2c k) + cos309o2c 138 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 137) (by norm_num) cos309o2c
    simpa using h
  have hprev := psum309o2_137
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos309o2c 138 - ((544279/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos309o2_br_138).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum309o2_139 : ((8190911/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 139, cos309o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 139, cos309o2c k)
      = (∑ k ∈ Finset.Icc 11 138, cos309o2c k) + cos309o2c 139 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 138) (by norm_num) cos309o2c
    simpa using h
  have hprev := psum309o2_138
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos309o2c 139 - ((-257071/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos309o2_br_139).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum309o2_140 : ((3596907/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 140, cos309o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 140, cos309o2c k)
      = (∑ k ∈ Finset.Icc 11 139, cos309o2c k) + cos309o2c 140 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 139) (by norm_num) cos309o2c
    simpa using h
  have hprev := psum309o2_139
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos309o2c 140 - ((-997057/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos309o2_br_140).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum309o2_141 : ((3404753/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 141, cos309o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 141, cos309o2c k)
      = (∑ k ∈ Finset.Icc 11 140, cos309o2c k) + cos309o2c 141 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 140) (by norm_num) cos309o2c
    simpa using h
  have hprev := psum309o2_140
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos309o2c 141 - ((-96067/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos309o2_br_141).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum309o2_142 : ((1490349/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 142, cos309o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 142, cos309o2c k)
      = (∑ k ∈ Finset.Icc 11 141, cos309o2c k) + cos309o2c 142 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 141) (by norm_num) cos309o2c
    simpa using h
  have hprev := psum309o2_141
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos309o2c 142 - ((642279/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos309o2_br_142).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum309o2_143 : ((168591/20000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 143, cos309o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 143, cos309o2c k)
      = (∑ k ∈ Finset.Icc 11 142, cos309o2c k) + cos309o2c 143 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 142) (by norm_num) cos309o2c
    simpa using h
  have hprev := psum309o2_142
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos309o2c 143 - ((195569/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos309o2_br_143).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum309o2_144 : ((4354497/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 144, cos309o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 144, cos309o2c k)
      = (∑ k ∈ Finset.Icc 11 143, cos309o2c k) + cos309o2c 144 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 143) (by norm_num) cos309o2c
    simpa using h
  have hprev := psum309o2_143
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos309o2c 144 - ((69871/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos309o2_br_144).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum309o2_145 : ((160029/20000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 145, cos309o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 145, cos309o2c k)
      = (∑ k ∈ Finset.Icc 11 144, cos309o2c k) + cos309o2c 145 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 144) (by norm_num) cos309o2c
    simpa using h
  have hprev := psum309o2_144
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos309o2c 145 - ((-44219/62500 : ℚ) : ℝ) :=
    (abs_le.mp cos309o2_br_145).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum309o2_146 : ((7039537/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 146, cos309o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 146, cos309o2c k)
      = (∑ k ∈ Finset.Icc 11 145, cos309o2c k) + cos309o2c 146 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 145) (by norm_num) cos309o2c
    simpa using h
  have hprev := psum309o2_145
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos309o2c 146 - ((-961873/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos309o2_br_146).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum309o2_147 : ((6802603/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 147, cos309o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 147, cos309o2c k)
      = (∑ k ∈ Finset.Icc 11 146, cos309o2c k) + cos309o2c 147 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 146) (by norm_num) cos309o2c
    simpa using h
  have hprev := psum309o2_146
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos309o2c 147 - ((-118447/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos309o2_br_147).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum309o2_148 : ((3762837/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 148, cos309o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 148, cos309o2c k)
      = (∑ k ∈ Finset.Icc 11 147, cos309o2c k) + cos309o2c 148 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 147) (by norm_num) cos309o2c
    simpa using h
  have hprev := psum309o2_147
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos309o2c 148 - ((723111/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos309o2_br_148).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum309o2_149 : ((8487263/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 149, cos309o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 149, cos309o2c k)
      = (∑ k ∈ Finset.Icc 11 148, cos309o2c k) + cos309o2c 149 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 148) (by norm_num) cos309o2c
    simpa using h
  have hprev := psum309o2_148
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos309o2c 149 - ((961629/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos309o2_br_149).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum309o2_150 : ((1748753/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 150, cos309o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 150, cos309o2c k)
      = (∑ k ∈ Finset.Icc 11 149, cos309o2c k) + cos309o2c 150 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 149) (by norm_num) cos309o2c
    simpa using h
  have hprev := psum309o2_149
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos309o2c 150 - ((128271/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos309o2_br_150).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum309o2_151 : ((201241/25000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 151, cos309o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 151, cos309o2c k)
      = (∑ k ∈ Finset.Icc 11 150, cos309o2c k) + cos309o2c 151 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 150) (by norm_num) cos309o2c
    simpa using h
  have hprev := psum309o2_150
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos309o2c 151 - ((-138817/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos309o2_br_151).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum309o2_152 : ((884109/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 152, cos309o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 152, cos309o2c k)
      = (∑ k ∈ Finset.Icc 11 151, cos309o2c k) + cos309o2c 152 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 151) (by norm_num) cos309o2c
    simpa using h
  have hprev := psum309o2_151
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos309o2c 152 - ((-122091/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos309o2_br_152).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum309o2_153 : ((3368957/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 153, cos309o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 153, cos309o2c k)
      = (∑ k ∈ Finset.Icc 11 152, cos309o2c k) + cos309o2c 153 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 152) (by norm_num) cos309o2c
    simpa using h
  have hprev := psum309o2_152
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos309o2c 153 - ((-167459/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos309o2_br_153).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum309o2_154 : ((1470987/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 154, cos309o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 154, cos309o2c k)
      = (∑ k ∈ Finset.Icc 11 153, cos309o2c k) + cos309o2c 154 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 153) (by norm_num) cos309o2c
    simpa using h
  have hprev := psum309o2_153
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos309o2c 154 - ((617061/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos309o2_br_154).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum309o2_155 : ((8350461/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 155, cos309o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 155, cos309o2c k)
      = (∑ k ∈ Finset.Icc 11 154, cos309o2c k) + cos309o2c 155 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 154) (by norm_num) cos309o2c
    simpa using h
  have hprev := psum309o2_154
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos309o2c 155 - ((497783/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos309o2_br_155).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum309o2_156 : ((1101859/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 156, cos309o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 156, cos309o2c k)
      = (∑ k ∈ Finset.Icc 11 155, cos309o2c k) + cos309o2c 156 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 155) (by norm_num) cos309o2c
    simpa using h
  have hprev := psum309o2_155
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos309o2c 156 - ((464451/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos309o2_br_156).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum309o2_157 : ((8331717/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 157, cos309o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 157, cos309o2c k)
      = (∑ k ∈ Finset.Icc 11 156, cos309o2c k) + cos309o2c 157 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 156) (by norm_num) cos309o2c
    simpa using h
  have hprev := psum309o2_156
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos309o2c 157 - ((-96623/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos309o2_br_157).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum309o2_158 : ((7335341/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 158, cos309o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 158, cos309o2c k)
      = (∑ k ∈ Finset.Icc 11 157, cos309o2c k) + cos309o2c 158 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 157) (by norm_num) cos309o2c
    simpa using h
  have hprev := psum309o2_157
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos309o2c 158 - ((-62271/62500 : ℚ) : ℝ) :=
    (abs_le.mp cos309o2_br_158).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum309o2_159 : ((3352609/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 159, cos309o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 159, cos309o2c k)
      = (∑ k ∈ Finset.Icc 11 158, cos309o2c k) + cos309o2c 159 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 158) (by norm_num) cos309o2c
    simpa using h
  have hprev := psum309o2_158
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos309o2c 159 - ((-630083/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos309o2_br_159).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum309o2_160 : ((6988247/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 160, cos309o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 160, cos309o2c k)
      = (∑ k ∈ Finset.Icc 11 159, cos309o2c k) + cos309o2c 160 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 159) (by norm_num) cos309o2c
    simpa using h
  have hprev := psum309o2_159
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos309o2c 160 - ((283069/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos309o2_br_160).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum309o2_161 : ((7937067/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 161, cos309o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 161, cos309o2c k)
      = (∑ k ∈ Finset.Icc 11 160, cos309o2c k) + cos309o2c 161 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 160) (by norm_num) cos309o2c
    simpa using h
  have hprev := psum309o2_160
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos309o2c 161 - ((47443/50000 : ℚ) : ℝ) :=
    (abs_le.mp cos309o2_br_161).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum309o2_162 : ((4370909/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 162, cos309o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 162, cos309o2c k)
      = (∑ k ∈ Finset.Icc 11 161, cos309o2c k) + cos309o2c 162 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 161) (by norm_num) cos309o2c
    simpa using h
  have hprev := psum309o2_161
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos309o2c 162 - ((804791/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos309o2_br_162).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum309o2_163 : ((349053/40000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 163, cos309o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 163, cos309o2c k)
      = (∑ k ∈ Finset.Icc 11 162, cos309o2c k) + cos309o2c 163 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 162) (by norm_num) cos309o2c
    simpa using h
  have hprev := psum309o2_162
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos309o2c 163 - ((-15453/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos309o2_br_163).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum309o2_164 : ((395343/50000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 164, cos309o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 164, cos309o2c k)
      = (∑ k ∈ Finset.Icc 11 163, cos309o2c k) + cos309o2c 164 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 163) (by norm_num) cos309o2c
    simpa using h
  have hprev := psum309o2_163
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos309o2c 164 - ((-32777/40000 : ℚ) : ℝ) :=
    (abs_le.mp cos309o2_br_164).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum309o2_165 : ((1392079/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 165, cos309o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 165, cos309o2c k)
      = (∑ k ∈ Finset.Icc 11 164, cos309o2c k) + cos309o2c 165 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 164) (by norm_num) cos309o2c
    simpa using h
  have hprev := psum309o2_164
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos309o2c 165 - ((-37857/40000 : ℚ) : ℝ) :=
    (abs_le.mp cos309o2_br_165).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum309o2_166 : ((3328389/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 166, cos309o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 166, cos309o2c k)
      = (∑ k ∈ Finset.Icc 11 165, cos309o2c k) + cos309o2c 166 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 165) (by norm_num) cos309o2c
    simpa using h
  have hprev := psum309o2_165
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos309o2c 166 - ((-303577/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos309o2_br_166).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum309o2_167 : ((1809341/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 167, cos309o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 167, cos309o2c k)
      = (∑ k ∈ Finset.Icc 11 166, cos309o2c k) + cos309o2c 167 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 166) (by norm_num) cos309o2c
    simpa using h
  have hprev := psum309o2_166
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos309o2c 167 - ((290313/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos309o2_br_167).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum309o2_168 : ((4118453/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 168, cos309o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 168, cos309o2c k)
      = (∑ k ∈ Finset.Icc 11 167, cos309o2c k) + cos309o2c 168 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 167) (by norm_num) cos309o2c
    simpa using h
  have hprev := psum309o2_167
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos309o2c 168 - ((499791/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos309o2_br_168).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum309o2_169 : ((354713/40000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 169, cos309o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 169, cos309o2c k)
      = (∑ k ∈ Finset.Icc 11 168, cos309o2c k) + cos309o2c 169 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 168) (by norm_num) cos309o2c
    simpa using h
  have hprev := psum309o2_168
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos309o2c 169 - ((630959/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos309o2_br_169).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum309o2_170 : ((4320529/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 170, cos309o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 170, cos309o2c k)
      = (∑ k ∈ Finset.Icc 11 169, cos309o2c k) + cos309o2c 170 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 169) (by norm_num) cos309o2c
    simpa using h
  have hprev := psum309o2_169
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos309o2c 170 - ((-226727/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos309o2_br_170).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum309o2_171 : ((7734537/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 171, cos309o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 171, cos309o2c k)
      = (∑ k ∈ Finset.Icc 11 170, cos309o2c k) + cos309o2c 171 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 170) (by norm_num) cos309o2c
    simpa using h
  have hprev := psum309o2_170
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos309o2c 171 - ((-906481/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos309o2_br_171).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum309o2_172 : ((6840653/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 172, cos309o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 172, cos309o2c k)
      = (∑ k ∈ Finset.Icc 11 171, cos309o2c k) + cos309o2c 172 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 171) (by norm_num) cos309o2c
    simpa using h
  have hprev := psum309o2_171
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos309o2c 172 - ((-223461/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos309o2_br_172).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum309o2_173 : ((1657991/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 173, cos309o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 173, cos309o2c k)
      = (∑ k ∈ Finset.Icc 11 172, cos309o2c k) + cos309o2c 173 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 172) (by norm_num) cos309o2c
    simpa using h
  have hprev := psum309o2_172
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos309o2c 173 - ((-208649/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos309o2_br_173).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum309o2_174 : ((7260949/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 174, cos309o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 174, cos309o2c k)
      = (∑ k ∈ Finset.Icc 11 173, cos309o2c k) + cos309o2c 174 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 173) (by norm_num) cos309o2c
    simpa using h
  have hprev := psum309o2_173
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos309o2c 174 - ((25161/40000 : ℚ) : ℝ) :=
    (abs_le.mp cos309o2_br_174).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum309o2_175 : ((258153/31250 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 175, cos309o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 175, cos309o2c k)
      = (∑ k ∈ Finset.Icc 11 174, cos309o2c k) + cos309o2c 175 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 174) (by norm_num) cos309o2c
    simpa using h
  have hprev := psum309o2_174
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos309o2c 175 - ((999987/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos309o2_br_175).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum309o2_176 : ((8901671/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 176, cos309o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 176, cos309o2c k)
      = (∑ k ∈ Finset.Icc 11 175, cos309o2c k) + cos309o2c 176 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 175) (by norm_num) cos309o2c
    simpa using h
  have hprev := psum309o2_175
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos309o2c 176 - ((128163/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos309o2_br_176).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum309o2_177 : ((1090349/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 177, cos309o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 177, cos309o2c k)
      = (∑ k ∈ Finset.Icc 11 176, cos309o2c k) + cos309o2c 177 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 176) (by norm_num) cos309o2c
    simpa using h
  have hprev := psum309o2_176
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos309o2c 177 - ((-178839/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos309o2_br_177).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum309o2_178 : ((1571043/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 178, cos309o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 178, cos309o2c k)
      = (∑ k ∈ Finset.Icc 11 177, cos309o2c k) + cos309o2c 178 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 177) (by norm_num) cos309o2c
    simpa using h
  have hprev := psum309o2_177
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos309o2c 178 - ((-867537/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos309o2_br_178).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum309o2_179 : ((1382819/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 179, cos309o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 179, cos309o2c k)
      = (∑ k ∈ Finset.Icc 11 178, cos309o2c k) + cos309o2c 179 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 178) (by norm_num) cos309o2c
    simpa using h
  have hprev := psum309o2_178
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos309o2c 179 - ((-23527/25000 : ℚ) : ℝ) :=
    (abs_le.mp cos309o2_br_179).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum309o2_180 : ((3278511/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 180, cos309o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 180, cos309o2c k)
      = (∑ k ∈ Finset.Icc 11 179, cos309o2c k) + cos309o2c 180 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 179) (by norm_num) cos309o2c
    simpa using h
  have hprev := psum309o2_179
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos309o2c 180 - ((-357033/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos309o2_br_180).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum309o2_181 : ((878547/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 181, cos309o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 181, cos309o2c k)
      = (∑ k ∈ Finset.Icc 11 180, cos309o2c k) + cos309o2c 181 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 180) (by norm_num) cos309o2c
    simpa using h
  have hprev := psum309o2_180
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos309o2c 181 - ((235697/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos309o2_br_181).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum309o2_182 : ((80023/10000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 182, cos309o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 182, cos309o2c k)
      = (∑ k ∈ Finset.Icc 11 181, cos309o2c k) + cos309o2c 182 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 181) (by norm_num) cos309o2c
    simpa using h
  have hprev := psum309o2_181
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos309o2c 182 - ((243491/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos309o2_br_182).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum309o2_183 : ((4408681/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 183, cos309o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 183, cos309o2c k)
      = (∑ k ∈ Finset.Icc 11 182, cos309o2c k) + cos309o2c 183 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 182) (by norm_num) cos309o2c
    simpa using h
  have hprev := psum309o2_182
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos309o2c 183 - ((407551/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos309o2_br_183).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum309o2_184 : ((8928037/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 184, cos309o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 184, cos309o2c k)
      = (∑ k ∈ Finset.Icc 11 183, cos309o2c k) + cos309o2c 184 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 183) (by norm_num) cos309o2c
    simpa using h
  have hprev := psum309o2_183
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos309o2c 184 - ((22143/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos309o2_br_184).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum309o2_185 : ((8263767/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 185, cos309o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 185, cos309o2c k)
      = (∑ k ∈ Finset.Icc 11 184, cos309o2c k) + cos309o2c 185 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 184) (by norm_num) cos309o2c
    simpa using h
  have hprev := psum309o2_184
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos309o2c 185 - ((-66423/100000 : ℚ) : ℝ) :=
    (abs_le.mp cos309o2_br_185).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum309o2_186 : ((7263793/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 186, cos309o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 186, cos309o2c k)
      = (∑ k ∈ Finset.Icc 11 185, cos309o2c k) + cos309o2c 186 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 185) (by norm_num) cos309o2c
    simpa using h
  have hprev := psum309o2_185
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos309o2c 186 - ((-499967/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos309o2_br_186).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum309o2_187 : ((6579323/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 187, cos309o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 187, cos309o2c k)
      = (∑ k ∈ Finset.Icc 11 186, cos309o2c k) + cos309o2c 187 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 186) (by norm_num) cos309o2c
    simpa using h
  have hprev := psum309o2_186
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos309o2c 187 - ((-68443/100000 : ℚ) : ℝ) :=
    (abs_le.mp cos309o2_br_187).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum309o2_188 : ((6649399/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 188, cos309o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 188, cos309o2c k)
      = (∑ k ∈ Finset.Icc 11 187, cos309o2c k) + cos309o2c 188 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 187) (by norm_num) cos309o2c
    simpa using h
  have hprev := psum309o2_187
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos309o2c 188 - ((17529/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos309o2_br_188).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum309o2_189 : ((928289/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 189, cos309o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 189, cos309o2c k)
      = (∑ k ∈ Finset.Icc 11 188, cos309o2c k) + cos309o2c 189 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 188) (by norm_num) cos309o2c
    simpa using h
  have hprev := psum309o2_188
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos309o2c 189 - ((776953/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos309o2_br_189).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum309o2_190 : ((4208633/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 190, cos309o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 190, cos309o2c k)
      = (∑ k ∈ Finset.Icc 11 189, cos309o2c k) + cos309o2c 190 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 189) (by norm_num) cos309o2c
    simpa using h
  have hprev := psum309o2_189
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos309o2c 190 - ((495497/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos309o2_br_190).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum309o2_191 : ((9002691/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 191, cos309o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 191, cos309o2c k)
      = (∑ k ∈ Finset.Icc 11 190, cos309o2c k) + cos309o2c 191 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 190) (by norm_num) cos309o2c
    simpa using h
  have hprev := psum309o2_190
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos309o2c 191 - ((117093/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos309o2_br_191).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum309o2_192 : ((8822313/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 192, cos309o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 192, cos309o2c k)
      = (∑ k ∈ Finset.Icc 11 191, cos309o2c k) + cos309o2c 192 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 191) (by norm_num) cos309o2c
    simpa using h
  have hprev := psum309o2_191
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos309o2c 192 - ((-90169/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos309o2_br_192).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum309o2_193 : ((3994797/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 193, cos309o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 193, cos309o2c k)
      = (∑ k ∈ Finset.Icc 11 192, cos309o2c k) + cos309o2c 193 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 192) (by norm_num) cos309o2c
    simpa using h
  have hprev := psum309o2_192
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos309o2c 193 - ((-832679/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos309o2_br_193).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum309o2_194 : ((1402371/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 194, cos309o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 194, cos309o2c k)
      = (∑ k ∈ Finset.Icc 11 193, cos309o2c k) + cos309o2c 194 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 193) (by norm_num) cos309o2c
    simpa using h
  have hprev := psum309o2_193
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos309o2c 194 - ((-977699/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos309o2_br_194).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum309o2_195 : ((1295303/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 195, cos309o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 195, cos309o2c k)
      = (∑ k ∈ Finset.Icc 11 194, cos309o2c k) + cos309o2c 195 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 194) (by norm_num) cos309o2c
    simpa using h
  have hprev := psum309o2_194
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos309o2c 195 - ((-5353/10000 : ℚ) : ℝ) :=
    (abs_le.mp cos309o2_br_195).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum309o2_196 : ((6699991/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 196, cos309o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 196, cos309o2c k)
      = (∑ k ∈ Finset.Icc 11 195, cos309o2c k) + cos309o2c 196 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 195) (by norm_num) cos309o2c
    simpa using h
  have hprev := psum309o2_195
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos309o2c 196 - ((55879/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos309o2_br_196).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum309o2_197 : ((3773839/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 197, cos309o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 197, cos309o2c k)
      = (∑ k ∈ Finset.Icc 11 196, cos309o2c k) + cos309o2c 197 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 196) (by norm_num) cos309o2c
    simpa using h
  have hprev := psum309o2_196
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos309o2c 197 - ((847727/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos309o2_br_197).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum309o2_198 : ((8522839/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 198, cos309o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 198, cos309o2c k)
      = (∑ k ∈ Finset.Icc 11 197, cos309o2c k) + cos309o2c 198 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 197) (by norm_num) cos309o2c
    simpa using h
  have hprev := psum309o2_197
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos309o2c 198 - ((975201/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos309o2_br_198).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum309o2_199 : ((9061831/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 199, cos309o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 199, cos309o2c k)
      = (∑ k ∈ Finset.Icc 11 198, cos309o2c k) + cos309o2c 199 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 198) (by norm_num) cos309o2c
    simpa using h
  have hprev := psum309o2_198
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos309o2c 199 - ((67379/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos309o2_br_199).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum309o2_200 : ((4429041/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 200, cos309o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 200, cos309o2c k)
      = (∑ k ∈ Finset.Icc 11 199, cos309o2c k) + cos309o2c 200 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 199) (by norm_num) cos309o2c
    simpa using h
  have hprev := psum309o2_199
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos309o2c 200 - ((-203709/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos309o2_br_200).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum309o2_201 : ((2007483/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 201, cos309o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 201, cos309o2c k)
      = (∑ k ∈ Finset.Icc 11 200, cos309o2c k) + cos309o2c 201 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 200) (by norm_num) cos309o2c
    simpa using h
  have hprev := psum309o2_200
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos309o2c 201 - ((-82811/100000 : ℚ) : ℝ) :=
    (abs_le.mp cos309o2_br_201).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum309o2_202 : ((7044591/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 202, cos309o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 202, cos309o2c k)
      = (∑ k ∈ Finset.Icc 11 201, cos309o2c k) + cos309o2c 202 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 201) (by norm_num) cos309o2c
    simpa using h
  have hprev := psum309o2_201
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos309o2c 202 - ((-985301/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos309o2_br_202).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum309o2_203 : ((161261/25000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 203, cos309o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 203, cos309o2c k)
      = (∑ k ∈ Finset.Icc 11 202, cos309o2c k) + cos309o2c 203 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 202) (by norm_num) cos309o2c
    simpa using h
  have hprev := psum309o2_202
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos309o2c 203 - ((-594111/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos309o2_br_203).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum309o2_204 : ((6573143/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 204, cos309o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 204, cos309o2c k)
      = (∑ k ∈ Finset.Icc 11 203, cos309o2c k) + cos309o2c 204 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 203) (by norm_num) cos309o2c
    simpa using h
  have hprev := psum309o2_203
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos309o2c 204 - ((122743/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos309o2_br_204).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum309o2_205 : ((7342923/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 205, cos309o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 205, cos309o2c k)
      = (∑ k ∈ Finset.Icc 11 204, cos309o2c k) + cos309o2c 205 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 204) (by norm_num) cos309o2c
    simpa using h
  have hprev := psum309o2_204
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos309o2c 205 - ((38491/50000 : ℚ) : ℝ) :=
    (abs_le.mp cos309o2_br_205).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum309o2_206 : ((2085277/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 206, cos309o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 206, cos309o2c k)
      = (∑ k ∈ Finset.Icc 11 205, cos309o2c k) + cos309o2c 206 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 205) (by norm_num) cos309o2c
    simpa using h
  have hprev := psum309o2_205
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos309o2c 206 - ((39929/40000 : ℚ) : ℝ) :=
    (abs_le.mp cos309o2_br_206).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum309o2_207 : ((9032179/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 207, cos309o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 207, cos309o2c k)
      = (∑ k ∈ Finset.Icc 11 206, cos309o2c k) + cos309o2c 207 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 206) (by norm_num) cos309o2c
    simpa using h
  have hprev := psum309o2_206
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos309o2c 207 - ((691111/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos309o2_br_207).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum309o2_208 : ((9050581/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 208, cos309o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 208, cos309o2c k)
      = (∑ k ∈ Finset.Icc 11 207, cos309o2c k) + cos309o2c 208 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 207) (by norm_num) cos309o2c
    simpa using h
  have hprev := psum309o2_207
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos309o2c 208 - ((9221/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos309o2_br_208).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum309o2_209 : ((4194613/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 209, cos309o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 209, cos309o2c k)
      = (∑ k ∈ Finset.Icc 11 208, cos309o2c k) + cos309o2c 209 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 208) (by norm_num) cos309o2c
    simpa using h
  have hprev := psum309o2_208
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos309o2c 209 - ((-132263/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos309o2_br_209).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum309o2_210 : ((7395313/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 210, cos309o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 210, cos309o2c k)
      = (∑ k ∈ Finset.Icc 11 209, cos309o2c k) + cos309o2c 210 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 209) (by norm_num) cos309o2c
    simpa using h
  have hprev := psum309o2_209
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos309o2c 210 - ((-993873/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos309o2_br_210).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum309o2_211 : ((1645817/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 211, cos309o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 211, cos309o2c k)
      = (∑ k ∈ Finset.Icc 11 210, cos309o2c k) + cos309o2c 211 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 210) (by norm_num) cos309o2c
    simpa using h
  have hprev := psum309o2_210
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos309o2c 211 - ((-162401/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos309o2_br_211).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum309o2_212 : ((6367841/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 212, cos309o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 212, cos309o2c k)
      = (∑ k ∈ Finset.Icc 11 211, cos309o2c k) + cos309o2c 212 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 211) (by norm_num) cos309o2c
    simpa using h
  have hprev := psum309o2_211
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos309o2c 212 - ((-215387/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos309o2_br_212).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum309o2_213 : ((1371191/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 213, cos309o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 213, cos309o2c k)
      = (∑ k ∈ Finset.Icc 11 212, cos309o2c k) + cos309o2c 213 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 212) (by norm_num) cos309o2c
    simpa using h
  have hprev := psum309o2_212
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos309o2c 213 - ((244077/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos309o2_br_213).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum309o2_214 : ((7799613/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 214, cos309o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 214, cos309o2c k)
      = (∑ k ∈ Finset.Icc 11 213, cos309o2c k) + cos309o2c 214 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 213) (by norm_num) cos309o2c
    simpa using h
  have hprev := psum309o2_213
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos309o2c 214 - ((471849/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos309o2_br_214).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum309o2_215 : ((8727077/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 215, cos309o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 215, cos309o2c k)
      = (∑ k ∈ Finset.Icc 11 214, cos309o2c k) + cos309o2c 215 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 214) (by norm_num) cos309o2c
    simpa using h
  have hprev := psum309o2_214
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos309o2c 215 - ((57969/62500 : ℚ) : ℝ) :=
    (abs_le.mp cos309o2_br_215).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum309o2_216 : ((459029/50000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 216, cos309o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 216, cos309o2c k)
      = (∑ k ∈ Finset.Icc 11 215, cos309o2c k) + cos309o2c 216 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 215) (by norm_num) cos309o2c
    simpa using h
  have hprev := psum309o2_215
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos309o2c 216 - ((453543/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos309o2_br_216).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum309o2_217 : ((8940037/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 217, cos309o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 217, cos309o2c k)
      = (∑ k ∈ Finset.Icc 11 216, cos309o2c k) + cos309o2c 217 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 216) (by norm_num) cos309o2c
    simpa using h
  have hprev := psum309o2_216
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos309o2c 217 - ((-240503/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos309o2_br_217).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum309o2_218 : ((2031177/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 218, cos309o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 218, cos309o2c k)
      = (∑ k ∈ Finset.Icc 11 217, cos309o2c k) + cos309o2c 218 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 217) (by norm_num) cos309o2c
    simpa using h
  have hprev := psum309o2_217
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos309o2c 218 - ((-815289/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos309o2_br_218).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum309o2_219 : ((7128673/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 219, cos309o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 219, cos309o2c k)
      = (∑ k ∈ Finset.Icc 11 218, cos309o2c k) + cos309o2c 219 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 218) (by norm_num) cos309o2c
    simpa using h
  have hprev := psum309o2_218
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos309o2c 219 - ((-199199/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos309o2_br_219).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum309o2_220 : ((6427209/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 220, cos309o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 220, cos309o2c k)
      = (∑ k ∈ Finset.Icc 11 219, cos309o2c k) + cos309o2c 220 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 219) (by norm_num) cos309o2c
    simpa using h
  have hprev := psum309o2_219
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos309o2c 220 - ((-43839/62500 : ℚ) : ℝ) :=
    (abs_le.mp cos309o2_br_220).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum309o2_221 : ((317527/50000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 221, cos309o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 221, cos309o2c k)
      = (∑ k ∈ Finset.Icc 11 220, cos309o2c k) + cos309o2c 221 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 220) (by norm_num) cos309o2c
    simpa using h
  have hprev := psum309o2_220
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos309o2c 221 - ((-76629/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos309o2_br_221).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum309o2_222 : ((6932187/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 222, cos309o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 222, cos309o2c k)
      = (∑ k ∈ Finset.Icc 11 221, cos309o2c k) + cos309o2c 222 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 221) (by norm_num) cos309o2c
    simpa using h
  have hprev := psum309o2_221
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos309o2c 222 - ((581687/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos309o2_br_222).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum309o2_223 : ((987457/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 223, cos309o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 223, cos309o2c k)
      = (∑ k ∈ Finset.Icc 11 222, cos309o2c k) + cos309o2c 223 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 222) (by norm_num) cos309o2c
    simpa using h
  have hprev := psum309o2_222
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos309o2c 223 - ((967509/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos309o2_br_223).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum309o2_224 : ((2201551/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 224, cos309o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 224, cos309o2c k)
      = (∑ k ∈ Finset.Icc 11 223, cos309o2c k) + cos309o2c 224 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 223) (by norm_num) cos309o2c
    simpa using h
  have hprev := psum309o2_223
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos309o2c 224 - ((226647/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos309o2_br_224).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum309o2_225 : ((9238357/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 225, cos309o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 225, cos309o2c k)
      = (∑ k ∈ Finset.Icc 11 224, cos309o2c k) + cos309o2c 225 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 224) (by norm_num) cos309o2c
    simpa using h
  have hprev := psum309o2_224
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos309o2c 225 - ((432193/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos309o2_br_225).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum309o2_226 : ((2250587/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 226, cos309o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 226, cos309o2c k)
      = (∑ k ∈ Finset.Icc 11 225, cos309o2c k) + cos309o2c 226 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 225) (by norm_num) cos309o2c
    simpa using h
  have hprev := psum309o2_225
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos309o2c 226 - ((-235969/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos309o2_br_226).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum309o2_227 : ((16413/2000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 227, cos309o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 227, cos309o2c k)
      = (∑ k ∈ Finset.Icc 11 226, cos309o2c k) + cos309o2c 227 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 226) (by norm_num) cos309o2c
    simpa using h
  have hprev := psum309o2_226
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos309o2c 227 - ((-24869/31250 : ℚ) : ℝ) :=
    (abs_le.mp cos309o2_br_227).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum309o2_228 : ((7206871/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 228, cos309o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 228, cos309o2c k)
      = (∑ k ∈ Finset.Icc 11 227, cos309o2c k) + cos309o2c 228 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 227) (by norm_num) cos309o2c
    simpa using h
  have hprev := psum309o2_227
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos309o2c 228 - ((-999589/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos309o2_br_228).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum309o2_229 : ((3222551/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 229, cos309o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 229, cos309o2c k)
      = (∑ k ∈ Finset.Icc 11 228, cos309o2c k) + cos309o2c 229 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 228) (by norm_num) cos309o2c
    simpa using h
  have hprev := psum309o2_228
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos309o2c 229 - ((-761729/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos309o2_br_229).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum309o2_230 : ((6253479/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 230, cos309o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 230, cos309o2c k)
      = (∑ k ∈ Finset.Icc 11 229, cos309o2c k) + cos309o2c 230 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 229) (by norm_num) cos309o2c
    simpa using h
  have hprev := psum309o2_229
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos309o2c 230 - ((-191583/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos309o2_br_230).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum309o2_231 : ((3356503/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 231, cos309o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 231, cos309o2c k)
      = (∑ k ∈ Finset.Icc 11 230, cos309o2c k) + cos309o2c 231 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 230) (by norm_num) cos309o2c
    simpa using h
  have hprev := psum309o2_230
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos309o2c 231 - ((459567/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos309o2_br_231).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum309o2_232 : ((7623629/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 232, cos309o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 232, cos309o2c k)
      = (∑ k ∈ Finset.Icc 11 231, cos309o2c k) + cos309o2c 232 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 231) (by norm_num) cos309o2c
    simpa using h
  have hprev := psum309o2_231
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos309o2c 232 - ((910663/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos309o2_br_232).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum309o2_233 : ((8595257/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 233, cos309o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 233, cos309o2c k)
      = (∑ k ∈ Finset.Icc 11 232, cos309o2c k) + cos309o2c 233 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 232) (by norm_num) cos309o2c
    simpa using h
  have hprev := psum309o2_232
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos309o2c 233 - ((242917/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos309o2_br_233).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum309o2_234 : ((9216603/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 234, cos309o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 234, cos309o2c k)
      = (∑ k ∈ Finset.Icc 11 233, cos309o2c k) + cos309o2c 234 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 233) (by norm_num) cos309o2c
    simpa using h
  have hprev := psum309o2_233
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos309o2c 234 - ((310693/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos309o2_br_234).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum309o2_235 : ((9228223/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 235, cos309o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 235, cos309o2c k)
      = (∑ k ∈ Finset.Icc 11 234, cos309o2c k) + cos309o2c 235 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 234) (by norm_num) cos309o2c
    simpa using h
  have hprev := psum309o2_234
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos309o2c 235 - ((583/50000 : ℚ) : ℝ) :=
    (abs_le.mp cos309o2_br_235).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum309o2_236 : ((862747/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 236, cos309o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 236, cos309o2c k)
      = (∑ k ∈ Finset.Icc 11 235, cos309o2c k) + cos309o2c 236 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 235) (by norm_num) cos309o2c
    simpa using h
  have hprev := psum309o2_235
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos309o2c 236 - ((-600713/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos309o2_br_236).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum309o2_237 : ((7664499/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 237, cos309o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 237, cos309o2c k)
      = (∑ k ∈ Finset.Icc 11 236, cos309o2c k) + cos309o2c 237 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 236) (by norm_num) cos309o2c
    simpa using h
  have hprev := psum309o2_236
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos309o2c 237 - ((-962931/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos309o2_br_237).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum309o2_238 : ((673483/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 238, cos309o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 238, cos309o2c k)
      = (∑ k ∈ Finset.Icc 11 237, cos309o2c k) + cos309o2c 238 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 237) (by norm_num) cos309o2c
    simpa using h
  have hprev := psum309o2_237
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos309o2c 238 - ((-929629/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos309o2_br_238).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum309o2_239 : ((6215857/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 239, cos309o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 239, cos309o2c k)
      = (∑ k ∈ Finset.Icc 11 238, cos309o2c k) + cos309o2c 239 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 238) (by norm_num) cos309o2c
    simpa using h
  have hprev := psum309o2_238
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos309o2c 239 - ((-518933/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos309o2_br_239).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum309o2_240 : ((126303/20000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 240, cos309o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 240, cos309o2c k)
      = (∑ k ∈ Finset.Icc 11 239, cos309o2c k) + cos309o2c 240 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 239) (by norm_num) cos309o2c
    simpa using h
  have hprev := psum309o2_239
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos309o2c 240 - ((99333/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos309o2_br_240).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum309o2_241 : ((3495403/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 241, cos309o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 241, cos309o2c k)
      = (∑ k ∈ Finset.Icc 11 240, cos309o2c k) + cos309o2c 241 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 240) (by norm_num) cos309o2c
    simpa using h
  have hprev := psum309o2_240
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos309o2c 241 - ((42231/62500 : ℚ) : ℝ) :=
    (abs_le.mp cos309o2_br_241).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum309o2_242 : ((7972933/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 242, cos309o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 242, cos309o2c k)
      = (∑ k ∈ Finset.Icc 11 241, cos309o2c k) + cos309o2c 242 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 241) (by norm_num) cos309o2c
    simpa using h
  have hprev := psum309o2_241
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos309o2c 242 - ((982167/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos309o2_br_242).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum309o2_243 : ((4437109/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 243, cos309o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 243, cos309o2c k)
      = (∑ k ∈ Finset.Icc 11 242, cos309o2c k) + cos309o2c 243 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 242) (by norm_num) cos309o2c
    simpa using h
  have hprev := psum309o2_242
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos309o2c 243 - ((36053/40000 : ℚ) : ℝ) :=
    (abs_le.mp cos309o2_br_243).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum309o2_244 : ((9343319/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 244, cos309o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 244, cos309o2c k)
      = (∑ k ∈ Finset.Icc 11 243, cos309o2c k) + cos309o2c 244 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 243) (by norm_num) cos309o2c
    simpa using h
  have hprev := psum309o2_243
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos309o2c 244 - ((469141/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos309o2_br_244).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum309o2_245 : ((9200193/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 245, cos309o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 245, cos309o2c k)
      = (∑ k ∈ Finset.Icc 11 244, cos309o2c k) + cos309o2c 245 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 244) (by norm_num) cos309o2c
    simpa using h
  have hprev := psum309o2_244
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos309o2c 245 - ((-71543/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos309o2_br_245).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum309o2_246 : ((850193/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 246, cos309o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 246, cos309o2c k)
      = (∑ k ∈ Finset.Icc 11 245, cos309o2c k) + cos309o2c 246 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 245) (by norm_num) cos309o2c
    simpa using h
  have hprev := psum309o2_245
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos309o2c 246 - ((-698223/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos309o2_br_246).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum309o2_247 : ((7516493/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 247, cos309o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 247, cos309o2c k)
      = (∑ k ∈ Finset.Icc 11 246, cos309o2c k) + cos309o2c 247 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 246) (by norm_num) cos309o2c
    simpa using h
  have hprev := psum309o2_246
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos309o2c 247 - ((-985397/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos309o2_br_247).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum309o2_248 : ((6617373/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 248, cos309o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 248, cos309o2c k)
      = (∑ k ∈ Finset.Icc 11 247, cos309o2c k) + cos309o2c 248 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 247) (by norm_num) cos309o2c
    simpa using h
  have hprev := psum309o2_247
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos309o2c 248 - ((-22477/25000 : ℚ) : ℝ) :=
    (abs_le.mp cos309o2_br_248).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum309o2_249 : ((3070737/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 249, cos309o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 249, cos309o2c k)
      = (∑ k ∈ Finset.Icc 11 248, cos309o2c k) + cos309o2c 249 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 248) (by norm_num) cos309o2c
    simpa using h
  have hprev := psum309o2_248
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos309o2c 249 - ((-475859/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos309o2_br_249).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum309o2_250 : ((6264433/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 250, cos309o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 250, cos309o2c k)
      = (∑ k ∈ Finset.Icc 11 249, cos309o2c k) + cos309o2c 250 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 249) (by norm_num) cos309o2c
    simpa using h
  have hprev := psum309o2_249
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos309o2c 250 - ((122999/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos309o2_br_250).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

set_option maxHeartbeats 3200000 in
/-- **The Abel floor at `t = 309/2`.** -/
theorem psum309o2_floor : ∀ j : ℕ, 11 ≤ j → j ≤ 250 →
    ((0 : ℚ) : ℝ) ≤ ∑ k ∈ Finset.Icc 11 j, cos309o2c k := by
  intro j hj1 hj2
  interval_cases j
  · exact le_trans (by norm_num) psum309o2_11
  · exact le_trans (by norm_num) psum309o2_12
  · exact le_trans (by norm_num) psum309o2_13
  · exact le_trans (by norm_num) psum309o2_14
  · exact le_trans (by norm_num) psum309o2_15
  · exact le_trans (by norm_num) psum309o2_16
  · exact le_trans (by norm_num) psum309o2_17
  · exact le_trans (by norm_num) psum309o2_18
  · exact le_trans (by norm_num) psum309o2_19
  · exact le_trans (by norm_num) psum309o2_20
  · exact le_trans (by norm_num) psum309o2_21
  · exact le_trans (by norm_num) psum309o2_22
  · exact le_trans (by norm_num) psum309o2_23
  · exact le_trans (by norm_num) psum309o2_24
  · exact le_trans (by norm_num) psum309o2_25
  · exact le_trans (by norm_num) psum309o2_26
  · exact le_trans (by norm_num) psum309o2_27
  · exact le_trans (by norm_num) psum309o2_28
  · exact le_trans (by norm_num) psum309o2_29
  · exact le_trans (by norm_num) psum309o2_30
  · exact le_trans (by norm_num) psum309o2_31
  · exact le_trans (by norm_num) psum309o2_32
  · exact le_trans (by norm_num) psum309o2_33
  · exact le_trans (by norm_num) psum309o2_34
  · exact le_trans (by norm_num) psum309o2_35
  · exact le_trans (by norm_num) psum309o2_36
  · exact le_trans (by norm_num) psum309o2_37
  · exact le_trans (by norm_num) psum309o2_38
  · exact le_trans (by norm_num) psum309o2_39
  · exact le_trans (by norm_num) psum309o2_40
  · exact le_trans (by norm_num) psum309o2_41
  · exact le_trans (by norm_num) psum309o2_42
  · exact le_trans (by norm_num) psum309o2_43
  · exact le_trans (by norm_num) psum309o2_44
  · exact le_trans (by norm_num) psum309o2_45
  · exact le_trans (by norm_num) psum309o2_46
  · exact le_trans (by norm_num) psum309o2_47
  · exact le_trans (by norm_num) psum309o2_48
  · exact le_trans (by norm_num) psum309o2_49
  · exact le_trans (by norm_num) psum309o2_50
  · exact le_trans (by norm_num) psum309o2_51
  · exact le_trans (by norm_num) psum309o2_52
  · exact le_trans (by norm_num) psum309o2_53
  · exact le_trans (by norm_num) psum309o2_54
  · exact le_trans (by norm_num) psum309o2_55
  · exact le_trans (by norm_num) psum309o2_56
  · exact le_trans (by norm_num) psum309o2_57
  · exact le_trans (by norm_num) psum309o2_58
  · exact le_trans (by norm_num) psum309o2_59
  · exact le_trans (by norm_num) psum309o2_60
  · exact le_trans (by norm_num) psum309o2_61
  · exact le_trans (by norm_num) psum309o2_62
  · exact le_trans (by norm_num) psum309o2_63
  · exact le_trans (by norm_num) psum309o2_64
  · exact le_trans (by norm_num) psum309o2_65
  · exact le_trans (by norm_num) psum309o2_66
  · exact le_trans (by norm_num) psum309o2_67
  · exact le_trans (by norm_num) psum309o2_68
  · exact le_trans (by norm_num) psum309o2_69
  · exact le_trans (by norm_num) psum309o2_70
  · exact le_trans (by norm_num) psum309o2_71
  · exact le_trans (by norm_num) psum309o2_72
  · exact le_trans (by norm_num) psum309o2_73
  · exact le_trans (by norm_num) psum309o2_74
  · exact le_trans (by norm_num) psum309o2_75
  · exact le_trans (by norm_num) psum309o2_76
  · exact le_trans (by norm_num) psum309o2_77
  · exact le_trans (by norm_num) psum309o2_78
  · exact le_trans (by norm_num) psum309o2_79
  · exact le_trans (by norm_num) psum309o2_80
  · exact le_trans (by norm_num) psum309o2_81
  · exact le_trans (by norm_num) psum309o2_82
  · exact le_trans (by norm_num) psum309o2_83
  · exact le_trans (by norm_num) psum309o2_84
  · exact le_trans (by norm_num) psum309o2_85
  · exact le_trans (by norm_num) psum309o2_86
  · exact le_trans (by norm_num) psum309o2_87
  · exact le_trans (by norm_num) psum309o2_88
  · exact le_trans (by norm_num) psum309o2_89
  · exact le_trans (by norm_num) psum309o2_90
  · exact le_trans (by norm_num) psum309o2_91
  · exact le_trans (by norm_num) psum309o2_92
  · exact le_trans (by norm_num) psum309o2_93
  · exact le_trans (by norm_num) psum309o2_94
  · exact le_trans (by norm_num) psum309o2_95
  · exact le_trans (by norm_num) psum309o2_96
  · exact le_trans (by norm_num) psum309o2_97
  · exact le_trans (by norm_num) psum309o2_98
  · exact le_trans (by norm_num) psum309o2_99
  · exact le_trans (by norm_num) psum309o2_100
  · exact le_trans (by norm_num) psum309o2_101
  · exact le_trans (by norm_num) psum309o2_102
  · exact le_trans (by norm_num) psum309o2_103
  · exact le_trans (by norm_num) psum309o2_104
  · exact le_trans (by norm_num) psum309o2_105
  · exact le_trans (by norm_num) psum309o2_106
  · exact le_trans (by norm_num) psum309o2_107
  · exact le_trans (by norm_num) psum309o2_108
  · exact le_trans (by norm_num) psum309o2_109
  · exact le_trans (by norm_num) psum309o2_110
  · exact le_trans (by norm_num) psum309o2_111
  · exact le_trans (by norm_num) psum309o2_112
  · exact le_trans (by norm_num) psum309o2_113
  · exact le_trans (by norm_num) psum309o2_114
  · exact le_trans (by norm_num) psum309o2_115
  · exact le_trans (by norm_num) psum309o2_116
  · exact le_trans (by norm_num) psum309o2_117
  · exact le_trans (by norm_num) psum309o2_118
  · exact le_trans (by norm_num) psum309o2_119
  · exact le_trans (by norm_num) psum309o2_120
  · exact le_trans (by norm_num) psum309o2_121
  · exact le_trans (by norm_num) psum309o2_122
  · exact le_trans (by norm_num) psum309o2_123
  · exact le_trans (by norm_num) psum309o2_124
  · exact le_trans (by norm_num) psum309o2_125
  · exact le_trans (by norm_num) psum309o2_126
  · exact le_trans (by norm_num) psum309o2_127
  · exact le_trans (by norm_num) psum309o2_128
  · exact le_trans (by norm_num) psum309o2_129
  · exact le_trans (by norm_num) psum309o2_130
  · exact le_trans (by norm_num) psum309o2_131
  · exact le_trans (by norm_num) psum309o2_132
  · exact le_trans (by norm_num) psum309o2_133
  · exact le_trans (by norm_num) psum309o2_134
  · exact le_trans (by norm_num) psum309o2_135
  · exact le_trans (by norm_num) psum309o2_136
  · exact le_trans (by norm_num) psum309o2_137
  · exact le_trans (by norm_num) psum309o2_138
  · exact le_trans (by norm_num) psum309o2_139
  · exact le_trans (by norm_num) psum309o2_140
  · exact le_trans (by norm_num) psum309o2_141
  · exact le_trans (by norm_num) psum309o2_142
  · exact le_trans (by norm_num) psum309o2_143
  · exact le_trans (by norm_num) psum309o2_144
  · exact le_trans (by norm_num) psum309o2_145
  · exact le_trans (by norm_num) psum309o2_146
  · exact le_trans (by norm_num) psum309o2_147
  · exact le_trans (by norm_num) psum309o2_148
  · exact le_trans (by norm_num) psum309o2_149
  · exact le_trans (by norm_num) psum309o2_150
  · exact le_trans (by norm_num) psum309o2_151
  · exact le_trans (by norm_num) psum309o2_152
  · exact le_trans (by norm_num) psum309o2_153
  · exact le_trans (by norm_num) psum309o2_154
  · exact le_trans (by norm_num) psum309o2_155
  · exact le_trans (by norm_num) psum309o2_156
  · exact le_trans (by norm_num) psum309o2_157
  · exact le_trans (by norm_num) psum309o2_158
  · exact le_trans (by norm_num) psum309o2_159
  · exact le_trans (by norm_num) psum309o2_160
  · exact le_trans (by norm_num) psum309o2_161
  · exact le_trans (by norm_num) psum309o2_162
  · exact le_trans (by norm_num) psum309o2_163
  · exact le_trans (by norm_num) psum309o2_164
  · exact le_trans (by norm_num) psum309o2_165
  · exact le_trans (by norm_num) psum309o2_166
  · exact le_trans (by norm_num) psum309o2_167
  · exact le_trans (by norm_num) psum309o2_168
  · exact le_trans (by norm_num) psum309o2_169
  · exact le_trans (by norm_num) psum309o2_170
  · exact le_trans (by norm_num) psum309o2_171
  · exact le_trans (by norm_num) psum309o2_172
  · exact le_trans (by norm_num) psum309o2_173
  · exact le_trans (by norm_num) psum309o2_174
  · exact le_trans (by norm_num) psum309o2_175
  · exact le_trans (by norm_num) psum309o2_176
  · exact le_trans (by norm_num) psum309o2_177
  · exact le_trans (by norm_num) psum309o2_178
  · exact le_trans (by norm_num) psum309o2_179
  · exact le_trans (by norm_num) psum309o2_180
  · exact le_trans (by norm_num) psum309o2_181
  · exact le_trans (by norm_num) psum309o2_182
  · exact le_trans (by norm_num) psum309o2_183
  · exact le_trans (by norm_num) psum309o2_184
  · exact le_trans (by norm_num) psum309o2_185
  · exact le_trans (by norm_num) psum309o2_186
  · exact le_trans (by norm_num) psum309o2_187
  · exact le_trans (by norm_num) psum309o2_188
  · exact le_trans (by norm_num) psum309o2_189
  · exact le_trans (by norm_num) psum309o2_190
  · exact le_trans (by norm_num) psum309o2_191
  · exact le_trans (by norm_num) psum309o2_192
  · exact le_trans (by norm_num) psum309o2_193
  · exact le_trans (by norm_num) psum309o2_194
  · exact le_trans (by norm_num) psum309o2_195
  · exact le_trans (by norm_num) psum309o2_196
  · exact le_trans (by norm_num) psum309o2_197
  · exact le_trans (by norm_num) psum309o2_198
  · exact le_trans (by norm_num) psum309o2_199
  · exact le_trans (by norm_num) psum309o2_200
  · exact le_trans (by norm_num) psum309o2_201
  · exact le_trans (by norm_num) psum309o2_202
  · exact le_trans (by norm_num) psum309o2_203
  · exact le_trans (by norm_num) psum309o2_204
  · exact le_trans (by norm_num) psum309o2_205
  · exact le_trans (by norm_num) psum309o2_206
  · exact le_trans (by norm_num) psum309o2_207
  · exact le_trans (by norm_num) psum309o2_208
  · exact le_trans (by norm_num) psum309o2_209
  · exact le_trans (by norm_num) psum309o2_210
  · exact le_trans (by norm_num) psum309o2_211
  · exact le_trans (by norm_num) psum309o2_212
  · exact le_trans (by norm_num) psum309o2_213
  · exact le_trans (by norm_num) psum309o2_214
  · exact le_trans (by norm_num) psum309o2_215
  · exact le_trans (by norm_num) psum309o2_216
  · exact le_trans (by norm_num) psum309o2_217
  · exact le_trans (by norm_num) psum309o2_218
  · exact le_trans (by norm_num) psum309o2_219
  · exact le_trans (by norm_num) psum309o2_220
  · exact le_trans (by norm_num) psum309o2_221
  · exact le_trans (by norm_num) psum309o2_222
  · exact le_trans (by norm_num) psum309o2_223
  · exact le_trans (by norm_num) psum309o2_224
  · exact le_trans (by norm_num) psum309o2_225
  · exact le_trans (by norm_num) psum309o2_226
  · exact le_trans (by norm_num) psum309o2_227
  · exact le_trans (by norm_num) psum309o2_228
  · exact le_trans (by norm_num) psum309o2_229
  · exact le_trans (by norm_num) psum309o2_230
  · exact le_trans (by norm_num) psum309o2_231
  · exact le_trans (by norm_num) psum309o2_232
  · exact le_trans (by norm_num) psum309o2_233
  · exact le_trans (by norm_num) psum309o2_234
  · exact le_trans (by norm_num) psum309o2_235
  · exact le_trans (by norm_num) psum309o2_236
  · exact le_trans (by norm_num) psum309o2_237
  · exact le_trans (by norm_num) psum309o2_238
  · exact le_trans (by norm_num) psum309o2_239
  · exact le_trans (by norm_num) psum309o2_240
  · exact le_trans (by norm_num) psum309o2_241
  · exact le_trans (by norm_num) psum309o2_242
  · exact le_trans (by norm_num) psum309o2_243
  · exact le_trans (by norm_num) psum309o2_244
  · exact le_trans (by norm_num) psum309o2_245
  · exact le_trans (by norm_num) psum309o2_246
  · exact le_trans (by norm_num) psum309o2_247
  · exact le_trans (by norm_num) psum309o2_248
  · exact le_trans (by norm_num) psum309o2_249
  · exact le_trans (by norm_num) psum309o2_250

end CriticalLinePhasor.DVP

section AxiomAudit
#print axioms CriticalLinePhasor.DVP.psum309o2_floor
#print axioms CriticalLinePhasor.DVP.psum309o2_250
end AxiomAudit
