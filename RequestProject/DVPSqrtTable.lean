import RequestProject.DVPPhaseStation

/-!
# Shared station instruments: `n^{−1/2}` brackets and the sign plumbing

The seven-decimal `n^{−1/2}` brackets for `n = 1..100` (pure kernel
arithmetic), the half-power shift identities that reduce every station
cost to the single bracketed atom `N^{−1/2}`, the phase/real-part bridge,
the `−π` sign flip for negative stations, and the trivial `log 1`
bracket completing the log table at `n = 1`.
-/

open Complex Finset
open CriticalLinePhasor.ContourArgument CriticalLinePhasor.CarrierScale

noncomputable section

namespace CriticalLinePhasor.DVP

/-- The `log 1` bracket. -/
theorem log_br_1 : ((0 : ℚ) : ℝ) ≤ Real.log (1 : ℕ)
    ∧ Real.log (1 : ℕ) ≤ ((0 : ℚ) : ℝ) := by
  norm_num

/-- Half-power shifts: every station cost through `N^{−1/2}`. -/
theorem rpow_half_shifts {N : ℕ} (hN : 1 ≤ N) :
    (N:ℝ) ^ ((1/2 : ℝ)) = N * (N:ℝ) ^ (-(1/2 : ℝ))
    ∧ (N:ℝ) ^ (-(3/2 : ℝ)) = (N:ℝ) ^ (-(1/2 : ℝ)) / N
    ∧ (N:ℝ) ^ (-(5/2 : ℝ)) = (N:ℝ) ^ (-(1/2 : ℝ)) / N ^ 2 := by
  have hN0 : (0:ℝ) < N := by exact_mod_cast hN
  refine ⟨?_, ?_, ?_⟩
  · have h := Real.rpow_add hN0 1 (-(1/2 : ℝ))
    rw [Real.rpow_one] at h
    rw [← h]
    norm_num
  · have h := Real.rpow_add hN0 (-(1/2 : ℝ)) (-1 : ℝ)
    rw [Real.rpow_neg_one] at h
    rw [show (-(3/2 : ℝ)) = -(1/2 : ℝ) + (-1 : ℝ) by norm_num, h]
    ring
  · have h := Real.rpow_add hN0 (-(1/2 : ℝ)) (-2 : ℝ)
    have h2 : (N:ℝ) ^ ((-2 : ℝ)) = ((N:ℝ) ^ 2)⁻¹ := by
      rw [show ((-2:ℝ)) = ((-2 : ℤ) : ℝ) by norm_num, Real.rpow_intCast,
        zpow_neg]
      norm_num
    rw [show (-(5/2 : ℝ)) = -(1/2 : ℝ) + (-2 : ℝ) by norm_num, h, h2]
    ring

/-- The phase/real-part bridge. -/
theorem re_phase_eq (ψ : ℝ) (z : ℂ) :
    (Complex.exp ((ψ : ℝ) * Complex.I) * z).re
      = Real.cos ψ * z.re - Real.sin ψ * z.im := by
  rw [Complex.mul_re, Complex.exp_ofReal_mul_I_re,
    Complex.exp_ofReal_mul_I_im]

/-- The `−π` sign flip for negative stations. -/
theorem cos_sin_flip (φ x y : ℝ)
    (h : 0 < Real.cos φ * x - Real.sin φ * y) :
    Real.cos (φ - Real.pi) * x - Real.sin (φ - Real.pi) * y < 0 := by
  rw [Real.cos_sub_pi, Real.sin_sub_pi]
  linarith

/-- Periodicity of the proxy phase. -/
theorem cos_sin_shift (ψ : ℝ) (J : ℤ) :
    Real.cos (ψ + J * (2 * Real.pi)) = Real.cos ψ
      ∧ Real.sin (ψ + J * (2 * Real.pi)) = Real.sin ψ :=
  ⟨Real.cos_add_int_mul_two_pi ψ J, Real.sin_add_int_mul_two_pi ψ J⟩

theorem sq_br_1 :
    ((1 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) ^ (-(1/2 : ℝ))
      ∧ ((1 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ ((10000001/10000000 : ℚ) : ℝ) :=
  inv_sqrt_enclosure (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem sq_br_2 :
    ((7071067/10000000 : ℚ) : ℝ) ≤ ((2 : ℕ) : ℝ) ^ (-(1/2 : ℝ))
      ∧ ((2 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ ((1767767/2500000 : ℚ) : ℝ) :=
  inv_sqrt_enclosure (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem sq_br_3 :
    ((2886751/5000000 : ℚ) : ℝ) ≤ ((3 : ℕ) : ℝ) ^ (-(1/2 : ℝ))
      ∧ ((3 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ ((5773503/10000000 : ℚ) : ℝ) :=
  inv_sqrt_enclosure (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem sq_br_4 :
    ((1/2 : ℚ) : ℝ) ≤ ((4 : ℕ) : ℝ) ^ (-(1/2 : ℝ))
      ∧ ((4 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ ((5000001/10000000 : ℚ) : ℝ) :=
  inv_sqrt_enclosure (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem sq_br_5 :
    ((894427/2000000 : ℚ) : ℝ) ≤ ((5 : ℕ) : ℝ) ^ (-(1/2 : ℝ))
      ∧ ((5 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ ((559017/1250000 : ℚ) : ℝ) :=
  inv_sqrt_enclosure (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem sq_br_6 :
    ((2041241/5000000 : ℚ) : ℝ) ≤ ((6 : ℕ) : ℝ) ^ (-(1/2 : ℝ))
      ∧ ((6 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ ((4082483/10000000 : ℚ) : ℝ) :=
  inv_sqrt_enclosure (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem sq_br_7 :
    ((944911/2500000 : ℚ) : ℝ) ≤ ((7 : ℕ) : ℝ) ^ (-(1/2 : ℝ))
      ∧ ((7 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ ((755929/2000000 : ℚ) : ℝ) :=
  inv_sqrt_enclosure (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem sq_br_8 :
    ((3535533/10000000 : ℚ) : ℝ) ≤ ((8 : ℕ) : ℝ) ^ (-(1/2 : ℝ))
      ∧ ((8 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ ((1767767/5000000 : ℚ) : ℝ) :=
  inv_sqrt_enclosure (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem sq_br_9 :
    ((3333333/10000000 : ℚ) : ℝ) ≤ ((9 : ℕ) : ℝ) ^ (-(1/2 : ℝ))
      ∧ ((9 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ ((1666667/5000000 : ℚ) : ℝ) :=
  inv_sqrt_enclosure (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem sq_br_10 :
    ((3162277/10000000 : ℚ) : ℝ) ≤ ((10 : ℕ) : ℝ) ^ (-(1/2 : ℝ))
      ∧ ((10 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ ((1581139/5000000 : ℚ) : ℝ) :=
  inv_sqrt_enclosure (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem sq_br_11 :
    ((3015113/10000000 : ℚ) : ℝ) ≤ ((11 : ℕ) : ℝ) ^ (-(1/2 : ℝ))
      ∧ ((11 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ ((1507557/5000000 : ℚ) : ℝ) :=
  inv_sqrt_enclosure (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem sq_br_12 :
    ((2886751/10000000 : ℚ) : ℝ) ≤ ((12 : ℕ) : ℝ) ^ (-(1/2 : ℝ))
      ∧ ((12 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ ((90211/312500 : ℚ) : ℝ) :=
  inv_sqrt_enclosure (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem sq_br_13 :
    ((5547/20000 : ℚ) : ℝ) ≤ ((13 : ℕ) : ℝ) ^ (-(1/2 : ℝ))
      ∧ ((13 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ ((2773501/10000000 : ℚ) : ℝ) :=
  inv_sqrt_enclosure (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem sq_br_14 :
    ((668153/2500000 : ℚ) : ℝ) ≤ ((14 : ℕ) : ℝ) ^ (-(1/2 : ℝ))
      ∧ ((14 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ ((2672613/10000000 : ℚ) : ℝ) :=
  inv_sqrt_enclosure (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem sq_br_15 :
    ((645497/2500000 : ℚ) : ℝ) ≤ ((15 : ℕ) : ℝ) ^ (-(1/2 : ℝ))
      ∧ ((15 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ ((2581989/10000000 : ℚ) : ℝ) :=
  inv_sqrt_enclosure (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem sq_br_16 :
    ((1/4 : ℚ) : ℝ) ≤ ((16 : ℕ) : ℝ) ^ (-(1/2 : ℝ))
      ∧ ((16 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ ((2500001/10000000 : ℚ) : ℝ) :=
  inv_sqrt_enclosure (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem sq_br_17 :
    ((606339/2500000 : ℚ) : ℝ) ≤ ((17 : ℕ) : ℝ) ^ (-(1/2 : ℝ))
      ∧ ((17 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ ((2425357/10000000 : ℚ) : ℝ) :=
  inv_sqrt_enclosure (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem sq_br_18 :
    ((1178511/5000000 : ℚ) : ℝ) ≤ ((18 : ℕ) : ℝ) ^ (-(1/2 : ℝ))
      ∧ ((18 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ ((2357023/10000000 : ℚ) : ℝ) :=
  inv_sqrt_enclosure (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem sq_br_19 :
    ((2294157/10000000 : ℚ) : ℝ) ≤ ((19 : ℕ) : ℝ) ^ (-(1/2 : ℝ))
      ∧ ((19 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ ((1147079/5000000 : ℚ) : ℝ) :=
  inv_sqrt_enclosure (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem sq_br_20 :
    ((2236067/10000000 : ℚ) : ℝ) ≤ ((20 : ℕ) : ℝ) ^ (-(1/2 : ℝ))
      ∧ ((20 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ ((559017/2500000 : ℚ) : ℝ) :=
  inv_sqrt_enclosure (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem sq_br_21 :
    ((1091089/5000000 : ℚ) : ℝ) ≤ ((21 : ℕ) : ℝ) ^ (-(1/2 : ℝ))
      ∧ ((21 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ ((2182179/10000000 : ℚ) : ℝ) :=
  inv_sqrt_enclosure (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem sq_br_22 :
    ((2132007/10000000 : ℚ) : ℝ) ≤ ((22 : ℕ) : ℝ) ^ (-(1/2 : ℝ))
      ∧ ((22 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ ((266501/1250000 : ℚ) : ℝ) :=
  inv_sqrt_enclosure (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem sq_br_23 :
    ((260643/1250000 : ℚ) : ℝ) ≤ ((23 : ℕ) : ℝ) ^ (-(1/2 : ℝ))
      ∧ ((23 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ ((417029/2000000 : ℚ) : ℝ) :=
  inv_sqrt_enclosure (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem sq_br_24 :
    ((2041241/10000000 : ℚ) : ℝ) ≤ ((24 : ℕ) : ℝ) ^ (-(1/2 : ℝ))
      ∧ ((24 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ ((1020621/5000000 : ℚ) : ℝ) :=
  inv_sqrt_enclosure (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem sq_br_25 :
    ((1/5 : ℚ) : ℝ) ≤ ((25 : ℕ) : ℝ) ^ (-(1/2 : ℝ))
      ∧ ((25 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ ((2000001/10000000 : ℚ) : ℝ) :=
  inv_sqrt_enclosure (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem sq_br_26 :
    ((1961161/10000000 : ℚ) : ℝ) ≤ ((26 : ℕ) : ℝ) ^ (-(1/2 : ℝ))
      ∧ ((26 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ ((980581/5000000 : ℚ) : ℝ) :=
  inv_sqrt_enclosure (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem sq_br_27 :
    ((3849/20000 : ℚ) : ℝ) ≤ ((27 : ℕ) : ℝ) ^ (-(1/2 : ℝ))
      ∧ ((27 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ ((1924501/10000000 : ℚ) : ℝ) :=
  inv_sqrt_enclosure (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem sq_br_28 :
    ((944911/5000000 : ℚ) : ℝ) ≤ ((28 : ℕ) : ℝ) ^ (-(1/2 : ℝ))
      ∧ ((28 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ ((1889823/10000000 : ℚ) : ℝ) :=
  inv_sqrt_enclosure (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem sq_br_29 :
    ((1856953/10000000 : ℚ) : ℝ) ≤ ((29 : ℕ) : ℝ) ^ (-(1/2 : ℝ))
      ∧ ((29 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ ((928477/5000000 : ℚ) : ℝ) :=
  inv_sqrt_enclosure (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem sq_br_30 :
    ((1825741/10000000 : ℚ) : ℝ) ≤ ((30 : ℕ) : ℝ) ^ (-(1/2 : ℝ))
      ∧ ((30 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ ((912871/5000000 : ℚ) : ℝ) :=
  inv_sqrt_enclosure (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem sq_br_31 :
    ((1796053/10000000 : ℚ) : ℝ) ≤ ((31 : ℕ) : ℝ) ^ (-(1/2 : ℝ))
      ∧ ((31 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ ((898027/5000000 : ℚ) : ℝ) :=
  inv_sqrt_enclosure (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem sq_br_32 :
    ((883883/5000000 : ℚ) : ℝ) ≤ ((32 : ℕ) : ℝ) ^ (-(1/2 : ℝ))
      ∧ ((32 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ ((1767767/10000000 : ℚ) : ℝ) :=
  inv_sqrt_enclosure (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem sq_br_33 :
    ((217597/1250000 : ℚ) : ℝ) ≤ ((33 : ℕ) : ℝ) ^ (-(1/2 : ℝ))
      ∧ ((33 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ ((1740777/10000000 : ℚ) : ℝ) :=
  inv_sqrt_enclosure (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem sq_br_34 :
    ((342997/2000000 : ℚ) : ℝ) ≤ ((34 : ℕ) : ℝ) ^ (-(1/2 : ℝ))
      ∧ ((34 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ ((857493/5000000 : ℚ) : ℝ) :=
  inv_sqrt_enclosure (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem sq_br_35 :
    ((422577/2500000 : ℚ) : ℝ) ≤ ((35 : ℕ) : ℝ) ^ (-(1/2 : ℝ))
      ∧ ((35 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ ((1690309/10000000 : ℚ) : ℝ) :=
  inv_sqrt_enclosure (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem sq_br_36 :
    ((833333/5000000 : ℚ) : ℝ) ≤ ((36 : ℕ) : ℝ) ^ (-(1/2 : ℝ))
      ∧ ((36 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ ((1666667/10000000 : ℚ) : ℝ) :=
  inv_sqrt_enclosure (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem sq_br_37 :
    ((1643989/10000000 : ℚ) : ℝ) ≤ ((37 : ℕ) : ℝ) ^ (-(1/2 : ℝ))
      ∧ ((37 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ ((164399/1000000 : ℚ) : ℝ) :=
  inv_sqrt_enclosure (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem sq_br_38 :
    ((811107/5000000 : ℚ) : ℝ) ≤ ((38 : ℕ) : ℝ) ^ (-(1/2 : ℝ))
      ∧ ((38 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ ((324443/2000000 : ℚ) : ℝ) :=
  inv_sqrt_enclosure (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem sq_br_39 :
    ((1601281/10000000 : ℚ) : ℝ) ≤ ((39 : ℕ) : ℝ) ^ (-(1/2 : ℝ))
      ∧ ((39 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ ((800641/5000000 : ℚ) : ℝ) :=
  inv_sqrt_enclosure (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem sq_br_40 :
    ((790569/5000000 : ℚ) : ℝ) ≤ ((40 : ℕ) : ℝ) ^ (-(1/2 : ℝ))
      ∧ ((40 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ ((1581139/10000000 : ℚ) : ℝ) :=
  inv_sqrt_enclosure (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem sq_br_41 :
    ((1561737/10000000 : ℚ) : ℝ) ≤ ((41 : ℕ) : ℝ) ^ (-(1/2 : ℝ))
      ∧ ((41 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ ((780869/5000000 : ℚ) : ℝ) :=
  inv_sqrt_enclosure (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem sq_br_42 :
    ((1543033/10000000 : ℚ) : ℝ) ≤ ((42 : ℕ) : ℝ) ^ (-(1/2 : ℝ))
      ∧ ((42 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ ((771517/5000000 : ℚ) : ℝ) :=
  inv_sqrt_enclosure (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem sq_br_43 :
    ((304997/2000000 : ℚ) : ℝ) ≤ ((43 : ℕ) : ℝ) ^ (-(1/2 : ℝ))
      ∧ ((43 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ ((762493/5000000 : ℚ) : ℝ) :=
  inv_sqrt_enclosure (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem sq_br_44 :
    ((376889/2500000 : ℚ) : ℝ) ≤ ((44 : ℕ) : ℝ) ^ (-(1/2 : ℝ))
      ∧ ((44 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ ((1507557/10000000 : ℚ) : ℝ) :=
  inv_sqrt_enclosure (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem sq_br_45 :
    ((1490711/10000000 : ℚ) : ℝ) ≤ ((45 : ℕ) : ℝ) ^ (-(1/2 : ℝ))
      ∧ ((45 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ ((186339/1250000 : ℚ) : ℝ) :=
  inv_sqrt_enclosure (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem sq_br_46 :
    ((1474419/10000000 : ℚ) : ℝ) ≤ ((46 : ℕ) : ℝ) ^ (-(1/2 : ℝ))
      ∧ ((46 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ ((73721/500000 : ℚ) : ℝ) :=
  inv_sqrt_enclosure (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem sq_br_47 :
    ((1458649/10000000 : ℚ) : ℝ) ≤ ((47 : ℕ) : ℝ) ^ (-(1/2 : ℝ))
      ∧ ((47 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ ((29173/200000 : ℚ) : ℝ) :=
  inv_sqrt_enclosure (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem sq_br_48 :
    ((11547/80000 : ℚ) : ℝ) ≤ ((48 : ℕ) : ℝ) ^ (-(1/2 : ℝ))
      ∧ ((48 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ ((90211/625000 : ℚ) : ℝ) :=
  inv_sqrt_enclosure (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem sq_br_49 :
    ((1428571/10000000 : ℚ) : ℝ) ≤ ((49 : ℕ) : ℝ) ^ (-(1/2 : ℝ))
      ∧ ((49 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ ((357143/2500000 : ℚ) : ℝ) :=
  inv_sqrt_enclosure (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem sq_br_50 :
    ((1414213/10000000 : ℚ) : ℝ) ≤ ((50 : ℕ) : ℝ) ^ (-(1/2 : ℝ))
      ∧ ((50 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ ((707107/5000000 : ℚ) : ℝ) :=
  inv_sqrt_enclosure (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem sq_br_51 :
    ((35007/250000 : ℚ) : ℝ) ≤ ((51 : ℕ) : ℝ) ^ (-(1/2 : ℝ))
      ∧ ((51 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ ((1400281/10000000 : ℚ) : ℝ) :=
  inv_sqrt_enclosure (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem sq_br_52 :
    ((5547/40000 : ℚ) : ℝ) ≤ ((52 : ℕ) : ℝ) ^ (-(1/2 : ℝ))
      ∧ ((52 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ ((1386751/10000000 : ℚ) : ℝ) :=
  inv_sqrt_enclosure (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem sq_br_53 :
    ((274721/2000000 : ℚ) : ℝ) ≤ ((53 : ℕ) : ℝ) ^ (-(1/2 : ℝ))
      ∧ ((53 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ ((686803/5000000 : ℚ) : ℝ) :=
  inv_sqrt_enclosure (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem sq_br_54 :
    ((1360827/10000000 : ℚ) : ℝ) ≤ ((54 : ℕ) : ℝ) ^ (-(1/2 : ℝ))
      ∧ ((54 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ ((340207/2500000 : ℚ) : ℝ) :=
  inv_sqrt_enclosure (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem sq_br_55 :
    ((1348399/10000000 : ℚ) : ℝ) ≤ ((55 : ℕ) : ℝ) ^ (-(1/2 : ℝ))
      ∧ ((55 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ ((3371/25000 : ℚ) : ℝ) :=
  inv_sqrt_enclosure (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem sq_br_56 :
    ((668153/5000000 : ℚ) : ℝ) ≤ ((56 : ℕ) : ℝ) ^ (-(1/2 : ℝ))
      ∧ ((56 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ ((1336307/10000000 : ℚ) : ℝ) :=
  inv_sqrt_enclosure (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem sq_br_57 :
    ((331133/2500000 : ℚ) : ℝ) ≤ ((57 : ℕ) : ℝ) ^ (-(1/2 : ℝ))
      ∧ ((57 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ ((1324533/10000000 : ℚ) : ℝ) :=
  inv_sqrt_enclosure (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem sq_br_58 :
    ((164133/1250000 : ℚ) : ℝ) ≤ ((58 : ℕ) : ℝ) ^ (-(1/2 : ℝ))
      ∧ ((58 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ ((262613/2000000 : ℚ) : ℝ) :=
  inv_sqrt_enclosure (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem sq_br_59 :
    ((1301889/10000000 : ℚ) : ℝ) ≤ ((59 : ℕ) : ℝ) ^ (-(1/2 : ℝ))
      ∧ ((59 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ ((130189/1000000 : ℚ) : ℝ) :=
  inv_sqrt_enclosure (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem sq_br_60 :
    ((645497/5000000 : ℚ) : ℝ) ≤ ((60 : ℕ) : ℝ) ^ (-(1/2 : ℝ))
      ∧ ((60 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ ((258199/2000000 : ℚ) : ℝ) :=
  inv_sqrt_enclosure (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem sq_br_61 :
    ((80023/625000 : ℚ) : ℝ) ≤ ((61 : ℕ) : ℝ) ^ (-(1/2 : ℝ))
      ∧ ((61 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ ((1280369/10000000 : ℚ) : ℝ) :=
  inv_sqrt_enclosure (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem sq_br_62 :
    ((1270001/10000000 : ℚ) : ℝ) ≤ ((62 : ℕ) : ℝ) ^ (-(1/2 : ℝ))
      ∧ ((62 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ ((635001/5000000 : ℚ) : ℝ) :=
  inv_sqrt_enclosure (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem sq_br_63 :
    ((1259881/10000000 : ℚ) : ℝ) ≤ ((63 : ℕ) : ℝ) ^ (-(1/2 : ℝ))
      ∧ ((63 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ ((629941/5000000 : ℚ) : ℝ) :=
  inv_sqrt_enclosure (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem sq_br_64 :
    ((1/8 : ℚ) : ℝ) ≤ ((64 : ℕ) : ℝ) ^ (-(1/2 : ℝ))
      ∧ ((64 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ ((1250001/10000000 : ℚ) : ℝ) :=
  inv_sqrt_enclosure (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem sq_br_65 :
    ((1240347/10000000 : ℚ) : ℝ) ≤ ((65 : ℕ) : ℝ) ^ (-(1/2 : ℝ))
      ∧ ((65 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ ((310087/2500000 : ℚ) : ℝ) :=
  inv_sqrt_enclosure (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem sq_br_66 :
    ((615457/5000000 : ℚ) : ℝ) ≤ ((66 : ℕ) : ℝ) ^ (-(1/2 : ℝ))
      ∧ ((66 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ ((246183/2000000 : ℚ) : ℝ) :=
  inv_sqrt_enclosure (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem sq_br_67 :
    ((610847/5000000 : ℚ) : ℝ) ≤ ((67 : ℕ) : ℝ) ^ (-(1/2 : ℝ))
      ∧ ((67 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ ((244339/2000000 : ℚ) : ℝ) :=
  inv_sqrt_enclosure (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem sq_br_68 :
    ((606339/5000000 : ℚ) : ℝ) ≤ ((68 : ℕ) : ℝ) ^ (-(1/2 : ℝ))
      ∧ ((68 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ ((1212679/10000000 : ℚ) : ℝ) :=
  inv_sqrt_enclosure (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem sq_br_69 :
    ((601929/5000000 : ℚ) : ℝ) ≤ ((69 : ℕ) : ℝ) ^ (-(1/2 : ℝ))
      ∧ ((69 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ ((1203859/10000000 : ℚ) : ℝ) :=
  inv_sqrt_enclosure (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem sq_br_70 :
    ((298807/2500000 : ℚ) : ℝ) ≤ ((70 : ℕ) : ℝ) ^ (-(1/2 : ℝ))
      ∧ ((70 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ ((1195229/10000000 : ℚ) : ℝ) :=
  inv_sqrt_enclosure (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem sq_br_71 :
    ((1186781/10000000 : ℚ) : ℝ) ≤ ((71 : ℕ) : ℝ) ^ (-(1/2 : ℝ))
      ∧ ((71 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ ((593391/5000000 : ℚ) : ℝ) :=
  inv_sqrt_enclosure (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem sq_br_72 :
    ((1178511/10000000 : ℚ) : ℝ) ≤ ((72 : ℕ) : ℝ) ^ (-(1/2 : ℝ))
      ∧ ((72 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ ((73657/625000 : ℚ) : ℝ) :=
  inv_sqrt_enclosure (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem sq_br_73 :
    ((1170411/10000000 : ℚ) : ℝ) ≤ ((73 : ℕ) : ℝ) ^ (-(1/2 : ℝ))
      ∧ ((73 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ ((292603/2500000 : ℚ) : ℝ) :=
  inv_sqrt_enclosure (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem sq_br_74 :
    ((290619/2500000 : ℚ) : ℝ) ≤ ((74 : ℕ) : ℝ) ^ (-(1/2 : ℝ))
      ∧ ((74 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ ((1162477/10000000 : ℚ) : ℝ) :=
  inv_sqrt_enclosure (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem sq_br_75 :
    ((11547/100000 : ℚ) : ℝ) ≤ ((75 : ℕ) : ℝ) ^ (-(1/2 : ℝ))
      ∧ ((75 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ ((1154701/10000000 : ℚ) : ℝ) :=
  inv_sqrt_enclosure (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem sq_br_76 :
    ((573539/5000000 : ℚ) : ℝ) ≤ ((76 : ℕ) : ℝ) ^ (-(1/2 : ℝ))
      ∧ ((76 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ ((1147079/10000000 : ℚ) : ℝ) :=
  inv_sqrt_enclosure (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem sq_br_77 :
    ((227921/2000000 : ℚ) : ℝ) ≤ ((77 : ℕ) : ℝ) ^ (-(1/2 : ℝ))
      ∧ ((77 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ ((569803/5000000 : ℚ) : ℝ) :=
  inv_sqrt_enclosure (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem sq_br_78 :
    ((1132277/10000000 : ℚ) : ℝ) ≤ ((78 : ℕ) : ℝ) ^ (-(1/2 : ℝ))
      ∧ ((78 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ ((566139/5000000 : ℚ) : ℝ) :=
  inv_sqrt_enclosure (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem sq_br_79 :
    ((1125087/10000000 : ℚ) : ℝ) ≤ ((79 : ℕ) : ℝ) ^ (-(1/2 : ℝ))
      ∧ ((79 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ ((35159/312500 : ℚ) : ℝ) :=
  inv_sqrt_enclosure (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem sq_br_80 :
    ((1118033/10000000 : ℚ) : ℝ) ≤ ((80 : ℕ) : ℝ) ^ (-(1/2 : ℝ))
      ∧ ((80 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ ((559017/5000000 : ℚ) : ℝ) :=
  inv_sqrt_enclosure (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem sq_br_81 :
    ((1111111/10000000 : ℚ) : ℝ) ≤ ((81 : ℕ) : ℝ) ^ (-(1/2 : ℝ))
      ∧ ((81 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ ((138889/1250000 : ℚ) : ℝ) :=
  inv_sqrt_enclosure (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem sq_br_82 :
    ((220863/2000000 : ℚ) : ℝ) ≤ ((82 : ℕ) : ℝ) ^ (-(1/2 : ℝ))
      ∧ ((82 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ ((276079/2500000 : ℚ) : ℝ) :=
  inv_sqrt_enclosure (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem sq_br_83 :
    ((548821/5000000 : ℚ) : ℝ) ≤ ((83 : ℕ) : ℝ) ^ (-(1/2 : ℝ))
      ∧ ((83 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ ((1097643/10000000 : ℚ) : ℝ) :=
  inv_sqrt_enclosure (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem sq_br_84 :
    ((1091089/10000000 : ℚ) : ℝ) ≤ ((84 : ℕ) : ℝ) ^ (-(1/2 : ℝ))
      ∧ ((84 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ ((109109/1000000 : ℚ) : ℝ) :=
  inv_sqrt_enclosure (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem sq_br_85 :
    ((271163/2500000 : ℚ) : ℝ) ≤ ((85 : ℕ) : ℝ) ^ (-(1/2 : ℝ))
      ∧ ((85 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ ((1084653/10000000 : ℚ) : ℝ) :=
  inv_sqrt_enclosure (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem sq_br_86 :
    ((1078327/10000000 : ℚ) : ℝ) ≤ ((86 : ℕ) : ℝ) ^ (-(1/2 : ℝ))
      ∧ ((86 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ ((134791/1250000 : ℚ) : ℝ) :=
  inv_sqrt_enclosure (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem sq_br_87 :
    ((67007/625000 : ℚ) : ℝ) ≤ ((87 : ℕ) : ℝ) ^ (-(1/2 : ℝ))
      ∧ ((87 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ ((1072113/10000000 : ℚ) : ℝ) :=
  inv_sqrt_enclosure (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem sq_br_88 :
    ((1066003/10000000 : ℚ) : ℝ) ≤ ((88 : ℕ) : ℝ) ^ (-(1/2 : ℝ))
      ∧ ((88 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ ((266501/2500000 : ℚ) : ℝ) :=
  inv_sqrt_enclosure (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem sq_br_89 :
    ((1059997/10000000 : ℚ) : ℝ) ≤ ((89 : ℕ) : ℝ) ^ (-(1/2 : ℝ))
      ∧ ((89 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ ((529999/5000000 : ℚ) : ℝ) :=
  inv_sqrt_enclosure (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem sq_br_90 :
    ((263523/2500000 : ℚ) : ℝ) ≤ ((90 : ℕ) : ℝ) ^ (-(1/2 : ℝ))
      ∧ ((90 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ ((1054093/10000000 : ℚ) : ℝ) :=
  inv_sqrt_enclosure (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem sq_br_91 :
    ((262071/2500000 : ℚ) : ℝ) ≤ ((91 : ℕ) : ℝ) ^ (-(1/2 : ℝ))
      ∧ ((91 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ ((209657/2000000 : ℚ) : ℝ) :=
  inv_sqrt_enclosure (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem sq_br_92 :
    ((260643/2500000 : ℚ) : ℝ) ≤ ((92 : ℕ) : ℝ) ^ (-(1/2 : ℝ))
      ∧ ((92 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ ((1042573/10000000 : ℚ) : ℝ) :=
  inv_sqrt_enclosure (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem sq_br_93 :
    ((1036951/10000000 : ℚ) : ℝ) ≤ ((93 : ℕ) : ℝ) ^ (-(1/2 : ℝ))
      ∧ ((93 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ ((129619/1250000 : ℚ) : ℝ) :=
  inv_sqrt_enclosure (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem sq_br_94 :
    ((1031421/10000000 : ℚ) : ℝ) ≤ ((94 : ℕ) : ℝ) ^ (-(1/2 : ℝ))
      ∧ ((94 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ ((515711/5000000 : ℚ) : ℝ) :=
  inv_sqrt_enclosure (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem sq_br_95 :
    ((512989/5000000 : ℚ) : ℝ) ≤ ((95 : ℕ) : ℝ) ^ (-(1/2 : ℝ))
      ∧ ((95 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ ((1025979/10000000 : ℚ) : ℝ) :=
  inv_sqrt_enclosure (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem sq_br_96 :
    ((51031/500000 : ℚ) : ℝ) ≤ ((96 : ℕ) : ℝ) ^ (-(1/2 : ℝ))
      ∧ ((96 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ ((1020621/10000000 : ℚ) : ℝ) :=
  inv_sqrt_enclosure (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem sq_br_97 :
    ((507673/5000000 : ℚ) : ℝ) ≤ ((97 : ℕ) : ℝ) ^ (-(1/2 : ℝ))
      ∧ ((97 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ ((1015347/10000000 : ℚ) : ℝ) :=
  inv_sqrt_enclosure (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem sq_br_98 :
    ((126269/1250000 : ℚ) : ℝ) ≤ ((98 : ℕ) : ℝ) ^ (-(1/2 : ℝ))
      ∧ ((98 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ ((1010153/10000000 : ℚ) : ℝ) :=
  inv_sqrt_enclosure (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem sq_br_99 :
    ((1005037/10000000 : ℚ) : ℝ) ≤ ((99 : ℕ) : ℝ) ^ (-(1/2 : ℝ))
      ∧ ((99 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ ((502519/5000000 : ℚ) : ℝ) :=
  inv_sqrt_enclosure (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem sq_br_100 :
    ((999999/10000000 : ℚ) : ℝ) ≤ ((100 : ℕ) : ℝ) ^ (-(1/2 : ℝ))
      ∧ ((100 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ ((1/10 : ℚ) : ℝ) :=
  inv_sqrt_enclosure (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

end CriticalLinePhasor.DVP

section AxiomAudit
#print axioms CriticalLinePhasor.DVP.rpow_half_shifts
#print axioms CriticalLinePhasor.DVP.sq_br_1
#print axioms CriticalLinePhasor.DVP.sq_br_100
end AxiomAudit
