import RequestProject.ZetaSectorBank

/-!
# The μ6 angle-sector balance law is FALSE, unconditionally

`ZetaSectorBank.AngleSectorBalanceLaw` asserts that at every on-line zero of `ζ` the antipodal
sector channels agree in the limit (`imbalance N t → 0`).  This file refutes it, at *every*
ordinate, with no hypothesis on `t` and no appeal to the location of any zero.

**The mechanism.**  A sector is an arc of angular width `2π/6 = π/3`.  Every phasor assigned to
sector `j` lies within `π/6` of that sector's midpoint direction, so its component along that
direction is at least `cos(π/6) = √3/2` times its modulus.  The antipodal sector `j+3` is the same
arc rotated by `π`, so its phasors have a *negative* component along the same direction, again of
size at least `√3/2` times their modulus.  Subtracting therefore ADDS the two masses instead of
cancelling them:

    ‖S_j − S_{j+3}‖ ≥ Re(e^{−i·mid j}(S_j − S_{j+3})) ≥ (√3/2)·(M_j + M_{j+3}),

and the three antipodal pairs sweep every term of the bank exactly once, giving

    `imbalance_ge_half_mass` :  (√3/2) · Σ_{n ≤ N} ‖zetaTerm t n‖  ≤  imbalance N t.

Since the mass `Σ_{n≤N} Λ(n)/√n` is unbounded, the imbalance is unbounded, so
`SectorBalanceAt t` fails for every real `t` (`not_sectorBalanceAt`), and the law holds only if
`ζ` has no zero on the critical line (`angleSectorBalanceLaw_iff_no_critical_zero`).

**What survives.**  Nothing already in `ZetaSectorBank` is wrong: the partition, the involution,
the finite characterisation `imbalance_eq_zero_iff` and the term norms are all correct and are
untouched.  What fails is the *limit* law built on top of them, and the reason is elementary
geometry — a `π/3` arc cannot cancel against its own antipode.

`Mathlib`-only, `sorry`-free, `axiom`-free.
-/

open Complex Finset Filter
open scoped BigOperators

namespace ZetaSectorBank

/-! ### The sector's midpoint direction -/

/-- The midpoint of the *phasor* arc of sector `j`.  Sector `j` collects those `n` with
`t·log n/2π ≡ u (mod 1)`, `u ∈ [j/6,(j+1)/6)`; the phasor carries angle `−t·log n`, so its angle
lies in an arc of width `π/3` centred at `−π(2j+1)/6`. -/
noncomputable def mid (j : Fin 6) : ℝ := -(Real.pi * (2 * (j : ℕ) + 1) / 6)

/-- Rotating by `−mid j` turns a sector-`j` phasor into one with real part at least
`cos(π/6) = √3/2` times its modulus. -/
theorem re_rotate_ge {t : ℝ} {n : ℕ} {j : Fin 6} (hj : sectorOf t n = j) :
    Real.sqrt 3 / 2 * ‖zetaTerm t n‖
      ≤ (Complex.exp (((-(mid j) : ℝ)) * Complex.I) * zetaTerm t n).re := by
  classical
  set L : ℝ := Real.log n with hL
  set u : ℝ := Int.fract (t * L / (2 * Real.pi)) with hu
  -- the floor datum carried by the sector
  have hfl : ⌊(6 : ℝ) * u⌋₊ = (j : ℕ) := by
    have h := congrArg Fin.val hj
    simpa [sectorOf, angleFrac, hu, hL] using h
  have hu0 : (0 : ℝ) ≤ u := Int.fract_nonneg _
  have hnn : (0 : ℝ) ≤ 6 * u := by linarith
  have hlow : ((j : ℕ) : ℝ) ≤ 6 * u := by
    have := Nat.floor_le hnn; rwa [hfl] at this
  have hhigh : 6 * u < ((j : ℕ) : ℝ) + 1 := by
    have := Nat.lt_floor_add_one ((6 : ℝ) * u); rwa [hfl] at this
  -- `t·L = 2π u + 2π k`
  obtain ⟨k, hk⟩ : ∃ k : ℤ, t * L = 2 * Real.pi * u + 2 * Real.pi * k := by
    refine ⟨⌊t * L / (2 * Real.pi)⌋, ?_⟩
    have hpi : (2 : ℝ) * Real.pi ≠ 0 := by positivity
    have hfr : u = t * L / (2 * Real.pi) - ⌊t * L / (2 * Real.pi)⌋ := by
      rw [hu, Int.fract]
    rw [hfr]; field_simp; ring
  -- the rotated phasor's real part is `w · cos(θ)` for the displayed angle
  have hw : (0 : ℝ) ≤ ArithmeticFunction.vonMangoldt n / Real.sqrt n :=
    div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg _)
  have hre : (Complex.exp (((-(mid j) : ℝ)) * Complex.I) * zetaTerm t n).re
      = (ArithmeticFunction.vonMangoldt n / Real.sqrt n) * Real.cos (-(mid j) + -(t * L)) := by
    unfold zetaTerm
    rw [show Complex.exp (((-(mid j) : ℝ)) * Complex.I)
          * (((ArithmeticFunction.vonMangoldt n / Real.sqrt n : ℝ) : ℂ)
              * Complex.exp (((-(t * L) : ℝ) : ℂ) * Complex.I))
        = ((ArithmeticFunction.vonMangoldt n / Real.sqrt n : ℝ) : ℂ)
              * (Complex.exp (((-(mid j) : ℝ)) * Complex.I)
                  * Complex.exp (((-(t * L) : ℝ) : ℂ) * Complex.I)) by ring, ← Complex.exp_add]
    rw [show ((-(mid j) : ℝ) : ℂ) * Complex.I + ((-(t * L) : ℝ) : ℂ) * Complex.I
        = (((-(mid j) + -(t * L) : ℝ)) : ℂ) * Complex.I by push_cast; ring]
    rw [Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re]
  rw [hre, norm_zetaTerm]
  have hcos : Real.sqrt 3 / 2 ≤ Real.cos (-(mid j) + -(t * L)) := by
    -- reduce the angle modulo 2π and apply the cosine bound
    have hang : -(mid j) + -(t * L)
        = (Real.pi * (2 * (j : ℕ) + 1) / 6 - 2 * Real.pi * u)
            + (((-k : ℤ) : ℝ)) * (2 * Real.pi) := by
      rw [mid, hk]; push_cast; ring
    rw [hang, Real.cos_add_int_mul_two_pi]
    set θ : ℝ := Real.pi * (2 * (j : ℕ) + 1) / 6 - 2 * Real.pi * u with hθ
    have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
    have habs : |θ| ≤ Real.pi / 6 := by
      rw [abs_le, hθ]
      constructor <;> nlinarith [hlow, hhigh, hpi]
    have h1 : Real.cos (Real.pi / 6) ≤ Real.cos |θ| :=
      Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg θ) (by linarith) habs
    rwa [Real.cos_abs, Real.cos_pi_div_six] at h1
  calc Real.sqrt 3 / 2 * (ArithmeticFunction.vonMangoldt n / Real.sqrt n)
      = (ArithmeticFunction.vonMangoldt n / Real.sqrt n) * (Real.sqrt 3 / 2) := by ring
    _ ≤ (ArithmeticFunction.vonMangoldt n / Real.sqrt n)
          * Real.cos (-(mid j) + -(t * L)) := mul_le_mul_of_nonneg_left hcos hw

/-- The antipodal sector's phasors point the other way along the same direction. -/
theorem re_rotate_le {t : ℝ} {n : ℕ} {j : Fin 6} (hj2 : (j : ℕ) ≤ 2)
    (hj : sectorOf t n = j + 3) :
    (Complex.exp (((-(mid j) : ℝ)) * Complex.I) * zetaTerm t n).re
      ≤ -(Real.sqrt 3 / 2) * ‖zetaTerm t n‖ := by
  have hval : ((j + 3 : Fin 6) : ℕ) = (j : ℕ) + 3 := by
    have : (j : ℕ) + 3 < 6 := by omega
    simp [Fin.add_def, Nat.mod_eq_of_lt this]
  have hmid : mid (j + 3) = mid j - Real.pi := by
    rw [mid, mid, hval]; push_cast; ring
  have hrot : Complex.exp (((-(mid j) : ℝ)) * Complex.I)
      = -Complex.exp (((-(mid (j + 3)) : ℝ)) * Complex.I) := by
    rw [hmid]
    rw [show ((-(mid j - Real.pi) : ℝ) : ℂ) * Complex.I
        = ((-(mid j) : ℝ) : ℂ) * Complex.I + (Real.pi : ℂ) * Complex.I by push_cast; ring,
      Complex.exp_add, Complex.exp_pi_mul_I]
    ring
  have h := re_rotate_ge (t := t) (n := n) (j := j + 3) hj
  rw [hrot]
  simp only [neg_mul, Complex.neg_re]
  linarith [h]

/-! ### The divergence bound -/

/-- **The arc obstruction.**  Antipodal subtraction adds the masses; it cannot cancel them. -/
theorem norm_sub_ge {t : ℝ} {N : ℕ} {j : Fin 6} (hj2 : (j : ℕ) ≤ 2) :
    Real.sqrt 3 / 2
        * (∑ n ∈ (Icc 1 N).filter (fun n => sectorOf t n = j), ‖zetaTerm t n‖
            + ∑ n ∈ (Icc 1 N).filter (fun n => sectorOf t n = j + 3), ‖zetaTerm t n‖)
      ≤ ‖sectorChan j N t - sectorChan (j + 3) N t‖ := by
  classical
  set c : ℂ := Complex.exp (((-(mid j) : ℝ)) * Complex.I) with hc
  have hcn : ‖c‖ = 1 := by
    rw [hc]; exact Complex.norm_exp_ofReal_mul_I _
  have hbound : (c * (sectorChan j N t - sectorChan (j + 3) N t)).re
      ≤ ‖c * (sectorChan j N t - sectorChan (j + 3) N t)‖ :=
    Complex.re_le_norm _
  have hnorm : ‖c * (sectorChan j N t - sectorChan (j + 3) N t)‖
      = ‖sectorChan j N t - sectorChan (j + 3) N t‖ := by
    rw [norm_mul, hcn, one_mul]
  refine le_trans ?_ (hbound.trans_eq hnorm)
  -- expand the real part termwise
  rw [sectorChan, sectorChan, mul_sub, Complex.sub_re, Finset.mul_sum, Finset.mul_sum,
    Complex.re_sum, Complex.re_sum, mul_add, ← sub_neg_eq_add]
  have hA : Real.sqrt 3 / 2
      * ∑ n ∈ (Icc 1 N).filter (fun n => sectorOf t n = j), ‖zetaTerm t n‖
      ≤ ∑ n ∈ (Icc 1 N).filter (fun n => sectorOf t n = j), (c * zetaTerm t n).re := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun n hn => ?_
    exact re_rotate_ge (Finset.mem_filter.mp hn).2
  have hB : ∑ n ∈ (Icc 1 N).filter (fun n => sectorOf t n = j + 3), (c * zetaTerm t n).re
      ≤ -(Real.sqrt 3 / 2
          * ∑ n ∈ (Icc 1 N).filter (fun n => sectorOf t n = j + 3), ‖zetaTerm t n‖) := by
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_le_sum fun n hn => ?_
    have := re_rotate_le hj2 (Finset.mem_filter.mp hn).2
    linarith
  linarith

/-- The mass carried by one sector. -/
noncomputable def sectorMass (j : Fin 6) (N : ℕ) (t : ℝ) : ℝ :=
  ∑ n ∈ (Icc 1 N).filter (fun n => sectorOf t n = j), ‖zetaTerm t n‖

/-- The six sector masses partition the bank's total mass. -/
theorem mass_partition (N : ℕ) (t : ℝ) :
    ∑ j : Fin 6, sectorMass j N t = ∑ n ∈ Icc 1 N, ‖zetaTerm t n‖ := by
  classical
  unfold sectorMass
  exact Finset.sum_fiberwise (Icc 1 N) (fun n => sectorOf t n) (fun n => ‖zetaTerm t n‖)

/-- **Every term of the bank is swept exactly once** by the three antipodal pairs. -/
theorem mass_pair_decomposition (N : ℕ) (t : ℝ) :
    ∑ n ∈ Icc 1 N, ‖zetaTerm t n‖
      = (sectorMass 0 N t + sectorMass 3 N t)
        + (sectorMass 1 N t + sectorMass 4 N t)
        + (sectorMass 2 N t + sectorMass 5 N t) := by
  rw [← mass_partition, Fin.sum_univ_six]
  ring

/-- **THE BOUND.**  `imbalance N t ≥ (√3/2)·(total mass of the bank)`, for every `t` and `N`. -/
theorem imbalance_ge_half_mass (t : ℝ) (N : ℕ) :
    Real.sqrt 3 / 2 * (∑ n ∈ Icc 1 N, ‖zetaTerm t n‖) ≤ imbalance N t := by
  classical
  have h0 := norm_sub_ge (t := t) (N := N) (j := (0 : Fin 6)) (by norm_num)
  have h1 := norm_sub_ge (t := t) (N := N) (j := (1 : Fin 6)) (by norm_num)
  have h2 := norm_sub_ge (t := t) (N := N) (j := (2 : Fin 6)) (by norm_num)
  have e0 : (0 + 3 : Fin 6) = 3 := rfl
  have e1 : (1 + 3 : Fin 6) = 4 := rfl
  have e2 : (2 + 3 : Fin 6) = 5 := rfl
  rw [e0] at h0; rw [e1] at h1; rw [e2] at h2
  rw [mass_pair_decomposition, imbalance]
  unfold sectorMass at *
  linarith

/-! ### The refutation

No prime number theorem is needed.  A single term of the bank already bounds the imbalance away
from zero, and a sequence bounded below by a positive constant cannot converge to `0`. -/

/-- The bank's mass is at least its `n = 2` term. -/
theorem mass_ge_two_term (t : ℝ) {N : ℕ} (hN : 2 ≤ N) :
    Real.log 2 / Real.sqrt 2 ≤ ∑ n ∈ Icc 1 N, ‖zetaTerm t n‖ := by
  classical
  have hmem : (2 : ℕ) ∈ Icc 1 N := Finset.mem_Icc.mpr ⟨by norm_num, hN⟩
  have hterm : ‖zetaTerm t 2‖ = Real.log 2 / Real.sqrt 2 := by
    rw [norm_zetaTerm, ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two]
    norm_num
  calc Real.log 2 / Real.sqrt 2 = ‖zetaTerm t 2‖ := hterm.symm
    _ ≤ ∑ n ∈ Icc 1 N, ‖zetaTerm t n‖ :=
        Finset.single_le_sum (fun n _ => norm_nonneg (zetaTerm t n)) hmem

/-- The positive constant the imbalance can never go below. -/
noncomputable def floorConst : ℝ := Real.sqrt 3 / 2 * (Real.log 2 / Real.sqrt 2)

theorem floorConst_pos : 0 < floorConst := by
  unfold floorConst
  have h2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have h3 : (0 : ℝ) < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  have hs : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  positivity

/-- **The imbalance is bounded below by a positive constant, at every ordinate.** -/
theorem floorConst_le_imbalance (t : ℝ) {N : ℕ} (hN : 2 ≤ N) :
    floorConst ≤ imbalance N t := by
  refine le_trans ?_ (imbalance_ge_half_mass t N)
  unfold floorConst
  have h3 : (0 : ℝ) ≤ Real.sqrt 3 / 2 := by positivity
  exact mul_le_mul_of_nonneg_left (mass_ge_two_term t hN) h3

/-- **THE REFUTATION.**  `SectorBalanceAt t` is false for every real `t` — not merely unproved,
but false, and with no hypothesis on `t` whatsoever. -/
theorem not_sectorBalanceAt (t : ℝ) : ¬ SectorBalanceAt t := by
  intro h
  have hpos := floorConst_pos
  have hev : ∀ᶠ N in atTop, imbalance N t < floorConst := by
    have : ∀ᶠ y in nhds (0 : ℝ), y < floorConst := by
      filter_upwards [Iio_mem_nhds hpos] with y hy using hy
    exact h.eventually this
  obtain ⟨N, hN1, hN2⟩ := (hev.and (eventually_ge_atTop 2)).exists
  exact absurd hN1 (not_lt.mpr (floorConst_le_imbalance t hN2))

/-- **Consequently the law holds only if `ζ` has no zero on the critical line.**  Since `ζ` does
have such zeros, `AngleSectorBalanceLaw` is false. -/
theorem angleSectorBalanceLaw_iff_no_critical_zero :
    AngleSectorBalanceLaw ↔ ∀ t : ℝ, riemannZeta (1 / 2 + (t : ℂ) * Complex.I) ≠ 0 := by
  constructor
  · intro hlaw t hz
    exact not_sectorBalanceAt t (hlaw t hz)
  · intro hno t hz
    exact absurd hz (hno t)

end ZetaSectorBank
