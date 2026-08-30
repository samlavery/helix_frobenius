import c3b7_B2

/-!
# C3 batch 7, block B3 — the head lower bound, the corrected aggregate domination, and the
`UTail` integrability correction (attack families 5, 6)

Three things.

**1.  The head, bounded below by a provable quantity.**  `modeTerm x u (0,0)` is exactly
`π²e^{5u}·radial(A₁)`; `C3B5.A2.radial_ge` (with `ρ ≤ 1` supplied by
`C3B6.Bessel.logDeriv_kix_le_one`) and `C3B6.Theta.kix_zero_lower` give

  `radial(A₁) ≥ (A₁²−6A₁+6)·e^{−A₁ cosh h}·h/4`,   `h = 1/(|x|+1)`.

**2.  The corrected aggregate domination.**  The batch-6 candidate
`C3B6.Theta.modeBound`-based `modeBound_tail_lt_head` is **FALSE** — six counterexamples,
worst `x = 0`, `A₁ = 8`, `tail/head = 1.2265` (`tmp/c3b7_falsify_out.txt`).  Its replacement
uses the sharp majorant of B1–B2 and the raised threshold `A₁ ≥ 20(|x|+1)²`:

  `Σ_{z≠(0,0)} modeBndS x u z < modeTerm x u (0,0)`   (`modeBndS_tail_lt_head`)

whence `0 < cellDensity x u` unconditionally on that range (`cellDensity_pos_uncond`).
The scalar comparison is
`128(A+3)²e^{−2A} < (A²−6A+6)·e^{−A cosh h}·h/4`, proved from `cosh h ≤ cosh 1 ≤ 1.55`,
`h ≥ 20/A`, `e^{9} ≥ 13³ = 2197` and one cubic with all-positive coefficients in `A = 20+t`.

**3.  The `UTail` correction.**  `C3B6.Theta.UTail` is a raw Bochner integral, so
`UTail_nonneg_of_cellDensity_nonneg` is *vacuously* available when the integrand is not
integrable.  `UTail_eq_zero_of_not_integrable` records that defect as a theorem, and
`cellDensity_abs_le` supplies the super-exponential decay bound that a genuine integrability
proof needs.

SCOPE: nothing here mentions `Ξ`, zeros, or RH.
-/

open MeasureTheory Set Filter Topology

noncomputable section

namespace C3B7

open C3B6.Bessel
open C3B6.Theta

/-! ### 1. Numeric constants, all from `1+y ≤ e^y` and the two `exp 1` decimals -/

theorem exp_neg_one_lt : Real.exp (-1 : ℝ) < 0.37 := by
  have he : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
  have hmul : Real.exp (-1 : ℝ) * Real.exp 1 = 1 := by
    rw [← Real.exp_add]
    norm_num
  nlinarith [hmul, he, Real.exp_pos (-1 : ℝ), Real.exp_pos (1 : ℝ)]

theorem cosh_one_le : Real.cosh 1 ≤ 1.55 := by
  rw [Real.cosh_eq]
  have h1 : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
  have h2 : Real.exp (-1 : ℝ) < 0.37 := exp_neg_one_lt
  linarith

theorem cosh_le_of_le_one {h : ℝ} (h0 : 0 ≤ h) (h1 : h ≤ 1) : Real.cosh h ≤ 1.55 :=
  le_trans (cosh_le_cosh_of_le h0 h1) cosh_one_le

theorem exp_three_ge : (13 : ℝ) ≤ Real.exp 3 := by
  have h := Real.sum_le_exp_of_nonneg (x := (3 : ℝ)) (by norm_num) 4
  norm_num [Finset.sum_range_succ, Nat.factorial] at h
  linarith

theorem exp_nine_ge : (2197 : ℝ) ≤ Real.exp 9 := by
  have h3 : (13 : ℝ) ≤ Real.exp 3 := exp_three_ge
  have h9 : Real.exp 3 ^ 3 = Real.exp 9 := by
    rw [← Real.exp_nat_mul]
    norm_num
  have hp : (13 : ℝ) ^ 3 ≤ Real.exp 3 ^ 3 :=
    pow_le_pow_left₀ (by norm_num) h3 3
  rw [← h9]
  norm_num at hp ⊢
  exact hp

theorem exp_lower_ge {A : ℝ} (hA : 20 ≤ A) :
    2197 * (9 / 20 * A - 8) ≤ Real.exp (9 / 20 * A) := by
  have h9 : (2197 : ℝ) ≤ Real.exp 9 := exp_nine_ge
  have hexp : (9 / 20 * A - 9) + 1 ≤ Real.exp (9 / 20 * A - 9) :=
    Real.add_one_le_exp _
  have ht : (1 : ℝ) ≤ 9 / 20 * A - 8 := by linarith
  have hsplit : Real.exp (9 / 20 * A) = Real.exp 9 * Real.exp (9 / 20 * A - 9) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hsplit]
  nlinarith [h9, hexp, ht, Real.exp_pos (9 / 20 * A - 9)]

/-! ### 2. The head, bounded below -/

theorem radial_ge_kix (x : ℝ) {A : ℝ} (h8 : 8 ≤ A) (hx : 4 * (|x| + 1) ^ 2 < A) :
    (A ^ 2 - 6 * A + 6) * kix 0 x A
      ≤ C3B5.A2.radial A (kix 0 x A) (kix 1 x A) := by
  have hA0 : (0 : ℝ) < A := by linarith
  have hKpos : ∀ B ∈ Set.Ici A, 0 < kix 0 x B := fun B hB =>
    kix_zero_pos (lt_of_lt_of_le hx hB)
  have hceil := logDeriv_kix_le_one (a := A) (x := x) hA0 hKpos
  have hρ : -zDer x A / zFun x A ≤ 1 := hceil A (Set.mem_Ici.mpr le_rfl)
  have hK : 0 < kix 0 x A := kix_zero_pos hx
  have hlog := kix_logDeriv_transfer hA0 hK.ne'
  exact C3B5.A2.radial_ge hA0 hK hρ hlog

theorem head_radial_lower (x : ℝ) {A : ℝ} (h8 : 8 ≤ A) (hx : 8 * (|x| + 1) ^ 2 ≤ A) :
    (A ^ 2 - 6 * A + 6)
        * (Real.exp (-(A * Real.cosh (1 / (|x| + 1)))) * (1 / (|x| + 1)) / 4)
      ≤ C3B5.A2.radial A (kix 0 x A) (kix 1 x A) := by
  have habs : (1 : ℝ) ≤ |x| + 1 := by have := abs_nonneg x; linarith
  have hquad : (0 : ℝ) ≤ A ^ 2 - 6 * A + 6 := by nlinarith [h8]
  have hx4 : 4 * (|x| + 1) ^ 2 < A := by nlinarith [hx, habs]
  have hlow := kix_zero_lower (x := x) (A := A) hx
  have hrad := radial_ge_kix x h8 hx4
  have hmul := mul_le_mul_of_nonneg_left hlow hquad
  linarith [hmul, hrad]

/-! ### 3. The scalar comparison -/

theorem tail_lt_head_scalar {A h : ℝ} (hA : 20 ≤ A) (hhpos : 0 < h) (hh1 : h ≤ 1)
    (hhlow : 20 / A ≤ h) :
    128 * (A + 3) ^ 2 * Real.exp (-(2 * A))
      < (A ^ 2 - 6 * A + 6) * (Real.exp (-(A * Real.cosh h)) * h / 4) := by
  have hA0 : (0 : ℝ) < A := by linarith
  have hquad : (0 : ℝ) < A ^ 2 - 6 * A + 6 := by nlinarith [hA]
  have hch : Real.cosh h ≤ 1.55 := cosh_le_of_le_one hhpos.le hh1
  have hexp1 : Real.exp (-(1.55 * A)) ≤ Real.exp (-(A * Real.cosh h)) := by
    refine Real.exp_le_exp.mpr ?_
    nlinarith [hch, hA0]
  have h20 : (0 : ℝ) < 20 / A := by positivity
  have hprod : Real.exp (-(1.55 * A)) * (20 / A)
      ≤ Real.exp (-(A * Real.cosh h)) * h :=
    mul_le_mul hexp1 hhlow h20.le (Real.exp_pos _).le
  have hstep : (A ^ 2 - 6 * A + 6) * (Real.exp (-(1.55 * A)) * (20 / A) / 4)
      ≤ (A ^ 2 - 6 * A + 6) * (Real.exp (-(A * Real.cosh h)) * h / 4) := by
    refine mul_le_mul_of_nonneg_left ?_ hquad.le
    linarith [hprod]
  refine lt_of_lt_of_le ?_ hstep
  -- the cubic
  have hmain : 128 * A * (A + 3) ^ 2 < 5 * (A ^ 2 - 6 * A + 6) * Real.exp (9 / 20 * A) := by
    have h1 : 2197 * (9 / 20 * A - 8) ≤ Real.exp (9 / 20 * A) := exp_lower_ge hA
    have hcoef : (0 : ℝ) ≤ 5 * (A ^ 2 - 6 * A + 6) := by linarith
    have hstep2 : 5 * (A ^ 2 - 6 * A + 6) * (2197 * (9 / 20 * A - 8))
        ≤ 5 * (A ^ 2 - 6 * A + 6) * Real.exp (9 / 20 * A) :=
      mul_le_mul_of_nonneg_left h1 hcoef
    refine lt_of_lt_of_le ?_ hstep2
    obtain ⟨t, ht, rfl⟩ : ∃ t, 0 ≤ t ∧ A = 20 + t := ⟨A - 20, by linarith, by ring⟩
    nlinarith [ht, mul_nonneg ht ht, mul_nonneg (mul_nonneg ht ht) ht]
  have hE : (0 : ℝ) < Real.exp (-(2 * A)) := Real.exp_pos _
  have hratio : Real.exp (-(1.55 * A)) = Real.exp (-(2 * A)) * Real.exp (9 / 20 * A) := by
    rw [← Real.exp_add]
    congr 1
    norm_num
    ring
  rw [hratio]
  have hrewrite : (A ^ 2 - 6 * A + 6)
        * (Real.exp (-(2 * A)) * Real.exp (9 / 20 * A) * (20 / A) / 4)
      = Real.exp (-(2 * A)) * (5 * (A ^ 2 - 6 * A + 6) * Real.exp (9 / 20 * A) / A) := by
    field_simp
    ring
  rw [hrewrite]
  have hlhs : 128 * (A + 3) ^ 2 * Real.exp (-(2 * A))
      = Real.exp (-(2 * A)) * (128 * (A + 3) ^ 2) := by ring
  rw [hlhs]
  refine mul_lt_mul_of_pos_left ?_ hE
  rw [lt_div_iff₀ hA0]
  nlinarith [hmain]

/-! ### 4. Summability of the sharp majorant (head included) -/

theorem exp_two_le_sixteen : Real.exp 2 ≤ 16 := by
  have h1 : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
  have h2 : Real.exp 1 ^ 2 = Real.exp 2 := by
    rw [← Real.exp_nat_mul]
    norm_num
  rw [← h2]
  nlinarith [h1, Real.exp_pos (1 : ℝ)]

/-- The factorised bound, extended to the head index — needed only for summability. -/
theorem modeBndS_le_prod_all (x : ℝ) {u : ℝ} (hA : 20 ≤ modeA 0 0 u) (z : ℕ × ℕ) :
    modeBndS x u z
      ≤ tailConst u (modeA 0 0 u) * (gq (modeA 0 0 u) z.1 * gq (modeA 0 0 u) z.2) := by
  obtain ⟨n, m⟩ := z
  by_cases hz : n = 0 ∧ m = 0
  · obtain ⟨hn, hm⟩ := hz
    subst hn; subst hm
    set A₁ : ℝ := modeA 0 0 u with hA1
    have hpi := Real.pi_pos
    have hA0 : (0 : ℝ) < A₁ := by linarith
    have hL : modeBndS x u ((0 : ℕ), (0 : ℕ))
        = Real.pi ^ 2 * Real.exp (5 * u) * (2 * (A₁ + 3) ^ 2 * Real.exp (-A₁)) := by
      unfold modeBndS
      simp only [Nat.cast_zero, zero_add, one_mul, one_pow]
      rw [hA1]
      ring
    have hq : gq A₁ 0 * gq A₁ 0 = Real.exp (-(2 * (A₁ - 2))) := by
      unfold gq qFac
      rw [pow_one, ← Real.exp_add]
      congr 1
      ring
    have hR : tailConst u A₁ * (gq A₁ 0 * gq A₁ 0)
        = Real.pi ^ 2 * Real.exp (5 * u)
          * (32 * (A₁ + 3) ^ 2 * (Real.exp (-A₁) * Real.exp (-2))) := by
      rw [hq]
      unfold tailConst
      rw [show Real.pi ^ 2 * Real.exp (5 * u) * (32 * (A₁ + 3) ^ 2 * Real.exp (-(2 * A₁)))
            * Real.exp (3 * (A₁ - 2)) * Real.exp (-(2 * (A₁ - 2)))
          = Real.pi ^ 2 * Real.exp (5 * u) * (32 * (A₁ + 3) ^ 2
            * (Real.exp (-(2 * A₁)) * Real.exp (3 * (A₁ - 2)) * Real.exp (-(2 * (A₁ - 2)))))
          by ring]
      congr 2
      rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
      congr 1
      ring
    rw [hL, hR]
    have hcoef : (0 : ℝ) ≤ Real.pi ^ 2 * Real.exp (5 * u) := by positivity
    refine mul_le_mul_of_nonneg_left ?_ hcoef
    have he2 : Real.exp 2 ≤ 16 := exp_two_le_sixteen
    have hinv : Real.exp (-2 : ℝ) * Real.exp 2 = 1 := by
      rw [← Real.exp_add]
      norm_num
    have hge : (2 : ℝ) ≤ 32 * Real.exp (-2 : ℝ) := by
      nlinarith [hinv, he2, Real.exp_pos (-2 : ℝ), Real.exp_pos (2 : ℝ)]
    have hAe : (0 : ℝ) < (A₁ + 3) ^ 2 * Real.exp (-A₁) := by positivity
    nlinarith [hge, hAe]
  · exact modeBndS_le_prod x hA hz

theorem summable_modeBndS (x : ℝ) {u : ℝ} (hA : 20 ≤ modeA 0 0 u) :
    Summable (modeBndS x u) :=
  ((summable_prod_gq hA).mul_left _).of_nonneg_of_le
    (modeBndS_nonneg x u) (modeBndS_le_prod_all x hA)

/-! ### 5. THE CORRECTED AGGREGATE DOMINATION -/

/-- **The batch-7 replacement for the refuted `modeBound_tail_lt_head`.**
Threshold raised from `max(modeThreshold x, 8(|x|+1)²)` to `20(|x|+1)²`, majorant replaced
by the mode-specific `modeBndS`. -/
theorem modeBndS_tail_lt_head (x : ℝ) {u : ℝ}
    (hx : 20 * (|x| + 1) ^ 2 ≤ modeA 0 0 u) :
    (∑' z : ℕ × ℕ, if z = (0, 0) then (0 : ℝ) else modeBndS x u z)
      < modeTerm x u (0, 0) := by
  have habs : (1 : ℝ) ≤ |x| + 1 := by have := abs_nonneg x; linarith
  set A : ℝ := modeA 0 0 u with hAdef
  have hsq1 : (1 : ℝ) ≤ (|x| + 1) ^ 2 := by nlinarith [habs]
  have hA20 : (20 : ℝ) ≤ A := by nlinarith [hx, hsq1]
  have hA8 : (8 : ℝ) ≤ A := by linarith
  have hlin : 20 * (|x| + 1) ≤ A := by nlinarith [hx, habs]
  have hx8 : 8 * (|x| + 1) ^ 2 ≤ A := by nlinarith [hx, hsq1]
  set h : ℝ := 1 / (|x| + 1) with hhdef
  have hhpos : 0 < h := by rw [hhdef]; positivity
  have hh1 : h ≤ 1 := by
    rw [hhdef, div_le_one (by linarith)]
    linarith
  have hA0 : (0 : ℝ) < A := by linarith
  have hhlow : 20 / A ≤ h := by
    rw [hhdef, div_le_div_iff₀ hA0 (by linarith : (0:ℝ) < |x| + 1)]
    nlinarith [hlin]
  have htail := modeBndS_tail_le x hA20
  have hhead := head_radial_lower x hA8 hx8
  have hscalar := tail_lt_head_scalar hA20 hhpos hh1 hhlow
  have hpi : (0 : ℝ) < Real.pi ^ 2 * Real.exp (5 * u) := by
    have := Real.pi_pos
    positivity
  rw [modeTerm_head]
  refine lt_of_le_of_lt htail ?_
  refine lt_of_lt_of_le (mul_lt_mul_of_pos_left hscalar hpi) ?_
  exact mul_le_mul_of_nonneg_left hhead hpi.le

/-- **`C(u,x) > 0`, unconditionally, above the explicit height `20(|x|+1)²`.** -/
theorem cellDensity_pos_uncond (x : ℝ) {u : ℝ}
    (hx : 20 * (|x| + 1) ^ 2 ≤ modeA 0 0 u) : 0 < cellDensity x u := by
  have habs : (1 : ℝ) ≤ |x| + 1 := by have := abs_nonneg x; linarith
  have hsq1 : (1 : ℝ) ≤ (|x| + 1) ^ 2 := by nlinarith [habs]
  have hA20 : (20 : ℝ) ≤ modeA 0 0 u := by nlinarith [hx, hsq1]
  have hA8 : (8 : ℝ) ≤ modeA 0 0 u := by linarith
  have hpos : 0 < ∑' z : ℕ × ℕ, modeTerm x u z :=
    tsum_pos_of_head_dominant' (0, 0) (summable_modeTerm x u) (summable_modeBndS x hA20)
      (fun z => modeTerm_abs_le_sharp x hA8 z) (modeBndS_tail_lt_head x hx)
  rw [cellDensity_eq_tsum]
  linarith

/-! ### 6. The `UTail` correction (ledger §0.3) -/

/-- **The defect, stated as a theorem.**  `C3B6.Theta.UTail` is a raw Bochner integral, so it
is `0` whenever the integrand fails to be integrable.  Consequently
`C3B6.Theta.UTail_nonneg_of_cellDensity_nonneg` is *vacuously* available in that case and
does **not** by itself establish the analytic `U_x(s)`.  Any consumer must supply
integrability. -/
theorem UTail_eq_zero_of_not_integrable {x s : ℝ}
    (hint : ¬ IntegrableOn (fun u => (u - s) ^ 2 / 2 * cellDensity x u) (Ioi s)) :
    UTail x s = 0 := by
  unfold UTail
  exact integral_undef hint

/-- The super-exponential decay bound a genuine integrability proof consumes:
`|C(u,x)| ≤ 16·(head majorant + tail majorant)`, both carrying `e^{−A₁(u)} = e^{−2πe^{2u}}`. -/
theorem cellDensity_abs_le (x : ℝ) {u : ℝ} (hA : 20 ≤ modeA 0 0 u) :
    |cellDensity x u|
      ≤ 16 * (modeBndS x u (0, 0)
        + Real.pi ^ 2 * Real.exp (5 * u)
          * (128 * (modeA 0 0 u + 3) ^ 2 * Real.exp (-(2 * modeA 0 0 u)))) := by
  have hA8 : (8 : ℝ) ≤ modeA 0 0 u := by linarith
  have hsum := summable_modeTerm x u
  have hsplit : ∑' z : ℕ × ℕ, modeTerm x u z
      = modeTerm x u (0, 0)
        + ∑' z : ℕ × ℕ, if z = (0, 0) then (0 : ℝ) else modeTerm x u z :=
    hsum.tsum_eq_add_tsum_ite (0, 0)
  have hbndS := summable_modeBndS x hA
  have hFabs : ∀ z : ℕ × ℕ,
      ‖(if z = (0, 0) then (0 : ℝ) else modeTerm x u z)‖
        ≤ (if z = (0, 0) then (0 : ℝ) else modeBndS x u z) := by
    intro z
    by_cases hz : z = (0, 0)
    · simp only [if_pos hz, norm_zero, le_refl]
    · simp only [if_neg hz, Real.norm_eq_abs]
      exact modeTerm_abs_le_sharp x hA8 z
  have hitebS : Summable (fun z : ℕ × ℕ => if z = (0, 0) then (0 : ℝ) else modeBndS x u z) := by
    refine hbndS.of_nonneg_of_le (fun z => ?_) (fun z => ?_)
    · by_cases hz : z = (0, 0)
      · simp only [if_pos hz, le_refl]
      · simp only [if_neg hz]
        exact modeBndS_nonneg x u z
    · by_cases hz : z = (0, 0)
      · simp only [if_pos hz]
        exact modeBndS_nonneg x u z
      · simp only [if_neg hz]
        exact le_rfl
  have hitef : Summable (fun z : ℕ × ℕ => if z = (0, 0) then (0 : ℝ) else modeTerm x u z) :=
    Summable.of_norm_bounded hitebS hFabs
  have hnorm : ‖∑' z : ℕ × ℕ, if z = (0, 0) then (0 : ℝ) else modeTerm x u z‖
      ≤ ∑' z : ℕ × ℕ, if z = (0, 0) then (0 : ℝ) else modeBndS x u z := by
    refine le_trans (norm_tsum_le_tsum_norm ?_) ?_
    · exact hitebS.of_nonneg_of_le (fun z => norm_nonneg _) hFabs
    · exact Summable.tsum_le_tsum hFabs
        (hitebS.of_nonneg_of_le (fun z => norm_nonneg _) hFabs) hitebS
  rw [Real.norm_eq_abs] at hnorm
  have htail := modeBndS_tail_le x hA
  have hhead : |modeTerm x u (0, 0)| ≤ modeBndS x u (0, 0) :=
    modeTerm_abs_le_sharp x hA8 (0, 0)
  rw [cellDensity_eq_tsum, abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ (16:ℝ))]
  rw [hsplit]
  refine mul_le_mul_of_nonneg_left ?_ (by norm_num : (0:ℝ) ≤ (16:ℝ))
  refine (abs_add_le _ _).trans ?_
  linarith [hhead, hnorm, htail]

end C3B7

section AxiomAudit
#print axioms C3B7.exp_neg_one_lt
#print axioms C3B7.cosh_one_le
#print axioms C3B7.exp_three_ge
#print axioms C3B7.exp_nine_ge
#print axioms C3B7.exp_lower_ge
#print axioms C3B7.radial_ge_kix
#print axioms C3B7.head_radial_lower
#print axioms C3B7.tail_lt_head_scalar
#print axioms C3B7.exp_two_le_sixteen
#print axioms C3B7.modeBndS_le_prod_all
#print axioms C3B7.summable_modeBndS
#print axioms C3B7.modeBndS_tail_lt_head
#print axioms C3B7.cellDensity_pos_uncond
#print axioms C3B7.UTail_eq_zero_of_not_integrable
#print axioms C3B7.cellDensity_abs_le
end AxiomAudit
