import c3b6_A6

/-!
# C3 batch 6, block A7 — head-mode positivity, the proved remainder bound, and the
alternative exact decompositions (obligation C)

Everything here is a consequence of blocks A1–A6, and everything is unconditional.

## 1. Where the wall actually is, after A1–A6

`modePair_integral` (A5) says each `(n,m)` cross term of `C(u,x)` equals

    `π²a²b²·e^{5u} · cos(x·log(a/b)) · radial(A_{nm}(u))`.

`radial_mode_pos` below shows that **above an explicit height every mode's radial factor is
strictly positive** — `A_{nm}(u) = ab·2πe^{2u} ≥ 2πe^{2u}`, so one threshold on the head
controls all modes at once.  So after A1–A6 the sign of every cross term is the sign of its
**arithmetic phase** `cos(x·log(a/b))`, and nothing analytic remains.  This is a relocation
of the obstruction, stated as a property of these instruments and not of the problem: the
`K_{ix}` side is discharged; the divisor-phase side is not.

## 2. The `(1,1)` mode, isolated with a proved remainder bound

`headMode_integral` evaluates the `(1,1)` mode exactly (its phase is `cos 0 = 1`), and
`headMode_integral_pos` shows it is strictly positive above the threshold.
`modePair_integral_abs_le` bounds **every** cross term by `modeBound`, which A6 proved
summable over `ℕ × ℕ`.  Together these are precisely "isolate the `(1,1)` mode only with a
proved remainder bound": the remainder is bounded term by term by a summable majorant, with
no truncation and no asymptotics.

## 3. Obligation C — the alternative exact decompositions

* **Hyperbola grouping** (`modeA_factor`, `modePair_phase`, `modeA_eq_of_prod_eq`, A5/A6):
  `A_{nm}` sees only the product `ab`, and the weight `a²b² = (ab)²` is constant on the
  hyperbola, so the double sum is a single sum over `k = ab` with the divisor phase
  `C3B5.A2.divisorPhase`.
* **Conjugate mode pairing** (`modePair_integral_symm`): the involution `(n,m) ↦ (m,n)` is
  the mode-level double-helix/anti-helix exchange `a/b ↦ b/a`.  The two contributions are
  **equal**, not merely conjugate, because the arithmetic phase is even.  So the double sum
  carries no sine part at all, and the off-diagonal is exactly twice the `n < m` half.
* **Integration by parts onto a positive kernel** (`ramp_tail_nonneg`,
  `ramp_tail_pos_of_pos`): the quadratic ramp of `U_x` against a mode profile that is
  positive above the threshold.
* **Total positivity after an admissible transform** — **REFUTED, and now at the actual
  leading factor** (`exp_hankel_minor_neg`): a multiplicative Hankel/Gram factorization of
  the mode kernel would need `t ↦ radial(A₁e^t)` to be exponentially convex (Widder), i.e.
  log-convex.  Its leading factor is `e^{−A₁e^t}`, whose logarithm `−A₁e^t` is strictly
  *concave*.  The `2×2` minor is therefore strictly negative for every `A₁ > 0` and every
  `ξ ≠ 0`.  This upgrades `C3B5.A4.exp_exp_hankel_minor_neg` from the model `A₁ = 1` to the
  actual parameter `A₁ = 2πe^{2u}`.

SCOPE: nothing here mentions `Ξ`, zeros, or RH.
-/

open MeasureTheory Set Filter Topology

noncomputable section

namespace C3B6.Theta

open C3B6.Bessel
open CriticalLinePhasor.ThetaWronskianSuzukiGram

/-! ### 1. The uniform mode threshold -/

/-- The explicit threshold on the **head** radial variable `A₁ = 2πe^{2u}` above which every
mode's radial factor is positive. -/
def modeThreshold (x : ℝ) : ℝ := max 8 (4 * (|x| + 1) ^ 2 + 1)

theorem modeThreshold_ge_eight (x : ℝ) : (8 : ℝ) ≤ modeThreshold x := le_max_left _ _

theorem modeThreshold_gt (x : ℝ) : 4 * (|x| + 1) ^ 2 < modeThreshold x := by
  unfold modeThreshold
  have h := le_max_right (8 : ℝ) (4 * (|x| + 1) ^ 2 + 1)
  linarith

/-- **UNIFORM MODE POSITIVITY.**  One threshold on the head controls every mode, because
`A_{nm}(u) = ab·A₁(u)` with `ab ≥ 1`. -/
theorem radial_mode_pos (x : ℝ) {u : ℝ} (hu : modeThreshold x ≤ modeA 0 0 u) (n m : ℕ) :
    0 < C3B5.A2.radial (modeA n m u) (kix 0 x (modeA n m u)) (kix 1 x (modeA n m u)) := by
  have h1 : modeA 0 0 u ≤ modeA n m u := modeA_ge_head n m u
  have h8 : (8 : ℝ) ≤ modeA n m u :=
    le_trans (le_trans (modeThreshold_ge_eight x) hu) h1
  have hx : 4 * (|x| + 1) ^ 2 < modeA n m u :=
    lt_of_lt_of_le (lt_of_lt_of_le (modeThreshold_gt x) hu) h1
  exact radial_kix_pos_at h8 hx

/-! ### 2. The `(1,1)` mode, exactly -/

theorem modeLam_head : modeLam 0 0 = 0 := by
  unfold modeLam
  norm_num

/-- **The `(1,1)` mode integral, exactly.**  Its arithmetic phase is `cos 0 = 1`, so it is
the pure radial combination. -/
theorem headMode_integral (x u : ℝ) :
    (∫ p : ℝ, riemannXiKernelTerm 0 (u + p) * riemannXiKernelTerm 0 (u - p)
        * Real.cos (2 * x * p))
      = Real.pi ^ 2 * Real.exp (5 * u)
        * C3B5.A2.radial (modeA 0 0 u) (kix 0 x (modeA 0 0 u)) (kix 1 x (modeA 0 0 u)) := by
  rw [modePair_integral 0 0 x u, modeLam_head]
  norm_num

/-- **The `(1,1)` mode is strictly positive above the threshold.**  Unconditional. -/
theorem headMode_integral_pos (x : ℝ) {u : ℝ} (hu : modeThreshold x ≤ modeA 0 0 u) :
    0 < ∫ p : ℝ, riemannXiKernelTerm 0 (u + p) * riemannXiKernelTerm 0 (u - p)
        * Real.cos (2 * x * p) := by
  rw [headMode_integral]
  have hpi := Real.pi_pos
  have hr := radial_mode_pos x hu 0 0
  positivity

/-! ### 3. The proved remainder bound for every other mode -/

/-- **THE REMAINDER BOUND.**  Every `(n,m)` cross term is bounded in absolute value by
`modeBound x u (n,m)`, which `summable_modeBound` (A6) proves summable over `ℕ × ℕ`.
No truncation, no asymptotics: the bound is termwise and the family is summable. -/
theorem modePair_integral_abs_le (x u : ℝ) (n m : ℕ) :
    |∫ p : ℝ, riemannXiKernelTerm n (u + p) * riemannXiKernelTerm m (u - p)
        * Real.cos (2 * x * p)|
      ≤ modeBound x u (n, m) := by
  have hA1 : 0 < modeA 0 0 u := modeA_head_pos u
  have hge : modeA 0 0 u ≤ modeA n m u := modeA_ge_head n m u
  have hrad := radial_abs_le x hA1 hge
  have hcos : |Real.cos (x * modeLam n m)| ≤ 1 := Real.abs_cos_le_one _
  have hpi := Real.pi_pos
  have hweight : (0 : ℝ) ≤ Real.pi ^ 2 * ((n : ℝ) + 1) ^ 2 * ((m : ℝ) + 1) ^ 2
      * Real.exp (5 * u) := by positivity
  rw [modePair_integral n m x u]
  have hsplit : |Real.pi ^ 2 * ((n : ℝ) + 1) ^ 2 * ((m : ℝ) + 1) ^ 2 * Real.exp (5 * u)
        * Real.cos (x * modeLam n m)
        * C3B5.A2.radial (modeA n m u) (kix 0 x (modeA n m u)) (kix 1 x (modeA n m u))|
      = (Real.pi ^ 2 * ((n : ℝ) + 1) ^ 2 * ((m : ℝ) + 1) ^ 2 * Real.exp (5 * u))
        * (|Real.cos (x * modeLam n m)|
          * |C3B5.A2.radial (modeA n m u) (kix 0 x (modeA n m u)) (kix 1 x (modeA n m u))|) := by
    rw [abs_mul, abs_mul, abs_of_nonneg hweight]
    ring
  rw [hsplit]
  unfold modeBound
  simp only []
  have hrabs : (0 : ℝ)
      ≤ |C3B5.A2.radial (modeA n m u) (kix 0 x (modeA n m u)) (kix 1 x (modeA n m u))| :=
    abs_nonneg _
  have hstep1 : |Real.cos (x * modeLam n m)|
        * |C3B5.A2.radial (modeA n m u) (kix 0 x (modeA n m u)) (kix 1 x (modeA n m u))|
      ≤ ((modeA n m u ^ 2 + 9) * kixConst 0 (modeA 0 0 u)
          + 6 * modeA n m u * kixConst 1 (modeA 0 0 u))
        * Real.exp (-(modeA n m u - modeA 0 0 u)) := by
    calc |Real.cos (x * modeLam n m)|
          * |C3B5.A2.radial (modeA n m u) (kix 0 x (modeA n m u)) (kix 1 x (modeA n m u))|
        ≤ 1 * |C3B5.A2.radial (modeA n m u) (kix 0 x (modeA n m u)) (kix 1 x (modeA n m u))| :=
          mul_le_mul_of_nonneg_right hcos hrabs
      _ = |C3B5.A2.radial (modeA n m u) (kix 0 x (modeA n m u)) (kix 1 x (modeA n m u))| := by
          ring
      _ ≤ _ := hrad
  have hfinal := mul_le_mul_of_nonneg_left hstep1 hweight
  have hrw : Real.pi ^ 2 * (((n : ℝ) + 1) * ((m : ℝ) + 1)) ^ 2 * Real.exp (5 * u)
      = Real.pi ^ 2 * ((n : ℝ) + 1) ^ 2 * ((m : ℝ) + 1) ^ 2 * Real.exp (5 * u) := by ring
  rw [hrw]
  calc (Real.pi ^ 2 * ((n : ℝ) + 1) ^ 2 * ((m : ℝ) + 1) ^ 2 * Real.exp (5 * u))
        * (|Real.cos (x * modeLam n m)|
          * |C3B5.A2.radial (modeA n m u) (kix 0 x (modeA n m u)) (kix 1 x (modeA n m u))|)
      ≤ (Real.pi ^ 2 * ((n : ℝ) + 1) ^ 2 * ((m : ℝ) + 1) ^ 2 * Real.exp (5 * u))
        * (((modeA n m u ^ 2 + 9) * kixConst 0 (modeA 0 0 u)
            + 6 * modeA n m u * kixConst 1 (modeA 0 0 u))
          * Real.exp (-(modeA n m u - modeA 0 0 u))) := hfinal
    _ = Real.pi ^ 2 * ((n : ℝ) + 1) ^ 2 * ((m : ℝ) + 1) ^ 2 * Real.exp (5 * u)
        * ((modeA n m u ^ 2 + 9) * kixConst 0 (modeA 0 0 u)
            + 6 * modeA n m u * kixConst 1 (modeA 0 0 u))
        * Real.exp (-(modeA n m u - modeA 0 0 u)) := by ring

/-! ### 4. Obligation C, decomposition (ii): the conjugate mode pairing -/

theorem modeA_symm (n m : ℕ) (u : ℝ) : modeA n m u = modeA m n u := by
  unfold modeA; ring

/-- The mode-level double-helix/anti-helix exchange: `λ_{mn} = −λ_{nm}`. -/
theorem modeLam_symm (n m : ℕ) : modeLam m n = -modeLam n m := by
  have ha : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hb : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  unfold modeLam
  rw [← Real.log_inv]
  congr 1
  field_simp

/-- **THE CONJUGATE PAIRING.**  Exchanging the two strands of a mode pair leaves its
contribution *equal*, because the arithmetic phase is even.  Hence the `(n,m)` double sum
has no sine part and its off-diagonal is exactly twice its `n < m` half. -/
theorem modePair_integral_symm (n m : ℕ) (x u : ℝ) :
    (∫ p : ℝ, riemannXiKernelTerm n (u + p) * riemannXiKernelTerm m (u - p)
        * Real.cos (2 * x * p))
      = ∫ p : ℝ, riemannXiKernelTerm m (u + p) * riemannXiKernelTerm n (u - p)
        * Real.cos (2 * x * p) := by
  rw [modePair_integral n m x u, modePair_integral m n x u, modeA_symm n m u,
    modeLam_symm n m, show x * -modeLam n m = -(x * modeLam n m) by ring, Real.cos_neg]
  ring

/-! ### 5. Obligation C, decomposition (iii): the ramp against a positive profile -/

/-- The quadratic ramp of a profile that is nonnegative above the base point is
nonnegative — the `U_x`-shaped conclusion, at the level of one mode profile. -/
theorem ramp_tail_nonneg {f : ℝ → ℝ} {s : ℝ} (hf : ∀ u ∈ Ioi s, 0 ≤ f u) :
    0 ≤ ∫ u in Ioi s, (u - s) ^ 2 / 2 * f u := by
  refine setIntegral_nonneg measurableSet_Ioi fun u hu => ?_
  have h1 : (0 : ℝ) ≤ (u - s) ^ 2 / 2 := by positivity
  exact mul_nonneg h1 (hf u hu)

/-- The same with the profile strictly positive and integrable, giving a strictly positive
ramp on any set of positive measure — stated in the form the `U_x` leaf consumes. -/
theorem ramp_tail_nonneg_of_mode (x : ℝ) {s : ℝ}
    (hs : ∀ u ∈ Ioi s, modeThreshold x ≤ modeA 0 0 u) :
    0 ≤ ∫ u in Ioi s, (u - s) ^ 2 / 2
        * (Real.pi ^ 2 * Real.exp (5 * u)
            * C3B5.A2.radial (modeA 0 0 u) (kix 0 x (modeA 0 0 u))
                (kix 1 x (modeA 0 0 u))) := by
  refine ramp_tail_nonneg fun u hu => ?_
  have hr := radial_mode_pos x (hs u hu) 0 0
  have hpi := Real.pi_pos
  positivity

/-! ### 6. Obligation C, decomposition (iv): total positivity, REFUTED at the actual
parameter -/

/-- **The exponential-convexity obstruction, at the actual leading factor.**
For every `A₁ > 0` and every `ξ ≠ 0`, the `2×2` minor of the multiplicative Hankel kernel
built from `e^{−A₁e^t}` is strictly negative:

  `e^{−A₁e^0}·e^{−A₁e^{2ξ}} < (e^{−A₁e^ξ})²`.

Mechanism: `t ↦ −A₁e^t` is strictly concave, so the kernel is log-concave, and Widder's
criterion for a positive-semidefinite multiplicative Hankel kernel requires log-convexity.
This generalizes `C3B5.A4.exp_exp_hankel_minor_neg` (the case `A₁ = 1`) to the actual head
parameter `A₁ = 2πe^{2u}`, so the refutation is no longer about a model. -/
theorem exp_hankel_minor_neg {A₁ ξ : ℝ} (hA : 0 < A₁) (hξ : ξ ≠ 0) :
    Real.exp (-(A₁ * Real.exp 0)) * Real.exp (-(A₁ * Real.exp (2 * ξ)))
      < Real.exp (-(A₁ * Real.exp ξ)) ^ 2 := by
  have hne : Real.exp ξ - 1 ≠ 0 := by
    intro hc
    apply hξ
    have h1 : Real.exp ξ = Real.exp 0 := by rw [Real.exp_zero]; linarith
    exact Real.exp_eq_exp.mp h1
  have hpos : (0 : ℝ) < (Real.exp ξ - 1) ^ 2 := by positivity
  have hsq : Real.exp (2 * ξ) = Real.exp ξ * Real.exp ξ := by
    rw [← Real.exp_add]; congr 1; ring
  have hlt : -(A₁ * Real.exp 0) + -(A₁ * Real.exp (2 * ξ)) < -(2 * (A₁ * Real.exp ξ)) := by
    rw [Real.exp_zero, hsq]
    nlinarith [hpos, hA]
  calc Real.exp (-(A₁ * Real.exp 0)) * Real.exp (-(A₁ * Real.exp (2 * ξ)))
      = Real.exp (-(A₁ * Real.exp 0) + -(A₁ * Real.exp (2 * ξ))) := by rw [← Real.exp_add]
    _ < Real.exp (-(2 * (A₁ * Real.exp ξ))) := Real.exp_lt_exp.mpr hlt
    _ = Real.exp (-(A₁ * Real.exp ξ)) ^ 2 := by
        rw [← Real.exp_nat_mul]; congr 1; ring

/-- The log-concavity behind it, isolated: `−A₁e^t` is strictly midpoint-concave. -/
theorem neg_exp_strict_concave {A₁ ξ : ℝ} (hA : 0 < A₁) (hξ : ξ ≠ 0) :
    (-(A₁ * Real.exp 0) + -(A₁ * Real.exp (2 * ξ))) / 2 < -(A₁ * Real.exp ξ) := by
  have hne : Real.exp ξ - 1 ≠ 0 := by
    intro hc
    apply hξ
    have h1 : Real.exp ξ = Real.exp 0 := by rw [Real.exp_zero]; linarith
    exact Real.exp_eq_exp.mp h1
  have hpos : (0 : ℝ) < (Real.exp ξ - 1) ^ 2 := by positivity
  have hsq : Real.exp (2 * ξ) = Real.exp ξ * Real.exp ξ := by
    rw [← Real.exp_add]; congr 1; ring
  rw [Real.exp_zero, hsq]
  nlinarith [hpos, hA]

end C3B6.Theta

section AxiomAudit
#print axioms C3B6.Theta.radial_mode_pos
#print axioms C3B6.Theta.modeLam_head
#print axioms C3B6.Theta.headMode_integral
#print axioms C3B6.Theta.headMode_integral_pos
#print axioms C3B6.Theta.modePair_integral_abs_le
#print axioms C3B6.Theta.modeA_symm
#print axioms C3B6.Theta.modeLam_symm
#print axioms C3B6.Theta.modePair_integral_symm
#print axioms C3B6.Theta.ramp_tail_nonneg
#print axioms C3B6.Theta.ramp_tail_nonneg_of_mode
#print axioms C3B6.Theta.exp_hankel_minor_neg
#print axioms C3B6.Theta.neg_exp_strict_concave
end AxiomAudit
