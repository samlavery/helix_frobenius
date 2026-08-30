import c3b6_A5

/-!
# C3 batch 6, block A6 — obligation B, part 2: explicit mode bounds and the summable
majorant of the `(n,m)` double family

Block A5 evaluated one `(n,m)` cross term exactly.  For a remainder bound over the full
double sum three quantitative facts are needed, and they are proved here.

1. **A quantitative lower bound for `K_{ix}`** (`kix_zero_lower`).  Block A4 proved
   `K_{ix}(A) > 0` for `A > 4(|x|+1)²`; the head-versus-tail comparison needs a *size*, and
   the same split gives it: for `A ≥ 8(|x|+1)²`, with `h = 1/(|x|+1)`,

       `K_{ix}(A) ≥ e^{−A cosh h} · h/4`.

2. **An explicit upper bound for the radial combination** (`radial_abs_le`), directly from
   the block-A1 decay bound — no logarithmic-derivative information used, so it is valid at
   *every* mode, including those below the turning point where `K_{ix}` oscillates.

3. **A summable majorant for the whole `(n,m)` family** (`summable_modeBound`).  The
   mechanism is the hyperbola inequality `ab ≥ (a+b)/2` for `a,b ≥ 1`, which converts the
   single exponential `e^{−A₁·ab}` into a product `e^{−A₁a/2}·e^{−A₁b/2}` and hence the
   double family into a product of two summable one-dimensional families.  This is the
   "explicit summable majorant" the sum/integral interchange requires.

Also recorded: `cosh_one_lt_two`, the reason the head can beat the tail at all —
the head carries `e^{−A₁ cosh h}` with `cosh h ≤ cosh 1 < 2` (since `h ≤ 1`), while every
off-head mode carries at most `e^{−2A₁}`.  The gap `e^{(2−cosh h)A₁}` grows with `A₁`.

SCOPE: nothing here mentions `Ξ`, zeros, or RH.
-/

open MeasureTheory Set Filter Topology

noncomputable section

namespace C3B6.Theta

open C3B6.Bessel
open CriticalLinePhasor.ThetaWronskianSuzukiGram

/-! ### 1. A quantitative lower bound for `K_{ix}` -/

/-- **The quantitative first-lobe bound.**  With `h = 1/(|x|+1)`,
`K_{ix}(A) ≥ e^{−A cosh h}·h/4` as soon as `A ≥ 8(|x|+1)²`. -/
theorem kix_zero_lower {x A : ℝ} (hA : 8 * (|x| + 1) ^ 2 ≤ A) :
    Real.exp (-(A * Real.cosh (1 / (|x| + 1)))) * (1 / (|x| + 1)) / 4 ≤ kix 0 x A := by
  set h : ℝ := 1 / (|x| + 1) with hhdef
  have hx1 : (0 : ℝ) < |x| + 1 := by positivity
  have hh : 0 < h := by rw [hhdef]; positivity
  have hh1 : h ≤ 1 := by
    rw [hhdef, div_le_one hx1]
    have := abs_nonneg x; linarith
  have hA0 : 0 < A := by
    have : (0 : ℝ) < 8 * (|x| + 1) ^ 2 := by positivity
    linarith
  have hxh : |x| * h ≤ 1 := by
    rw [hhdef, mul_one_div, div_le_one hx1]; linarith
  have hsh : 0 < Real.sinh h := Real.sinh_pos_iff.mpr hh
  have hM : (0 : ℝ) < Real.exp (-(A * Real.cosh h)) := Real.exp_pos _
  -- split
  have hdisj : Disjoint (Ioc (0 : ℝ) h) (Ioi h) := by
    rw [Set.disjoint_left]
    intro a ha hb
    exact absurd hb (by simpa using ha.2)
  have hi1 : IntegrableOn (kixTerm 0 x A) (Ioc (0 : ℝ) h) :=
    (kixTerm_integrableOn 0 x hA0).mono_set Ioc_subset_Ioi_self
  have hi2 : IntegrableOn (kixTerm 0 x A) (Ioi h) :=
    (kixTerm_integrableOn 0 x hA0).mono_set (Ioi_subset_Ioi (le_of_lt hh))
  have hsplit : kix 0 x A
      = (∫ w in Ioc (0 : ℝ) h, kixTerm 0 x A w) + ∫ w in Ioi h, kixTerm 0 x A w := by
    unfold kix
    rw [← Set.Ioc_union_Ioi_eq_Ioi (le_of_lt hh),
      setIntegral_union hdisj measurableSet_Ioi hi1 hi2]
  have hhead := kix_head_ge hA0 hh hxh
  have htail' : -(Real.exp (-(A * Real.cosh h)) * (1 / (A * Real.sinh h)))
      ≤ ∫ w in Ioi h, kixTerm 0 x A w :=
    neg_le_of_abs_le (kix_tail_abs_le (x := x) hA0 hh)
  -- the tail is at most a quarter of the head's length factor
  have hstep : 8 ≤ A * h ^ 2 := by
    have hhsq : h ^ 2 = 1 / (|x| + 1) ^ 2 := by rw [hhdef, div_pow, one_pow]
    have hx2 : (0 : ℝ) < (|x| + 1) ^ 2 := by positivity
    rw [hhsq, mul_one_div, le_div_iff₀ hx2]
    linarith
  have hshh : h / 2 ≤ Real.sinh h := half_le_sinh (le_of_lt hh)
  have hAs : 0 < A * Real.sinh h := mul_pos hA0 hsh
  have hquarter : 1 / (A * Real.sinh h) ≤ h / 4 := by
    rw [div_le_div_iff₀ hAs (by norm_num : (0:ℝ) < 4)]
    have h1 : A * (h / 2) ≤ A * Real.sinh h := mul_le_mul_of_nonneg_left hshh hA0.le
    nlinarith [mul_le_mul_of_nonneg_left h1 hh.le, hstep, hh]
  have hfinal : Real.exp (-(A * Real.cosh h)) * (1 / (A * Real.sinh h))
      ≤ Real.exp (-(A * Real.cosh h)) * (h / 4) :=
    mul_le_mul_of_nonneg_left hquarter hM.le
  rw [hsplit]
  have hgoal : Real.exp (-(A * Real.cosh h)) * h / 4
      = Real.exp (-(A * Real.cosh h)) * (1 / 2) * h
        - Real.exp (-(A * Real.cosh h)) * (h / 4) := by ring
  rw [hgoal]
  linarith

/-! ### 2. An explicit upper bound for the radial combination -/

/-- **The mode upper bound.**  Uses only the block-A1 decay estimate, so it holds at every
`A ≥ δ > 0` — including below the turning point, where `K_{ix}` oscillates and no
logarithmic-derivative information is available. -/
theorem radial_abs_le (x : ℝ) {A δ : ℝ} (hδ : 0 < δ) (hA : δ ≤ A) :
    |C3B5.A2.radial A (kix 0 x A) (kix 1 x A)|
      ≤ ((A ^ 2 + 9) * kixConst 0 δ + 6 * A * kixConst 1 δ) * Real.exp (-(A - δ)) := by
  have hA0 : 0 < A := lt_of_lt_of_le hδ hA
  have hb0 := kix_abs_le 0 x hδ hA
  have hb1 := kix_abs_le 1 x hδ hA
  have hE : (0 : ℝ) < Real.exp (-(A - δ)) := Real.exp_pos _
  have hstep : |C3B5.A2.radial A (kix 0 x A) (kix 1 x A)|
      ≤ (A ^ 2 + 9) * |kix 0 x A| + 6 * A * |kix 1 x A| := by
    unfold C3B5.A2.radial
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ A ^ 2 + 9),
      abs_of_nonneg (by positivity : (0:ℝ) ≤ 6 * A)]
  refine hstep.trans ?_
  have h1 : (A ^ 2 + 9) * |kix 0 x A|
      ≤ (A ^ 2 + 9) * (Real.exp (-(A - δ)) * kixConst 0 δ) :=
    mul_le_mul_of_nonneg_left hb0 (by positivity)
  have h2 : 6 * A * |kix 1 x A|
      ≤ 6 * A * (Real.exp (-(A - δ)) * kixConst 1 δ) :=
    mul_le_mul_of_nonneg_left hb1 (by positivity)
  nlinarith [h1, h2]

/-! ### 3. `cosh 1 < 2`: why the head can beat the tail -/

theorem cosh_one_lt_two : Real.cosh 1 < 2 := by
  rw [Real.cosh_eq]
  have h1 : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
  have h2 : Real.exp (-1 : ℝ) < 1 := by
    rw [show (-1 : ℝ) = -(1 : ℝ) by norm_num]
    have := Real.exp_lt_one_iff (x := (-1 : ℝ))
    rw [this]
    norm_num
  linarith

/-- On `0 < h ≤ 1` the head's exponential rate `cosh h` is strictly below `2`, while every
off-head mode has rate at least `2`.  This is the entire mechanism of head dominance. -/
theorem cosh_lt_two_of_le_one {h : ℝ} (hh : 0 ≤ h) (hh1 : h ≤ 1) : Real.cosh h < 2 :=
  lt_of_le_of_lt (cosh_le_cosh_of_le hh hh1) cosh_one_lt_two

/-! ### 4. The head mode and the hyperbola comparison -/

theorem modeA_head (u : ℝ) : modeA 0 0 u = 2 * Real.pi * Real.exp (2 * u) := by
  unfold modeA; norm_num

theorem modeA_head_pos (u : ℝ) : 0 < modeA 0 0 u := modeA_pos 0 0 u

/-- Every mode's radial variable is a multiple of the head's by the hyperbola parameter
`ab = (n+1)(m+1) ≥ 1`. -/
theorem modeA_factor (n m : ℕ) (u : ℝ) :
    modeA n m u = (((n : ℝ) + 1) * ((m : ℝ) + 1)) * modeA 0 0 u := by
  unfold modeA
  norm_num
  ring

theorem one_le_cast_succ (n : ℕ) : (1 : ℝ) ≤ (n : ℝ) + 1 := by
  have := Nat.cast_nonneg (α := ℝ) n
  linarith

theorem one_le_prod (n m : ℕ) : (1 : ℝ) ≤ ((n : ℝ) + 1) * ((m : ℝ) + 1) := by
  have h1 := one_le_cast_succ n
  have h2 := one_le_cast_succ m
  nlinarith

theorem modeA_ge_head (n m : ℕ) (u : ℝ) : modeA 0 0 u ≤ modeA n m u := by
  rw [modeA_factor n m u]
  nlinarith [one_le_prod n m, modeA_head_pos u]

/-- Off the head, the radial variable is at least **twice** the head's. -/
theorem modeA_two_le {n m : ℕ} (h : ¬(n = 0 ∧ m = 0)) (u : ℝ) :
    2 * modeA 0 0 u ≤ modeA n m u := by
  have hprod : (2 : ℝ) ≤ ((n : ℝ) + 1) * ((m : ℝ) + 1) := by
    rcases Nat.eq_zero_or_pos n with hn | hn
    · have hm : m ≠ 0 := by
        intro hm0; exact h ⟨hn, hm0⟩
      have hm1 : (1 : ℕ) ≤ m := Nat.one_le_iff_ne_zero.mpr hm
      have : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm1
      have hn0 : ((n : ℝ) + 1) = 1 := by rw [hn]; norm_num
      rw [hn0, one_mul]; linarith
    · have : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      have h2 : (1 : ℝ) ≤ (m : ℝ) + 1 := one_le_cast_succ m
      nlinarith
  rw [modeA_factor n m u]
  nlinarith [modeA_head_pos u, hprod]

/-- **The hyperbola inequality.**  `ab ≥ (a+b)/2` for `a, b ≥ 1` — the step that turns one
exponential in the product into a product of two exponentials, and hence the double family
into a product of two summable families. -/
theorem prod_ge_half_sum {a b : ℝ} (ha : 1 ≤ a) (hb : 1 ≤ b) : (a + b) / 2 ≤ a * b := by
  nlinarith [ha, hb]

/-! ### 5. The summable majorant of the double family -/

/-- The explicit majorant of the `(n,m)` mode contribution, with the head's decay rate
factored out. -/
def modeBound (x u : ℝ) (q : ℕ × ℕ) : ℝ :=
  Real.pi ^ 2 * (((q.1 : ℝ) + 1) * ((q.2 : ℝ) + 1)) ^ 2 * Real.exp (5 * u)
    * (((modeA q.1 q.2 u) ^ 2 + 9) * kixConst 0 (modeA 0 0 u)
        + 6 * (modeA q.1 q.2 u) * kixConst 1 (modeA 0 0 u))
    * Real.exp (-(modeA q.1 q.2 u - modeA 0 0 u))

theorem modeBound_nonneg (x u : ℝ) (q : ℕ × ℕ) : 0 ≤ modeBound x u q := by
  unfold modeBound
  have h1 : 0 ≤ kixConst 0 (modeA 0 0 u) := kixConst_nonneg 0 _
  have h2 : 0 ≤ kixConst 1 (modeA 0 0 u) := kixConst_nonneg 1 _
  have h3 : 0 < modeA q.1 q.2 u := modeA_pos _ _ _
  have hpi := Real.pi_pos
  positivity

/-- The one-dimensional summable family: `(n+1)^4 · e^{−c(n+1)}`. -/
theorem summable_pow_exp_shift (k : ℕ) {c : ℝ} (hc : 0 < c) :
    Summable (fun n : ℕ => ((n : ℝ) + 1) ^ k * Real.exp (-c * ((n : ℝ) + 1))) := by
  have hbase : Summable (fun n : ℕ => (n : ℝ) ^ k * Real.exp (-c * n)) :=
    Real.summable_pow_mul_exp_neg_nat_mul k hc
  have hshift : Summable (fun n : ℕ =>
      ((n + 1 : ℕ) : ℝ) ^ k * Real.exp (-c * ((n + 1 : ℕ) : ℝ))) :=
    (summable_nat_add_iff 1).2 hbase
  refine hshift.congr fun n => ?_
  push_cast
  ring_nf

/-- **THE SUMMABLE MAJORANT.**  The `(n,m)` mode majorant is summable over `ℕ × ℕ`,
by the hyperbola inequality plus a product of two one-dimensional exponential families. -/
theorem summable_modeBound (x u : ℝ) : Summable (modeBound x u) := by
  set A₁ : ℝ := modeA 0 0 u with hA1def
  have hA1 : 0 < A₁ := modeA_head_pos u
  set C₀ : ℝ := kixConst 0 A₁ with hC0
  set C₁ : ℝ := kixConst 1 A₁ with hC1
  have hC0n : 0 ≤ C₀ := kixConst_nonneg 0 _
  have hC1n : 0 ≤ C₁ := kixConst_nonneg 1 _
  -- the constant absorbing everything that does not grow with `(n,m)`
  set M : ℝ := Real.pi ^ 2 * Real.exp (5 * u) * Real.exp A₁
      * ((A₁ ^ 2 + 9) * C₀ + 6 * A₁ * C₁ + 1) with hM
  have hMn : 0 ≤ M := by
    rw [hM]
    have hpi := Real.pi_pos
    positivity
  -- one-dimensional summable family
  have hhalf : (0 : ℝ) < A₁ / 2 := by linarith
  set g : ℕ → ℝ := fun n => ((n : ℝ) + 1) ^ 4 * Real.exp (-(A₁ / 2) * ((n : ℝ) + 1)) with hg
  have hgs : Summable g := summable_pow_exp_shift 4 hhalf
  have hgn : ∀ n, 0 ≤ g n := by
    intro n; rw [hg]; positivity
  have hprodsum : Summable (fun q : ℕ × ℕ => g q.1 * g q.2) :=
    hgs.mul_of_nonneg hgs hgn hgn
  have hscaled : Summable (fun q : ℕ × ℕ => M * (g q.1 * g q.2)) := hprodsum.mul_left M
  refine Summable.of_nonneg_of_le (fun q => modeBound_nonneg x u q) ?_ hscaled
  intro q
  obtain ⟨n, m⟩ := q
  set a : ℝ := (n : ℝ) + 1 with ha
  set b : ℝ := (m : ℝ) + 1 with hb
  have ha1 : (1 : ℝ) ≤ a := by rw [ha]; exact one_le_cast_succ n
  have hb1 : (1 : ℝ) ≤ b := by rw [hb]; exact one_le_cast_succ m
  have hab1 : (1 : ℝ) ≤ a * b := by nlinarith
  have hAfac : modeA n m u = (a * b) * A₁ := by
    rw [hA1def, ha, hb]; exact modeA_factor n m u
  -- exponential: `e^{-(ab-1)A₁} ≤ e^{A₁}·e^{-(A₁/2)a}·e^{-(A₁/2)b}`
  have hexp : Real.exp (-(modeA n m u - A₁))
      ≤ Real.exp A₁ * (Real.exp (-(A₁ / 2) * a) * Real.exp (-(A₁ / 2) * b)) := by
    rw [← Real.exp_add, ← Real.exp_add, hAfac]
    refine Real.exp_le_exp.mpr ?_
    have hhyp : (a + b) / 2 ≤ a * b := prod_ge_half_sum ha1 hb1
    nlinarith [hhyp, hA1]
  -- polynomial: `(ab)^2·((ab)^2A₁^2 + 9 + 6abA₁)·(C₀+C₁) ≤ (a^4 b^4)·(...)`
  have hpoly : (((modeA n m u) ^ 2 + 9) * C₀ + 6 * (modeA n m u) * C₁)
      ≤ (a * b) ^ 2 * ((A₁ ^ 2 + 9) * C₀ + 6 * A₁ * C₁ + 1) := by
    rw [hAfac]
    have hab2 : (1 : ℝ) ≤ (a * b) ^ 2 := by nlinarith
    have t1 : 0 ≤ C₀ * ((a * b) ^ 2 - 1) := mul_nonneg hC0n (by linarith)
    have t2 : 0 ≤ A₁ * C₁ * (a * b) * ((a * b) - 1) :=
      mul_nonneg (mul_nonneg (mul_nonneg hA1.le hC1n) (by linarith)) (by linarith)
    have t3 : (0 : ℝ) ≤ (a * b) ^ 2 := sq_nonneg _
    nlinarith [t1, t2, t3]
  have hpi := Real.pi_pos
  have habpos : (0 : ℝ) < a * b := by linarith
  have hE : (0 : ℝ) < Real.exp (-(modeA n m u - A₁)) := Real.exp_pos _
  have hcoef : (0 : ℝ) ≤ Real.pi ^ 2 * (a * b) ^ 2 * Real.exp (5 * u) := by positivity
  unfold modeBound
  simp only []
  calc Real.pi ^ 2 * (a * b) ^ 2 * Real.exp (5 * u)
        * (((modeA n m u) ^ 2 + 9) * C₀ + 6 * (modeA n m u) * C₁)
        * Real.exp (-(modeA n m u - A₁))
      ≤ Real.pi ^ 2 * (a * b) ^ 2 * Real.exp (5 * u)
        * ((a * b) ^ 2 * ((A₁ ^ 2 + 9) * C₀ + 6 * A₁ * C₁ + 1))
        * Real.exp (-(modeA n m u - A₁)) := by
        refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpoly hcoef) hE.le
    _ ≤ Real.pi ^ 2 * (a * b) ^ 2 * Real.exp (5 * u)
        * ((a * b) ^ 2 * ((A₁ ^ 2 + 9) * C₀ + 6 * A₁ * C₁ + 1))
        * (Real.exp A₁ * (Real.exp (-(A₁ / 2) * a) * Real.exp (-(A₁ / 2) * b))) := by
        refine mul_le_mul_of_nonneg_left hexp ?_
        have hpos : (0 : ℝ) ≤ (A₁ ^ 2 + 9) * C₀ + 6 * A₁ * C₁ + 1 := by positivity
        positivity
    _ = M * ((a ^ 4 * Real.exp (-(A₁ / 2) * a)) * (b ^ 4 * Real.exp (-(A₁ / 2) * b))) := by
        rw [hM]; ring

end C3B6.Theta

section AxiomAudit
#print axioms C3B6.Theta.kix_zero_lower
#print axioms C3B6.Theta.radial_abs_le
#print axioms C3B6.Theta.cosh_one_lt_two
#print axioms C3B6.Theta.cosh_lt_two_of_le_one
#print axioms C3B6.Theta.modeA_factor
#print axioms C3B6.Theta.modeA_ge_head
#print axioms C3B6.Theta.modeA_two_le
#print axioms C3B6.Theta.prod_ge_half_sum
#print axioms C3B6.Theta.summable_pow_exp_shift
#print axioms C3B6.Theta.summable_modeBound
end AxiomAudit
