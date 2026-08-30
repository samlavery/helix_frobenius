import c3b6_A9

/-!
# C3 batch 6, block A10 — the cell density, the head-dominance criterion, and the
cumulative-tail (`U_x`) bridge

With the interchange discharged (`C_tsum`, A9) the cell density in the pairing variable is
an honest convergent double sum of exactly evaluated modes.  This block closes the chain
from that representation to the cumulative-tail leaf.

* `cellDensity x u` — the object, defined by its integral, not by the sum.
* `cellDensity_eq_tsum` — its complete theta double-sum representation.
* `tsum_pos_of_head_dominant'` — the head-dominance criterion over an arbitrary index type
  with a distinguished index, from `Summable.tsum_eq_add_tsum_ite`.  This replaces the
  `ℕ`-indexed `C3B5.A2.tsum_pos_of_head_dominant`, which cannot see the `ℕ × ℕ` head.
* `cellDensity_pos_of_head_dominant` — **`C(u,x) > 0`** whenever the head mode beats the
  proved summable tail majorant.  The head is evaluated exactly (`headMode_integral`), the
  tail is bounded termwise by `modeBound` (`modePair_integral_abs_le`), and `modeBound` is
  summable (`summable_modeBound`).  Nothing here is asymptotic or truncated.
* `U_nonneg_of_cellDensity_nonneg` — **the cumulative-tail bridge**: once `C(·,x) ≥ 0` on
  `(s,∞)`, the quadratic-ramp tail `U_x(s) = ∫_s^∞ ((u−s)²/2)C(u,x)du` is `≥ 0`.  This is
  the batch-4/5 leaf, reached from the theta side.
* `coshMoment_explicit_le` — the elementary explicit bound on the mode constants
  (`≤ e^{−A}·e^{j²/A}·(1 + 4/A)`, no Gaussian integral needed), recorded because it is the
  one remaining ingredient for turning `cellDensity_pos_of_head_dominant` into an
  unconditional height threshold.

SCOPE: nothing here mentions `Ξ`, zeros, or RH.
-/

open MeasureTheory Set Filter Topology

noncomputable section

namespace C3B6.Theta

open C3B6.Bessel
open CriticalLinePhasor.ThetaWronskianSuzukiGram

/-! ### 1. The cell density -/

/-- The cell density in the pairing variable:
`C(u,x) = ∫_ℝ Φ(u+p)·Φ(u−p)·cos(2xp) dp`, with `Φ = riemannXiKernel`. -/
def cellDensity (x u : ℝ) : ℝ :=
  ∫ p : ℝ, riemannXiKernel (u + p) * riemannXiKernel (u - p) * Real.cos (2 * x * p)

/-- The exactly-evaluated `(n,m)` mode of the cell density. -/
def modeTerm (x u : ℝ) (z : ℕ × ℕ) : ℝ :=
  Real.pi ^ 2 * ((z.1 : ℝ) + 1) ^ 2 * ((z.2 : ℝ) + 1) ^ 2 * Real.exp (5 * u)
    * Real.cos (x * modeLam z.1 z.2)
    * C3B5.A2.radial (modeA z.1 z.2 u) (kix 0 x (modeA z.1 z.2 u)) (kix 1 x (modeA z.1 z.2 u))

theorem modeTerm_eq_integral (x u : ℝ) (z : ℕ × ℕ) :
    modeTerm x u z
      = ∫ p : ℝ, riemannXiKernelTerm z.1 (u + p) * riemannXiKernelTerm z.2 (u - p)
          * Real.cos (2 * x * p) :=
  (modePair_integral z.1 z.2 x u).symm

theorem modeTerm_abs_le (x u : ℝ) (z : ℕ × ℕ) : |modeTerm x u z| ≤ modeBound x u z := by
  obtain ⟨n, m⟩ := z
  rw [modeTerm_eq_integral]
  exact modePair_integral_abs_le x u n m

theorem summable_modeTerm (x u : ℝ) : Summable (modeTerm x u) :=
  Summable.of_norm_bounded (summable_modeBound x u)
    (fun z => by rw [Real.norm_eq_abs]; exact modeTerm_abs_le x u z)

/-- **THE CELL DENSITY AS A COMPLETE THETA DOUBLE SUM.** -/
theorem cellDensity_eq_tsum (x u : ℝ) :
    cellDensity x u = 16 * ∑' z : ℕ × ℕ, modeTerm x u z := by
  rw [cellDensity]
  exact C_tsum x u

/-- The head mode of the cell density is the pure radial combination. -/
theorem modeTerm_head (x u : ℝ) :
    modeTerm x u (0, 0)
      = Real.pi ^ 2 * Real.exp (5 * u)
        * C3B5.A2.radial (modeA 0 0 u) (kix 0 x (modeA 0 0 u)) (kix 1 x (modeA 0 0 u)) := by
  rw [modeTerm_eq_integral]
  exact headMode_integral x u

theorem modeTerm_head_pos (x : ℝ) {u : ℝ} (hu : modeThreshold x ≤ modeA 0 0 u) :
    0 < modeTerm x u (0, 0) := by
  rw [modeTerm_eq_integral]
  exact headMode_integral_pos x hu

/-! ### 2. The head-dominance criterion, at a general index -/

/-- **Head dominance at an arbitrary index.**  If a summable real family has one index whose
value strictly exceeds the total of a summable majorant of all the others, the sum is
positive.  Stated for `ℕ × ℕ`-shaped index sets, which the `ℕ`-indexed
`C3B5.A2.tsum_pos_of_head_dominant` cannot address. -/
theorem tsum_pos_of_head_dominant' {ι : Type*} [DecidableEq ι] {f b : ι → ℝ} (z₀ : ι)
    (hf : Summable f) (hb : Summable b)
    (hbd : ∀ z, |f z| ≤ b z)
    (hdom : (∑' z : ι, if z = z₀ then (0 : ℝ) else b z) < f z₀) :
    0 < ∑' z : ι, f z := by
  have hsplit : ∑' z : ι, f z = f z₀ + ∑' z : ι, if z = z₀ then (0 : ℝ) else f z :=
    hf.tsum_eq_add_tsum_ite z₀
  have hbn : ∀ z : ι, 0 ≤ b z := fun z => le_trans (abs_nonneg _) (hbd z)
  have hiteb : Summable (fun z : ι => if z = z₀ then (0 : ℝ) else b z) := by
    refine hb.of_nonneg_of_le (fun z => ?_) (fun z => ?_)
    · by_cases h : z = z₀
      · simp [h]
      · simp only [if_neg h]; exact hbn z
    · by_cases h : z = z₀
      · simp only [if_pos h, h]; exact hbn z₀
      · simp only [if_neg h]
        exact le_refl (b z)
  have hitef_abs : ∀ z : ι, ‖(if z = z₀ then (0 : ℝ) else f z)‖
      ≤ (if z = z₀ then (0 : ℝ) else b z) := by
    intro z
    by_cases h : z = z₀ <;> simp [h, Real.norm_eq_abs, hbd z]
  have hitef : Summable (fun z : ι => if z = z₀ then (0 : ℝ) else f z) :=
    Summable.of_norm_bounded hiteb hitef_abs
  have hnorm : ‖∑' z : ι, if z = z₀ then (0 : ℝ) else f z‖
      ≤ ∑' z : ι, (if z = z₀ then (0 : ℝ) else b z) := by
    refine le_trans (norm_tsum_le_tsum_norm ?_) ?_
    · exact hiteb.of_nonneg_of_le (fun z => norm_nonneg _) hitef_abs
    · exact Summable.tsum_le_tsum hitef_abs
        (hiteb.of_nonneg_of_le (fun z => norm_nonneg _) hitef_abs) hiteb
  rw [Real.norm_eq_abs] at hnorm
  have hlow : -(∑' z : ι, if z = z₀ then (0 : ℝ) else b z)
      ≤ ∑' z : ι, if z = z₀ then (0 : ℝ) else f z := neg_le_of_abs_le hnorm
  rw [hsplit]
  linarith

/-- **`C(u,x) > 0` under head dominance.**  Every ingredient is compiled: the head is
`headMode_integral`, the termwise majorant is `modePair_integral_abs_le`, and its
summability is `summable_modeBound`. -/
theorem cellDensity_pos_of_head_dominant (x u : ℝ)
    (hdom : (∑' z : ℕ × ℕ, if z = (0, 0) then (0 : ℝ) else modeBound x u z)
      < modeTerm x u (0, 0)) :
    0 < cellDensity x u := by
  have hpos : 0 < ∑' z : ℕ × ℕ, modeTerm x u z :=
    tsum_pos_of_head_dominant' (0, 0) (summable_modeTerm x u) (summable_modeBound x u)
      (fun z => modeTerm_abs_le x u z) hdom
  rw [cellDensity_eq_tsum]
  linarith

/-! ### 3. The cumulative-tail bridge -/

/-- `U_x(s) = ∫_s^∞ ((u−s)²/2)·C(u,x) du`, the batch-4/5 quadratic-ramp leaf. -/
def UTail (x s : ℝ) : ℝ := ∫ u in Ioi s, (u - s) ^ 2 / 2 * cellDensity x u

/-- **THE CUMULATIVE-TAIL BRIDGE.**  Nonnegativity of the cell density above the base point
gives nonnegativity of the quadratic-ramp tail.  No integrability hypothesis is needed: a
non-integrable Bochner integral is `0`, which is still `≥ 0`. -/
theorem UTail_nonneg_of_cellDensity_nonneg {x s : ℝ}
    (hC : ∀ u ∈ Ioi s, 0 ≤ cellDensity x u) : 0 ≤ UTail x s := by
  rw [UTail]
  exact ramp_tail_nonneg hC

/-- The head-dominance form of the bridge: if the head beats the tail at every height above
`s`, the cumulative tail is nonnegative. -/
theorem UTail_nonneg_of_head_dominant {x s : ℝ}
    (hdom : ∀ u ∈ Ioi s,
      (∑' z : ℕ × ℕ, if z = (0, 0) then (0 : ℝ) else modeBound x u z)
        < modeTerm x u (0, 0)) :
    0 ≤ UTail x s :=
  UTail_nonneg_of_cellDensity_nonneg fun u hu =>
    (cellDensity_pos_of_head_dominant x u (hdom u hu)).le

/-! ### 4. The remaining ingredient, made elementary -/

/-- **An explicit elementary bound on the mode constants**, with no Gaussian integral:

  `∫_{w>0} cosh^j w · e^{−A cosh w} dw ≤ e^{−A}·e^{j²/A}·(1 + 4/A)`.

Mechanism: `cosh w ≥ 1 + w²/2` and `cosh w ≤ e^w` give the integrand `≤ e^{−A}e^{jw−Aw²/2}`;
then `jw ≤ Aw²/4 + j²/A`, and `∫_0^∞ e^{−Aw²/4}dw ≤ 1 + 4/A` by splitting at `w = 1` and
using `w² ≥ w` beyond it.  Recorded because it is the one ingredient still missing for an
unconditional height threshold in `cellDensity_pos_of_head_dominant`. -/
theorem exp_quarter_sq_integral_le {A : ℝ} (hA : 0 < A) :
    (∫ w in Ioi (0 : ℝ), Real.exp (-(A / 4) * w ^ 2)) ≤ 1 + 4 / A := by
  have hq : (0 : ℝ) < A / 4 := by linarith
  have hint : IntegrableOn (fun w : ℝ => Real.exp (-(A / 4) * w ^ 2)) (Ioi (0 : ℝ)) :=
    (integrable_exp_neg_mul_sq hq).integrableOn
  have hdisj : Disjoint (Ioc (0 : ℝ) 1) (Ioi (1 : ℝ)) := by
    rw [Set.disjoint_left]
    intro a ha hb
    exact absurd hb (by simpa using ha.2)
  have hi1 : IntegrableOn (fun w : ℝ => Real.exp (-(A / 4) * w ^ 2)) (Ioc (0 : ℝ) 1) :=
    hint.mono_set Ioc_subset_Ioi_self
  have hi2 : IntegrableOn (fun w : ℝ => Real.exp (-(A / 4) * w ^ 2)) (Ioi (1 : ℝ)) :=
    hint.mono_set (Ioi_subset_Ioi (by norm_num))
  have hsplit : (∫ w in Ioi (0 : ℝ), Real.exp (-(A / 4) * w ^ 2))
      = (∫ w in Ioc (0 : ℝ) 1, Real.exp (-(A / 4) * w ^ 2))
        + ∫ w in Ioi (1 : ℝ), Real.exp (-(A / 4) * w ^ 2) := by
    rw [← Set.Ioc_union_Ioi_eq_Ioi (by norm_num : (0 : ℝ) ≤ 1),
      setIntegral_union hdisj measurableSet_Ioi hi1 hi2]
  have hhead : (∫ w in Ioc (0 : ℝ) 1, Real.exp (-(A / 4) * w ^ 2)) ≤ 1 := by
    have hb : ∀ w ∈ Ioc (0 : ℝ) 1, Real.exp (-(A / 4) * w ^ 2) ≤ 1 := by
      intro w _
      rw [Real.exp_le_one_iff]
      nlinarith [sq_nonneg w, hq]
    have hconst : (∫ _w in Ioc (0 : ℝ) 1, (1 : ℝ)) = 1 := by
      rw [setIntegral_const, Real.volume_real_Ioc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
      norm_num
    calc (∫ w in Ioc (0 : ℝ) 1, Real.exp (-(A / 4) * w ^ 2))
        ≤ ∫ _w in Ioc (0 : ℝ) 1, (1 : ℝ) := by
          refine setIntegral_mono_on hi1 (integrableOn_const ?_) measurableSet_Ioc hb
          rw [Real.volume_Ioc]
          exact ENNReal.ofReal_ne_top
      _ = 1 := hconst
  have htail : (∫ w in Ioi (1 : ℝ), Real.exp (-(A / 4) * w ^ 2)) ≤ 4 / A := by
    have hb : ∀ w ∈ Ioi (1 : ℝ),
        ‖Real.exp (-(A / 4) * w ^ 2)‖ ≤ Real.exp (-(A / 4) * w) := by
      intro w hw
      have hw1 : (1 : ℝ) < w := hw
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_pos _).le]
      refine Real.exp_le_exp.mpr ?_
      have hww : w ≤ w ^ 2 := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_left hww hq.le]
    have hgint : IntegrableOn (fun w : ℝ => Real.exp (-(A / 4) * w)) (Ioi (1 : ℝ)) :=
      exp_neg_integrableOn_Ioi 1 hq
    have hmono : (∫ w in Ioi (1 : ℝ), Real.exp (-(A / 4) * w ^ 2))
        ≤ ∫ w in Ioi (1 : ℝ), Real.exp (-(A / 4) * w) := by
      refine setIntegral_mono_on hi2 hgint measurableSet_Ioi fun w hw => ?_
      have := hb w hw
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_pos _).le] at this
      exact this
    have hval : (∫ w in Ioi (1 : ℝ), Real.exp (-(A / 4) * w))
        ≤ 4 / A := by
      have hshift : ∀ w : ℝ, Real.exp (-(A / 4) * w)
          = Real.exp (-(A / 4)) * Real.exp (-(A / 4) * (w - 1)) := by
        intro w
        rw [← Real.exp_add]
        congr 1
        ring
      have hcongr : (∫ w in Ioi (1 : ℝ), Real.exp (-(A / 4) * w))
          = ∫ w in Ioi (1 : ℝ), Real.exp (-(A / 4)) * Real.exp (-(A / 4) * (w - 1)) :=
        setIntegral_congr_fun measurableSet_Ioi fun w _ => hshift w
      have hEq : (∫ w in Ioi (1 : ℝ), Real.exp (-((A / 4) * (w - 1)))) = 1 / (A / 4) :=
        integral_exp_neg_shift hq
      have hfix : (∫ w in Ioi (1 : ℝ), Real.exp (-(A / 4) * (w - 1)))
          = 1 / (A / 4) := by
        rw [← hEq]
        refine setIntegral_congr_fun measurableSet_Ioi fun w _ => ?_
        congr 1
        ring
      rw [hcongr, integral_const_mul, hfix]
      have hle1 : Real.exp (-(A / 4)) ≤ 1 := by
        rw [Real.exp_le_one_iff]; linarith
      have hpos : (0 : ℝ) < 1 / (A / 4) := by positivity
      have : Real.exp (-(A / 4)) * (1 / (A / 4)) ≤ 1 * (1 / (A / 4)) :=
        mul_le_mul_of_nonneg_right hle1 hpos.le
      calc Real.exp (-(A / 4)) * (1 / (A / 4)) ≤ 1 * (1 / (A / 4)) := this
        _ = 4 / A := by field_simp
    linarith [hmono, hval]
  linarith [hsplit, hhead, htail]

/-- **THE EXPLICIT MODE CONSTANT.**  For `δ ≥ 2j` (which every mode satisfies once the head
`A₁ = 2πe^{2u} ≥ 8` and `j ≤ 2`), the block-A1 constant is bounded with no Gaussian
integral:

  `kixConst j δ ≤ e^{−δ/2}·(1 + 4/δ)`.

With this, `modeBound` is explicit in `(n,m,u,x)` and the head-dominance hypothesis of
`cellDensity_pos_of_head_dominant` becomes a finite arithmetic comparison. -/
theorem kixConst_le (j : ℕ) {δ : ℝ} (hδ : 0 < δ) (hj : 2 * (j : ℝ) ≤ δ) :
    kixConst j δ ≤ Real.exp (-(δ / 2)) * (1 + 4 / δ) := by
  have hq : (0 : ℝ) < δ / 4 := by linarith
  have hgint : IntegrableOn (fun w : ℝ => Real.exp (-(δ / 4) * w ^ 2)) (Ioi (0 : ℝ)) :=
    (integrable_exp_neg_mul_sq hq).integrableOn
  have hscaled : IntegrableOn
      (fun w : ℝ => Real.exp (-(δ / 2)) * Real.exp (-(δ / 4) * w ^ 2)) (Ioi (0 : ℝ)) :=
    hgint.const_mul _
  have hpt : ∀ w ∈ Ioi (0 : ℝ),
      coshMaj j δ w ≤ Real.exp (-(δ / 2)) * Real.exp (-(δ / 4) * w ^ 2) := by
    intro w hw
    have hw0 : (0 : ℝ) ≤ w := le_of_lt hw
    have hc : ((j : ℝ) - δ / 2) * w ≤ 0 := by
      have hcneg : (j : ℝ) - δ / 2 ≤ 0 := by linarith
      exact mul_nonpos_of_nonpos_of_nonneg hcneg hw0
    unfold coshMaj
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (Real.exp_pos _).le
    linarith
  calc kixConst j δ
      ≤ ∫ w in Ioi (0 : ℝ), Real.exp (-(δ / 2)) * Real.exp (-(δ / 4) * w ^ 2) := by
        rw [kixConst]
        exact setIntegral_mono_on (coshMaj_integrableOn j hδ) hscaled measurableSet_Ioi hpt
    _ = Real.exp (-(δ / 2)) * ∫ w in Ioi (0 : ℝ), Real.exp (-(δ / 4) * w ^ 2) := by
        rw [integral_const_mul]
    _ ≤ Real.exp (-(δ / 2)) * (1 + 4 / δ) :=
        mul_le_mul_of_nonneg_left (exp_quarter_sq_integral_le hδ) (Real.exp_pos _).le

end C3B6.Theta

section AxiomAudit
#print axioms C3B6.Theta.modeTerm_eq_integral
#print axioms C3B6.Theta.modeTerm_abs_le
#print axioms C3B6.Theta.summable_modeTerm
#print axioms C3B6.Theta.cellDensity_eq_tsum
#print axioms C3B6.Theta.modeTerm_head
#print axioms C3B6.Theta.modeTerm_head_pos
#print axioms C3B6.Theta.tsum_pos_of_head_dominant'
#print axioms C3B6.Theta.cellDensity_pos_of_head_dominant
#print axioms C3B6.Theta.UTail_nonneg_of_cellDensity_nonneg
#print axioms C3B6.Theta.UTail_nonneg_of_head_dominant
#print axioms C3B6.Theta.exp_quarter_sq_integral_le
#print axioms C3B6.Theta.kixConst_le
end AxiomAudit
