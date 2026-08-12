import RequestProject.RectResidue
import RequestProject.GlobalCarry

/-!
# Fuse #3, the assembly (part 1): winding and residue on general rectangles

Strip poles have arbitrary real part, so the detection box is a rectangle,
not a centred square.  This file extends the repo's compiled winding to
that generality:

* `rect_winding` — `∮ (z−ρ)⁻¹ = 2πi` over any rectangle with `ρ` interior:
  nine-piece splitting via the compiled `horizontal_add`/`vertical_add`,
  Cauchy–Goursat on the eight `ρ`-free pieces, the compiled centred-square
  winding on the ninth;
* `rect_residue_of_simple_pole` — the residue identity
  `∮ Q·F = 2πi·res·F(ρ)` on general rectangles with `ρ` interior, for a
  simple-pole decomposition `Q = res·(s−ρ)⁻¹ + g` and entire `F` — the
  general-position form of the compiled square identity.

Part 2 (`carry_detects_simple_pole`) glues this to the global carry.
No `axiom`, no `sorry`.
-/

open Complex Set MeasureTheory intervalIntegral
open scoped Interval Real

namespace CriticalLinePhasor.CarryDetection

open CriticalLinePhasor.ContourArgument
open CriticalLinePhasor.RectResidue

/-- Continuity of the Cauchy kernel along a vertical line missing the pole. -/
lemma contKernel_vline {ρ : ℂ} {x : ℝ} (hx : x ≠ ρ.re) :
    Continuous fun y : ℝ => ((x : ℂ) + y * I - ρ)⁻¹ := by
  apply Continuous.inv₀
  · fun_prop
  · intro y
    intro h
    apply hx
    have h2 := congrArg Complex.re h
    simp at h2
    linarith [h2]

/-- Continuity of the Cauchy kernel along a horizontal line missing the pole. -/
lemma contKernel_hline {ρ : ℂ} {y : ℝ} (hy : y ≠ ρ.im) :
    Continuous fun x : ℝ => ((x : ℂ) + y * I - ρ)⁻¹ := by
  apply Continuous.inv₀
  · fun_prop
  · intro x
    intro h
    apply hy
    have h2 := congrArg Complex.im h
    simp at h2
    linarith [h2]

/-- The Cauchy kernel is differentiable on any closed box avoiding the pole. -/
lemma diffKernel_box {ρ : ℂ} {a b c d : ℝ}
    (havoid : ∀ z ∈ Icc a b ×ℂ Icc c d, z ≠ ρ) :
    DifferentiableOn ℂ (fun z : ℂ => (z - ρ)⁻¹) (Icc a b ×ℂ Icc c d) := by
  apply DifferentiableOn.inv
  · exact (differentiable_id.sub_const ρ).differentiableOn
  · intro z hz
    exact sub_ne_zero.mpr (havoid z hz)

/-- **The winding on a general rectangle**: for `ρ` interior,
`∮ (z−ρ)⁻¹ = 2πi`. -/
theorem rect_winding {ρ : ℂ} {a b c d : ℝ}
    (hax : a < ρ.re) (hxb : ρ.re < b) (hcy : c < ρ.im) (hyd : ρ.im < d) :
    rectangleBoundaryIntegral (fun z : ℂ => (z - ρ)⁻¹) a b c d
      = 2 * Real.pi * I := by
  set r : ℝ := (min (min (ρ.re - a) (b - ρ.re)) (min (ρ.im - c) (d - ρ.im))) / 2
    with hr_def
  have hr : 0 < r := by
    rw [hr_def]
    have h1 : 0 < ρ.re - a := by linarith
    have h2 : 0 < b - ρ.re := by linarith
    have h3 : 0 < ρ.im - c := by linarith
    have h4 : 0 < d - ρ.im := by linarith
    positivity
  have hra : r < ρ.re - a := by
    rw [hr_def]
    have h1 : min (min (ρ.re - a) (b - ρ.re)) (min (ρ.im - c) (d - ρ.im))
        ≤ ρ.re - a := le_trans (min_le_left _ _) (min_le_left _ _)
    linarith [hr]
  have hrb : r < b - ρ.re := by
    rw [hr_def]
    have h1 : min (min (ρ.re - a) (b - ρ.re)) (min (ρ.im - c) (d - ρ.im))
        ≤ b - ρ.re := le_trans (min_le_left _ _) (min_le_right _ _)
    linarith [hr]
  have hrc : r < ρ.im - c := by
    rw [hr_def]
    have h1 : min (min (ρ.re - a) (b - ρ.re)) (min (ρ.im - c) (d - ρ.im))
        ≤ ρ.im - c := le_trans (min_le_right _ _) (min_le_left _ _)
    linarith [hr]
  have hrd : r < d - ρ.im := by
    rw [hr_def]
    have h1 : min (min (ρ.re - a) (b - ρ.re)) (min (ρ.im - c) (d - ρ.im))
        ≤ d - ρ.im := le_trans (min_le_right _ _) (min_le_right _ _)
    linarith [hr]
  set x₁ : ℝ := ρ.re - r
  set x₂ : ℝ := ρ.re + r
  set y₁ : ℝ := ρ.im - r
  set y₂ : ℝ := ρ.im + r
  have hax₁ : a < x₁ := by simp only [x₁]; linarith
  have hx₂b : x₂ < b := by simp only [x₂]; linarith
  have hcy₁ : c < y₁ := by simp only [y₁]; linarith
  have hy₂d : y₂ < d := by simp only [y₂]; linarith
  have hx₁₂ : x₁ < x₂ := by simp only [x₁, x₂]; linarith
  have hy₁₂ : y₁ < y₂ := by simp only [y₁, y₂]; linarith
  set f : ℂ → ℂ := fun z => (z - ρ)⁻¹ with hf
  -- line-continuity data for the splits
  have hcont_c : Continuous fun x : ℝ => f ((x : ℂ) + c * I) :=
    contKernel_hline (by linarith)
  have hcont_d : Continuous fun x : ℝ => f ((x : ℂ) + d * I) :=
    contKernel_hline (by linarith)
  have hcont_x₁ : Continuous fun y : ℝ => f ((x₁ : ℂ) + y * I) :=
    contKernel_vline (by simp only [x₁]; intro h; linarith [h])
  have hcont_x₂ : Continuous fun y : ℝ => f ((x₂ : ℂ) + y * I) :=
    contKernel_vline (by simp only [x₂]; intro h; linarith [h])
  -- split vertically at x₁ then x₂
  have hsplit1 := rectangleBoundaryIntegral_vertical_add f a x₁ b c d
    hcont_c hcont_d
  have hsplit2 := rectangleBoundaryIntegral_vertical_add f x₁ x₂ b c d
    hcont_c hcont_d
  -- left and right strips are ρ-free
  have hleft : rectangleBoundaryIntegral f a x₁ c d = 0 := by
    apply rectangleBoundaryIntegral_eq_zero_of_differentiableOn f a x₁ c d
      (by linarith) (by linarith)
    apply diffKernel_box
    intro z hz
    rw [Complex.mem_reProdIm] at hz
    intro hcon
    have hre : z.re ≤ x₁ := hz.1.2
    rw [hcon] at hre
    simp only [x₁] at hre
    linarith
  have hright : rectangleBoundaryIntegral f x₂ b c d = 0 := by
    apply rectangleBoundaryIntegral_eq_zero_of_differentiableOn f x₂ b c d
      (by linarith) (by linarith)
    apply diffKernel_box
    intro z hz
    rw [Complex.mem_reProdIm] at hz
    intro hcon
    have hre : x₂ ≤ z.re := hz.1.1
    rw [hcon] at hre
    simp only [x₂] at hre
    linarith
  -- split the middle strip horizontally at y₁ then y₂
  have hsplit3 := rectangleBoundaryIntegral_horizontal_add f x₁ x₂ c y₁ d
    hcont_x₁ hcont_x₂
  have hsplit4 := rectangleBoundaryIntegral_horizontal_add f x₁ x₂ y₁ y₂ d
    hcont_x₁ hcont_x₂
  have hbot : rectangleBoundaryIntegral f x₁ x₂ c y₁ = 0 := by
    apply rectangleBoundaryIntegral_eq_zero_of_differentiableOn f x₁ x₂ c y₁
      (by linarith) (by linarith)
    apply diffKernel_box
    intro z hz
    rw [Complex.mem_reProdIm] at hz
    intro hcon
    have him : z.im ≤ y₁ := hz.2.2
    rw [hcon] at him
    simp only [y₁] at him
    linarith
  have htop : rectangleBoundaryIntegral f x₁ x₂ y₂ d = 0 := by
    apply rectangleBoundaryIntegral_eq_zero_of_differentiableOn f x₁ x₂ y₂ d
      (by linarith) (by linarith)
    apply diffKernel_box
    intro z hz
    rw [Complex.mem_reProdIm] at hz
    intro hcon
    have him : y₂ ≤ z.im := hz.2.1
    rw [hcon] at him
    simp only [y₂] at him
    linarith
  -- the centred square is the compiled winding
  have hsq : rectangleBoundaryIntegral f x₁ x₂ y₁ y₂ = 2 * Real.pi * I := by
    simp only [x₁, x₂, y₁, y₂, hf]
    exact rectangleBoundaryIntegral_inv_square hr
  rw [hsplit1, hsplit2, hsplit3, hsplit4, hleft, hright, hbot, htop, hsq]
  ring

/-- **The residue identity on general rectangles**: a simple-pole
decomposition of `Q` on a closed rectangle with `ρ` interior gives
`∮ Q·F = 2πi·res·F(ρ)` for entire `F`. -/
theorem rect_residue_of_simple_pole {Q g F : ℂ → ℂ} {ρ res : ℂ}
    {a b c d : ℝ}
    (hax : a < ρ.re) (hxb : ρ.re < b) (hcy : c < ρ.im) (hyd : ρ.im < d)
    (hg : DifferentiableOn ℂ g (Icc a b ×ℂ Icc c d))
    (hF : Differentiable ℂ F)
    (hdec : ∀ s ∈ (Icc a b ×ℂ Icc c d) \ {ρ},
      Q s = res * (s - ρ)⁻¹ + g s) :
    rectangleBoundaryIntegral (fun s => Q s * F s) a b c d
      = 2 * Real.pi * I * (res * F ρ) := by
  have hab : a ≤ b := by linarith
  have hcd : c ≤ d := by linarith
  set v : ℂ → ℂ := fun s => res * dslope F ρ s + g s * F s with hv
  have hvdiff : DifferentiableOn ℂ v (Icc a b ×ℂ Icc c d) := by
    apply DifferentiableOn.add
    · exact (((differentiable_dslope_of_entire hF ρ).const_mul res)).differentiableOn
    · exact hg.mul hF.differentiableOn
  have hvzero : rectangleBoundaryIntegral v a b c d = 0 :=
    rectangleBoundaryIntegral_eq_zero_of_differentiableOn v a b c d hab hcd hvdiff
  set u : ℂ → ℂ := fun s => (res * F ρ) * (s - ρ)⁻¹ with hu
  have huval : rectangleBoundaryIntegral u a b c d
      = (res * F ρ) * (2 * Real.pi * I) := by
    have hinv := rect_winding hax hxb hcy hyd
    unfold rectangleBoundaryIntegral at hinv ⊢
    simp only [hu]
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
    have halg : ∀ w x y z : ℂ, (res * F ρ) * w - (res * F ρ) * x
        + I * ((res * F ρ) * y) - I * ((res * F ρ) * z)
        = (res * F ρ) * (w - x + I * y - I * z) := by
      intro w x y z; ring
    rw [halg, hinv]
  have hmem_h : ∀ (y : ℝ) (x : ℝ), x ∈ [[a, b]] → (y = c ∨ y = d) →
      ((x : ℂ) + y * I) ∈ (Icc a b ×ℂ Icc c d) \ {ρ} := by
    intro y x hx hy
    rw [uIcc_of_le hab] at hx
    constructor
    · rw [Complex.mem_reProdIm]
      constructor
      · simpa using hx
      · rcases hy with h | h <;> subst h <;>
          · constructor <;> simp <;> linarith
    · simp only [Set.mem_singleton_iff]
      intro hcon
      have him := congrArg Complex.im hcon
      simp at him
      rcases hy with h | h <;> subst h <;> linarith
  have hmem_v : ∀ (x : ℝ) (y : ℝ), y ∈ [[c, d]] → (x = a ∨ x = b) →
      ((x : ℂ) + y * I) ∈ (Icc a b ×ℂ Icc c d) \ {ρ} := by
    intro x y hy hx
    rw [uIcc_of_le hcd] at hy
    constructor
    · rw [Complex.mem_reProdIm]
      constructor
      · rcases hx with h | h <;> subst h <;>
          · constructor <;> simp <;> linarith
      · simpa using hy
    · simp only [Set.mem_singleton_iff]
      intro hcon
      have hre := congrArg Complex.re hcon
      simp at hre
      rcases hx with h | h <;> subst h <;> linarith
  have hpt : ∀ s ∈ (Icc a b ×ℂ Icc c d) \ {ρ}, Q s * F s = u s + v s := by
    intro s hs
    have hsne : s ≠ ρ := hs.2
    rw [hdec s hs]
    show (res * (s - ρ)⁻¹ + g s) * F s
      = res * F ρ * (s - ρ)⁻¹ + (res * dslope F ρ s + g s * F s)
    rw [dslope_of_ne F hsne]
    simp only [slope_def_field]
    field_simp
    ring
  have hsplit : rectangleBoundaryIntegral (fun s => Q s * F s) a b c d
      = rectangleBoundaryIntegral u a b c d
        + rectangleBoundaryIntegral v a b c d := by
    unfold rectangleBoundaryIntegral
    have hcont_u : ∀ (y : ℝ), (y = c ∨ y = d) →
        IntervalIntegrable (fun x : ℝ => u ((x : ℂ) + y * I)) volume a b := by
      intro y hy
      apply ContinuousOn.intervalIntegrable
      apply ContinuousOn.mul continuousOn_const
      apply ContinuousOn.inv₀
      · fun_prop
      · intro x hx
        have := (hmem_h y x hx hy).2
        simp only [Set.mem_singleton_iff] at this
        exact sub_ne_zero.mpr this
    have hcont_v_h : ∀ (y : ℝ), (y = c ∨ y = d) →
        IntervalIntegrable (fun x : ℝ => v ((x : ℂ) + y * I)) volume a b := by
      intro y hy
      apply ContinuousOn.intervalIntegrable
      have hpar : ContinuousOn (fun x : ℝ => ((x : ℂ) + y * I)) [[a, b]] := by
        fun_prop
      apply ContinuousOn.add
      · exact (((differentiable_dslope_of_entire hF ρ).const_mul
          res).continuous.comp_continuousOn hpar)
      · apply ContinuousOn.mul
        · apply hg.continuousOn.comp hpar
          intro x hx
          exact (hmem_h y x hx hy).1
        · exact hF.continuous.comp_continuousOn hpar
    have hcont_u_v : ∀ (x : ℝ), (x = a ∨ x = b) →
        IntervalIntegrable (fun y : ℝ => u ((x : ℂ) + y * I)) volume c d := by
      intro x hx
      apply ContinuousOn.intervalIntegrable
      apply ContinuousOn.mul continuousOn_const
      apply ContinuousOn.inv₀
      · fun_prop
      · intro y hy
        have := (hmem_v x y hy hx).2
        simp only [Set.mem_singleton_iff] at this
        exact sub_ne_zero.mpr this
    have hcont_v_v : ∀ (x : ℝ), (x = a ∨ x = b) →
        IntervalIntegrable (fun y : ℝ => v ((x : ℂ) + y * I)) volume c d := by
      intro x hx
      apply ContinuousOn.intervalIntegrable
      have hpar : ContinuousOn (fun y : ℝ => ((x : ℂ) + y * I)) [[c, d]] := by
        fun_prop
      apply ContinuousOn.add
      · exact (((differentiable_dslope_of_entire hF ρ).const_mul
          res).continuous.comp_continuousOn hpar)
      · apply ContinuousOn.mul
        · apply hg.continuousOn.comp hpar
          intro y hy
          exact (hmem_v x y hy hx).1
        · exact hF.continuous.comp_continuousOn hpar
    have e1 : (∫ x in a..b, Q ((x : ℂ) + c * I) * F ((x : ℂ) + c * I))
        = (∫ x in a..b, u ((x : ℂ) + c * I))
          + ∫ x in a..b, v ((x : ℂ) + c * I) := by
      rw [← integral_add (hcont_u c (Or.inl rfl)) (hcont_v_h c (Or.inl rfl))]
      apply integral_congr
      intro x hx
      exact hpt _ (hmem_h c x hx (Or.inl rfl))
    have e2 : (∫ x in a..b, Q ((x : ℂ) + d * I) * F ((x : ℂ) + d * I))
        = (∫ x in a..b, u ((x : ℂ) + d * I))
          + ∫ x in a..b, v ((x : ℂ) + d * I) := by
      rw [← integral_add (hcont_u d (Or.inr rfl)) (hcont_v_h d (Or.inr rfl))]
      apply integral_congr
      intro x hx
      exact hpt _ (hmem_h d x hx (Or.inr rfl))
    have e3 : (∫ y in c..d, Q ((b : ℂ) + y * I) * F ((b : ℂ) + y * I))
        = (∫ y in c..d, u ((b : ℂ) + y * I))
          + ∫ y in c..d, v ((b : ℂ) + y * I) := by
      rw [← integral_add (hcont_u_v b (Or.inr rfl)) (hcont_v_v b (Or.inr rfl))]
      apply integral_congr
      intro y hy
      exact hpt _ (hmem_v b y hy (Or.inr rfl))
    have e4 : (∫ y in c..d, Q ((a : ℂ) + y * I) * F ((a : ℂ) + y * I))
        = (∫ y in c..d, u ((a : ℂ) + y * I))
          + ∫ y in c..d, v ((a : ℂ) + y * I) := by
      rw [← integral_add (hcont_u_v a (Or.inl rfl)) (hcont_v_v a (Or.inl rfl))]
      apply integral_congr
      intro y hy
      exact hpt _ (hmem_v a y hy (Or.inl rfl))
    rw [e1, e2, e3, e4]
    ring
  rw [hsplit, hvzero, huval]
  ring

/-! ## Part 2: the carry detects the pole -/

open CriticalLinePhasor.GlobalCarry

/-- The tilted Gaussian test at sharpness `M`. -/
noncomputable def gaussTest (M : ℝ) (ρ : ℂ) : ℂ → ℂ :=
  fun s => Complex.exp ((M : ℂ) * (s - ρ) ^ 2)

lemma gaussTest_norm (M : ℝ) (ρ s : ℂ) :
    ‖gaussTest M ρ s‖
      = Real.exp (M * ((s.re - ρ.re) ^ 2 - (s.im - ρ.im) ^ 2)) := by
  unfold gaussTest
  rw [Complex.norm_exp]
  congr 1
  have h1 : ((M : ℂ) * (s - ρ) ^ 2).re
      = M * ((s - ρ).re ^ 2 - (s - ρ).im ^ 2) := by
    simp only [Complex.mul_re, Complex.mul_im, pow_two, Complex.ofReal_re,
      Complex.ofReal_im]
    ring
  rw [h1]
  simp [Complex.sub_re, Complex.sub_im]

lemma gaussTest_at_center (M : ℝ) (ρ : ℂ) : gaussTest M ρ ρ = 1 := by
  unfold gaussTest
  simp

lemma gaussTest_entire (M : ℝ) (ρ : ℂ) : Differentiable ℂ (gaussTest M ρ) := by
  unfold gaussTest
  apply Complex.differentiable_exp.comp
  apply Differentiable.const_mul
  exact (differentiable_id.sub_const ρ).pow 2

lemma gaussTest_line_continuous (M : ℝ) (ρ : ℂ) (σ : ℝ) :
    Continuous fun t : ℝ => gaussTest M ρ ((σ : ℂ) + t * I) :=
  (gaussTest_entire M ρ).continuous.comp (by fun_prop)

set_option maxHeartbeats 1600000 in
/-- **Fuse #3, assembled: the carry detects a simple pole.**
If the carry datum decomposes with a simple pole at an interior point `ρ`
on a window box taller than the strip is wide, then some admissible test
sees it: `∃ F, carry D F ≠ 0`.  The test is the tilted Gaussian
`e^{M(s−ρ)²}` at explicit sharpness. -/
theorem carry_detects_simple_pole
    (D : CarryData) {ρ : ℂ} (hmp : D.σm < ρ.re) (hpp : ρ.re < D.σp)
    {res : ℂ} (hres : res ≠ 0) {g : ℂ → ℂ} {H B : ℝ} (hB : 0 ≤ B)
    (hw : max (D.σp - ρ.re) (ρ.re - D.σm) < H)
    (hdec : ∀ s ∈ (Icc D.σm D.σp ×ℂ Icc (ρ.im - H) (ρ.im + H)) \ {ρ},
      D.Q s = res * (s - ρ)⁻¹ + g s)
    (hg : DifferentiableOn ℂ g
      (Icc D.σm D.σp ×ℂ Icc (ρ.im - H) (ρ.im + H)))
    (hedge : ∀ x : ℝ, D.σm ≤ x → x ≤ D.σp → ∀ y : ℝ,
      (y = ρ.im - H ∨ y = ρ.im + H) → ‖D.Q ((x : ℂ) + y * I)‖ ≤ B) :
    ∃ F : ℂ → ℂ, carry D F ≠ 0 := by
  classical
  set w : ℝ := max (D.σp - ρ.re) (ρ.re - D.σm) with hw_def
  have hw0 : 0 < w :=
    lt_of_lt_of_le (by linarith) (le_max_left _ _)
  have hH0 : 0 < H := lt_trans hw0 hw
  have hβ : 0 < H ^ 2 - w ^ 2 := by nlinarith
  have hσ : D.σm < D.σp := lt_trans hmp hpp
  -- the tail integral of the exponential majorant
  set Itail : ℝ := ∫ t : ℝ, Real.exp (-D.δ * |t|) with hItail
  have hItail0 : 0 ≤ Itail := by
    rw [hItail]
    apply MeasureTheory.integral_nonneg
    intro t
    positivity
  -- error constant
  set K : ℝ := (2 * Real.pi)⁻¹ *
    ((D.σp - D.σm) * B * 2 + D.C * Itail * 2) with hK
  have hK0 : 0 ≤ K := by
    rw [hK]
    have h1 : 0 ≤ (D.σp - D.σm) := by linarith
    have h2 := D.hC
    positivity
  -- choose the sharpness M
  obtain ⟨M, hM0, hMsmall⟩ :
      ∃ M : ℝ, 0 ≤ M ∧ K * Real.exp (M * (w ^ 2 - H ^ 2)) < ‖res‖ := by
    by_cases hKz : K ≤ 0
    · refine ⟨0, le_refl 0, ?_⟩
      have : K * Real.exp (0 * (w ^ 2 - H ^ 2)) ≤ 0 := by
        simp only [zero_mul, Real.exp_zero, mul_one]
        exact hKz
      have hr : 0 < ‖res‖ := norm_pos_iff.mpr hres
      linarith
    · push_neg at hKz
      set M : ℝ := max 0 (Real.log (K / (‖res‖ / 2)) / (H ^ 2 - w ^ 2)) with hM
      refine ⟨M, le_max_left _ _, ?_⟩
      have hr : 0 < ‖res‖ := norm_pos_iff.mpr hres
      have hq : 0 < K / (‖res‖ / 2) := by positivity
      have hMge : Real.log (K / (‖res‖ / 2)) / (H ^ 2 - w ^ 2) ≤ M :=
        le_max_right _ _
      have hexp : Real.exp (M * (w ^ 2 - H ^ 2))
          ≤ Real.exp (-(Real.log (K / (‖res‖ / 2)))) := by
        apply Real.exp_le_exp.mpr
        have hneg : M * (w ^ 2 - H ^ 2) = -(M * (H ^ 2 - w ^ 2)) := by ring
        rw [hneg]
        apply neg_le_neg
        calc Real.log (K / (‖res‖ / 2))
            = (Real.log (K / (‖res‖ / 2)) / (H ^ 2 - w ^ 2)) * (H ^ 2 - w ^ 2) := by
              field_simp
          _ ≤ M * (H ^ 2 - w ^ 2) := by
              apply mul_le_mul_of_nonneg_right hMge (le_of_lt hβ)
      have hval : Real.exp (-(Real.log (K / (‖res‖ / 2))))
          = (‖res‖ / 2) / K := by
        rw [Real.exp_neg, Real.exp_log hq]
        field_simp
      calc K * Real.exp (M * (w ^ 2 - H ^ 2))
          ≤ K * ((‖res‖ / 2) / K) := by
            apply mul_le_mul_of_nonneg_left _ (le_of_lt hKz)
            rw [← hval]
            exact hexp
        _ = ‖res‖ / 2 := by field_simp
        _ < ‖res‖ := by linarith
  -- the chosen test
  refine ⟨gaussTest M ρ, ?_⟩
  set F : ℂ → ℂ := gaussTest M ρ with hF
  -- line bound for pairing integrability: constant exp(M·w²)
  have hlineb : ∀ σ : ℝ, (σ = D.σp ∨ σ = D.σm) →
      ∀ t : ℝ, ‖F ((σ : ℂ) + t * I)‖ ≤ Real.exp (M * w ^ 2) := by
    intro σ hσ' t
    rw [hF, gaussTest_norm]
    apply Real.exp_le_exp.mpr
    have hre : ((σ : ℂ) + t * I).re = σ := by simp
    have him : ((σ : ℂ) + t * I).im = t := by simp
    rw [hre, him]
    have h1 : (σ - ρ.re) ^ 2 ≤ w ^ 2 := by
      rcases hσ' with h | h <;> subst h
      · have : D.σp - ρ.re ≤ w := le_max_left _ _
        nlinarith
      · have : ρ.re - D.σm ≤ w := le_max_right _ _
        nlinarith
    nlinarith [sq_nonneg (t - ρ.im), hM0]
  have hLB : ∀ σ : ℝ, (σ = D.σp ∨ σ = D.σm) →
      LineBound F σ (Real.exp (M * w ^ 2)) 0 := by
    intro σ hσ' t
    calc ‖F ((σ : ℂ) + t * I)‖
        ≤ Real.exp (M * w ^ 2) := hlineb σ hσ' t
      _ = Real.exp (M * w ^ 2) * Real.exp (0 * |t|) := by simp
  have hintp : Integrable fun t : ℝ =>
      D.Q ((D.σp : ℂ) + t * I) * F ((D.σp : ℂ) + t * I) :=
    carry_integrable_of_bounds D (Or.inl rfl)
      (hLB D.σp (Or.inl rfl)) (Real.exp_pos _).le
      D.hδ (gaussTest_line_continuous M ρ D.σp)
  have hintm : Integrable fun t : ℝ =>
      D.Q ((D.σm : ℂ) + t * I) * F ((D.σm : ℂ) + t * I) :=
    carry_integrable_of_bounds D (Or.inr rfl)
      (hLB D.σm (Or.inr rfl)) (Real.exp_pos _).le
      D.hδ (gaussTest_line_continuous M ρ D.σm)
  -- window and edge coordinates
  set cc : ℝ := ρ.im - H with hcc
  set dd : ℝ := ρ.im + H with hdd
  have hccdd : cc ≤ dd := by rw [hcc, hdd]; linarith
  set S : Set ℝ := Set.Ioc cc dd with hS
  have hSmeas : MeasurableSet S := measurableSet_Ioc
  -- the four correction pieces
  set QF : ℂ → ℂ := fun s => D.Q s * F s with hQF
  set bot : ℂ := ∫ x in D.σm..D.σp, QF ((x : ℂ) + cc * I) with hbot
  set top : ℂ := ∫ x in D.σm..D.σp, QF ((x : ℂ) + dd * I) with htop
  set tailp : ℂ := ∫ t in Sᶜ, D.Q ((D.σp : ℂ) + t * I) * F ((D.σp : ℂ) + t * I)
    with htailp
  set tailm : ℂ := ∫ t in Sᶜ, D.Q ((D.σm : ℂ) + t * I) * F ((D.σm : ℂ) + t * I)
    with htailm
  -- the residue value of the window rectangle
  have hrect : rectangleBoundaryIntegral QF D.σm D.σp cc dd
      = 2 * Real.pi * I * (res * F ρ) := by
    apply rect_residue_of_simple_pole hmp hpp
      (by rw [hcc]; linarith) (by rw [hdd]; linarith) hg (gaussTest_entire M ρ)
    exact hdec
  rw [hF, gaussTest_at_center, mul_one] at hrect
  -- the line splits: full line = window + tail
  have hsplitp : (∫ t : ℝ, D.Q ((D.σp : ℂ) + t * I) * F ((D.σp : ℂ) + t * I))
      = (∫ t in cc..dd, D.Q ((D.σp : ℂ) + t * I) * F ((D.σp : ℂ) + t * I))
        + tailp := by
    rw [htailp, intervalIntegral.integral_of_le hccdd, ← hS]
    exact (integral_add_compl hSmeas hintp).symm
  have hsplitm : (∫ t : ℝ, D.Q ((D.σm : ℂ) + t * I) * F ((D.σm : ℂ) + t * I))
      = (∫ t in cc..dd, D.Q ((D.σm : ℂ) + t * I) * F ((D.σm : ℂ) + t * I))
        + tailm := by
    rw [htailm, intervalIntegral.integral_of_le hccdd, ← hS]
    exact (integral_add_compl hSmeas hintm).symm
  -- the rectangle in terms of the window pieces
  have hrectdef : rectangleBoundaryIntegral QF D.σm D.σp cc dd
      = bot - top
        + I * (∫ t in cc..dd, D.Q ((D.σp : ℂ) + t * I) * F ((D.σp : ℂ) + t * I))
        - I * (∫ t in cc..dd, D.Q ((D.σm : ℂ) + t * I) * F ((D.σm : ℂ) + t * I)) := by
    rw [hbot, htop]
    rfl
  -- assemble: carry = res + (2π)⁻¹·E
  set E : ℂ := I * bot - I * top + tailp - tailm with hE
  have hassemble : carry D F = res + ((2 * Real.pi : ℝ) : ℂ)⁻¹ * E := by
    unfold carry
    rw [hsplitp, hsplitm]
    have hwin : (∫ t in cc..dd, D.Q ((D.σp : ℂ) + t * I) * F ((D.σp : ℂ) + t * I))
        - (∫ t in cc..dd, D.Q ((D.σm : ℂ) + t * I) * F ((D.σm : ℂ) + t * I))
        = -I * (rectangleBoundaryIntegral QF D.σm D.σp cc dd - bot + top) := by
      rw [hrectdef]
      have hI : I * I = -1 := Complex.I_mul_I
      linear_combination (∫ t in cc..dd, D.Q ((D.σp : ℂ) + t * I)
        * F ((D.σp : ℂ) + t * I)) * hI - (∫ t in cc..dd,
        D.Q ((D.σm : ℂ) + t * I) * F ((D.σm : ℂ) + t * I)) * hI
    have hπ : ((2 * Real.pi : ℝ) : ℂ) ≠ 0 := by
      push_cast
      simp [Real.pi_ne_zero]
    have hres2 : -I * (2 * Real.pi * I * res) = ((2 * Real.pi : ℝ) : ℂ) * res := by
      have hI : I * I = -1 := Complex.I_mul_I
      push_cast
      linear_combination (-2 * (Real.pi : ℂ) * res) * hI
    rw [Complex.ofReal_inv]
    calc ((2 * Real.pi : ℝ) : ℂ)⁻¹
          * (((∫ t in cc..dd, D.Q ((D.σp : ℂ) + t * I) * F ((D.σp : ℂ) + t * I))
              + tailp)
            - ((∫ t in cc..dd, D.Q ((D.σm : ℂ) + t * I) * F ((D.σm : ℂ) + t * I))
              + tailm))
        = ((2 * Real.pi : ℝ) : ℂ)⁻¹
          * (-I * (rectangleBoundaryIntegral QF D.σm D.σp cc dd - bot + top)
            + tailp - tailm) := by
          rw [← hwin]; ring
      _ = ((2 * Real.pi : ℝ) : ℂ)⁻¹
          * (((2 * Real.pi : ℝ) : ℂ) * res + E) := by
          rw [hrect, hE]
          rw [← hres2]
          ring
      _ = res + ((2 * Real.pi : ℝ) : ℂ)⁻¹ * E := by
          field_simp
  -- the error bound: every piece carries exp(M(w² − H²))
  set X : ℝ := Real.exp (M * (w ^ 2 - H ^ 2)) with hX
  have hX0 : 0 < X := Real.exp_pos _
  -- edge bound for the Gaussian
  have hFedge : ∀ x : ℝ, D.σm ≤ x → x ≤ D.σp → ∀ y : ℝ,
      (y = cc ∨ y = dd) → ‖F ((x : ℂ) + y * I)‖ ≤ X := by
    intro x hx1 hx2 y hy
    rw [hF, gaussTest_norm, hX]
    apply Real.exp_le_exp.mpr
    have hre : ((x : ℂ) + y * I).re = x := by simp
    have him : ((x : ℂ) + y * I).im = y := by simp
    rw [hre, him]
    have h1 : (x - ρ.re) ^ 2 ≤ w ^ 2 := by
      have ha : x - ρ.re ≤ D.σp - ρ.re := by linarith
      have hb : ρ.re - x ≤ ρ.re - D.σm := by linarith
      have hc : D.σp - ρ.re ≤ w := le_max_left _ _
      have hd : ρ.re - D.σm ≤ w := le_max_right _ _
      nlinarith
    have h2 : (y - ρ.im) ^ 2 = H ^ 2 := by
      rcases hy with h | h <;> subst h <;>
        · simp only [hcc, hdd]; ring
    rw [h2]
    nlinarith
  have hedgeQF : ∀ (y : ℝ), (y = cc ∨ y = dd) →
      ‖(∫ x in D.σm..D.σp, QF ((x : ℂ) + y * I))‖
        ≤ B * X * |D.σp - D.σm| := by
    intro y hy
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro x hx
    rw [Set.uIoc_of_le (le_of_lt hσ)] at hx
    have hx1 : D.σm ≤ x := le_of_lt hx.1
    have hx2 : x ≤ D.σp := hx.2
    rw [hQF]
    calc ‖D.Q ((x : ℂ) + y * I) * F ((x : ℂ) + y * I)‖
        = ‖D.Q ((x : ℂ) + y * I)‖ * ‖F ((x : ℂ) + y * I)‖ := norm_mul _ _
      _ ≤ B * X := by
          apply mul_le_mul (hedge x hx1 hx2 y (by
            rcases hy with h | h <;> subst h
            · exact Or.inl (by rw [hcc])
            · exact Or.inr (by rw [hdd])))
            (hFedge x hx1 hx2 y hy) (norm_nonneg _) hB
  -- tail bound: on Sᶜ the Gaussian is ≤ X and Q decays
  have htailbound : ∀ (σ : ℝ), (σ = D.σp ∨ σ = D.σm) →
      ∀ (hint : Integrable fun t : ℝ =>
        D.Q ((σ : ℂ) + t * I) * F ((σ : ℂ) + t * I)),
      ‖(∫ t in Sᶜ, D.Q ((σ : ℂ) + t * I) * F ((σ : ℂ) + t * I))‖
        ≤ D.C * X * Itail := by
    intro σ hσ' hint
    have hQb : ∀ t : ℝ, ‖D.Q ((σ : ℂ) + t * I)‖ ≤ D.C * Real.exp (-D.δ * |t|) := by
      rcases hσ' with h | h <;> subst h
      · exact D.boundp
      · exact D.boundm
    have hFtail : ∀ t : ℝ, t ∈ Sᶜ → ‖F ((σ : ℂ) + t * I)‖ ≤ X := by
      intro t ht
      rw [hF, gaussTest_norm, hX]
      apply Real.exp_le_exp.mpr
      have hre : ((σ : ℂ) + t * I).re = σ := by simp
      have him : ((σ : ℂ) + t * I).im = t := by simp
      rw [hre, him]
      have h1 : (σ - ρ.re) ^ 2 ≤ w ^ 2 := by
        rcases hσ' with h | h <;> subst h
        · have : D.σp - ρ.re ≤ w := le_max_left _ _
          nlinarith
        · have : ρ.re - D.σm ≤ w := le_max_right _ _
          nlinarith
      have h2 : H ^ 2 ≤ (t - ρ.im) ^ 2 := by
        rw [hS] at ht
        simp only [Set.mem_compl_iff, Set.mem_Ioc, not_and_or, not_lt, not_le] at ht
        rcases ht with h | h
        · have : t ≤ ρ.im - H := by rw [← hcc]; exact h
          nlinarith
        · have : ρ.im + H < t := by rw [← hdd]; exact h
          nlinarith
      have h3 : (σ - ρ.re) ^ 2 - (t - ρ.im) ^ 2 ≤ w ^ 2 - H ^ 2 := by linarith
      exact mul_le_mul_of_nonneg_left h3 hM0
    calc ‖(∫ t in Sᶜ, D.Q ((σ : ℂ) + t * I) * F ((σ : ℂ) + t * I))‖
        ≤ ∫ t in Sᶜ, ‖D.Q ((σ : ℂ) + t * I) * F ((σ : ℂ) + t * I)‖ :=
          norm_integral_le_integral_norm _
      _ ≤ ∫ t in Sᶜ, (D.C * X) * Real.exp (-D.δ * |t|) := by
          apply setIntegral_mono_on
          · exact hint.norm.integrableOn
          · exact (((integrable_exp_neg_mul_abs D.hδ).const_mul
              (D.C * X))).integrableOn
          · exact hSmeas.compl
          · intro t ht
            rw [norm_mul]
            calc ‖D.Q ((σ : ℂ) + t * I)‖ * ‖F ((σ : ℂ) + t * I)‖
                ≤ (D.C * Real.exp (-D.δ * |t|)) * X := by
                  apply mul_le_mul (hQb t) (hFtail t ht) (norm_nonneg _)
                  exact mul_nonneg D.hC (Real.exp_pos _).le
              _ = (D.C * X) * Real.exp (-D.δ * |t|) := by ring
      _ ≤ ∫ t : ℝ, (D.C * X) * Real.exp (-D.δ * |t|) := by
          apply setIntegral_le_integral
            ((integrable_exp_neg_mul_abs D.hδ).const_mul (D.C * X))
          apply Filter.Eventually.of_forall
          intro t
          have h2 := D.hC
          positivity
      _ = D.C * X * Itail := by
          rw [MeasureTheory.integral_const_mul, hItail]
  -- total error
  have hEbound : ‖((2 * Real.pi : ℝ) : ℂ)⁻¹ * E‖ ≤ K * X := by
    have hnormE : ‖E‖ ≤ (D.σp - D.σm) * B * X * 2 + D.C * Itail * X * 2 := by
      rw [hE]
      have h1 := hedgeQF cc (Or.inl rfl)
      have h2 := hedgeQF dd (Or.inr rfl)
      have h3 := htailbound D.σp (Or.inl rfl) hintp
      have h4 := htailbound D.σm (Or.inr rfl) hintm
      have habs : |D.σp - D.σm| = D.σp - D.σm := abs_of_pos (by linarith)
      rw [habs] at h1 h2
      calc ‖I * bot - I * top + tailp - tailm‖
          ≤ ‖I * bot - I * top + tailp‖ + ‖tailm‖ := norm_sub_le _ _
        _ ≤ ‖I * bot - I * top‖ + ‖tailp‖ + ‖tailm‖ := by
            have := norm_add_le (I * bot - I * top) tailp
            linarith
        _ ≤ ‖I * bot‖ + ‖I * top‖ + ‖tailp‖ + ‖tailm‖ := by
            have := norm_sub_le (I * bot) (I * top)
            linarith
        _ = ‖bot‖ + ‖top‖ + ‖tailp‖ + ‖tailm‖ := by
            rw [norm_mul, norm_mul, Complex.norm_I, one_mul, one_mul]
        _ ≤ (B * X * (D.σp - D.σm)) + (B * X * (D.σp - D.σm))
            + (D.C * X * Itail) + (D.C * X * Itail) := by
            rw [hbot, htop, htailp, htailm] at *
            linarith [h1, h2, h3, h4]
        _ = (D.σp - D.σm) * B * X * 2 + D.C * Itail * X * 2 := by ring
    have hπnorm : ‖((2 * Real.pi : ℝ) : ℂ)⁻¹‖ = (2 * Real.pi)⁻¹ := by
      rw [norm_inv, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (by positivity)]
    calc ‖((2 * Real.pi : ℝ) : ℂ)⁻¹ * E‖
        = (2 * Real.pi)⁻¹ * ‖E‖ := by rw [norm_mul, hπnorm]
      _ ≤ (2 * Real.pi)⁻¹ * ((D.σp - D.σm) * B * X * 2 + D.C * Itail * X * 2) := by
          apply mul_le_mul_of_nonneg_left hnormE
          positivity
      _ = K * X := by rw [hK]; ring
  -- conclude
  intro hzero
  rw [hassemble] at hzero
  have hres_eq : res = -(((2 * Real.pi : ℝ) : ℂ)⁻¹ * E) := by
    linear_combination hzero
  have : ‖res‖ ≤ K * X := by
    rw [hres_eq, norm_neg]
    exact hEbound
  rw [hX] at this
  linarith [hMsmall]

end CriticalLinePhasor.CarryDetection

#print axioms CriticalLinePhasor.CarryDetection.rect_winding
#print axioms CriticalLinePhasor.CarryDetection.rect_residue_of_simple_pole
#print axioms CriticalLinePhasor.CarryDetection.carry_detects_simple_pole
