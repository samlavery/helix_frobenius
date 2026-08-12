import RequestProject.ArgumentPrincipleRectangle

/-!
# Fuse #3, the heart: the square residue identity

The local detection step of the three-fuse program (registered 2026-08-10):
`zeroCarry_implies_noPoles` reduces to showing that a simple pole inside a
square forces a nonzero boundary integral against a test factor.  This file
compiles that heart on the repo's existing rectangle machinery — as
predicted, with no new conceptual input:

* `differentiable_dslope_of_entire` — the difference quotient of an entire
  function is entire (power-series shift at the centre, direct formula off
  it);
* `square_residue_of_simple_pole` — **the identity**: if on a closed square
  centred at `ρ` the function decomposes as
  `Q = res·(s−ρ)⁻¹ + g` with `g` analytic on the square, then for entire
  `F` the boundary integral is exactly
  `∮ Q·F = 2πi·res·F(ρ)`.
  Proof: boundary congruence to
  `res·F(ρ)·(s−ρ)⁻¹ + (res·dslope F ρ + g·F)`, the first term by the
  repo's compiled winding (`rectangleBoundaryIntegral_inv_square`), the
  second by Cauchy–Goursat (`rectangleBoundaryIntegral_eq_zero_of_
  differentiableOn`).

The remaining assembly of fuse #3 — choosing the tilted-Gaussian-times-
polynomial test and passing to the `M → ∞` limit against the CarryData
bounds so that `carry ≠ 0` — is estimates on objects compiled here and in
`GlobalCarry`; the pole geometry needs nothing beyond discreteness.  No
`axiom`, no `sorry`.
-/

open Complex Set MeasureTheory intervalIntegral
open scoped Interval Real

namespace CriticalLinePhasor.RectResidue

open CriticalLinePhasor.ContourArgument

/-- The difference quotient of an entire function is entire. -/
theorem differentiable_dslope_of_entire {F : ℂ → ℂ} (hF : Differentiable ℂ F)
    (ρ : ℂ) : Differentiable ℂ (dslope F ρ) := by
  intro b
  by_cases hb : b = ρ
  · subst hb
    obtain ⟨p, hp⟩ := (hF.analyticAt b)
    exact (hp.has_fpower_series_dslope_fslope).analyticAt.differentiableAt
  · have hev : dslope F ρ =ᶠ[nhds b] fun s => (s - ρ)⁻¹ * (F s - F ρ) := by
      filter_upwards [IsOpen.mem_nhds (isOpen_compl_singleton) hb] with s hs
      rw [dslope_of_ne F hs]
      simp [slope_def_field]
      ring
    rw [Filter.EventuallyEq.differentiableAt_iff hev]
    exact DifferentiableAt.mul
      (((differentiableAt_id.sub_const ρ).inv (sub_ne_zero.mpr hb)))
      ((hF b).sub_const (F ρ))

/-- **The square residue identity** — the heart of fuse #3.  A simple-pole
decomposition on a closed square centred at `ρ` forces
`∮ Q·F = 2πi·res·F(ρ)` for every entire test factor `F`. -/
theorem square_residue_of_simple_pole {Q g F : ℂ → ℂ} {ρ res : ℂ} {L : ℝ}
    (hL : 0 < L)
    (hg : DifferentiableOn ℂ g
      (Icc (ρ.re - L) (ρ.re + L) ×ℂ Icc (ρ.im - L) (ρ.im + L)))
    (hF : Differentiable ℂ F)
    (hdec : ∀ s ∈ (Icc (ρ.re - L) (ρ.re + L) ×ℂ Icc (ρ.im - L) (ρ.im + L)) \ {ρ},
      Q s = res * (s - ρ)⁻¹ + g s) :
    rectangleBoundaryIntegral (fun s => Q s * F s)
      (ρ.re - L) (ρ.re + L) (ρ.im - L) (ρ.im + L)
      = 2 * Real.pi * I * (res * F ρ) := by
  set a : ℝ := ρ.re - L
  set b : ℝ := ρ.re + L
  set c : ℝ := ρ.im - L
  set d : ℝ := ρ.im + L
  have hab : a ≤ b := by simp only [a, b]; linarith
  have hcd : c ≤ d := by simp only [c, d]; linarith
  -- the analytic part
  set v : ℂ → ℂ := fun s => res * dslope F ρ s + g s * F s with hv
  have hvdiff : DifferentiableOn ℂ v (Icc a b ×ℂ Icc c d) := by
    apply DifferentiableOn.add
    · exact (((differentiable_dslope_of_entire hF ρ).const_mul res)).differentiableOn
    · exact hg.mul hF.differentiableOn
  have hvzero : rectangleBoundaryIntegral v a b c d = 0 :=
    rectangleBoundaryIntegral_eq_zero_of_differentiableOn v a b c d hab hcd hvdiff
  -- the singular part, by the compiled winding
  set u : ℂ → ℂ := fun s => (res * F ρ) * (s - ρ)⁻¹ with hu
  have huval : rectangleBoundaryIntegral u a b c d
      = (res * F ρ) * (2 * Real.pi * I) := by
    have hinv := rectangleBoundaryIntegral_inv_square (ρ := ρ) hL
    unfold rectangleBoundaryIntegral at hinv ⊢
    simp only [hu]
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
    have : ∀ w x y z : ℂ, (res * F ρ) * w - (res * F ρ) * x
        + I * ((res * F ρ) * y) - I * ((res * F ρ) * z)
        = (res * F ρ) * (w - x + I * y - I * z) := by
      intro w x y z; ring
    rw [this]
    rw [hinv]
  -- membership and non-centrality of boundary points
  have hmem_h : ∀ (y : ℝ) (x : ℝ), x ∈ [[a, b]] → (y = c ∨ y = d) →
      ((x : ℂ) + y * I) ∈
        (Icc a b ×ℂ Icc c d) \ {ρ} := by
    intro y x hx hy
    rw [uIcc_of_le hab] at hx
    constructor
    · constructor
      · simpa using hx
      · rcases hy with h | h <;> subst h
        · simp only [c, d]
          constructor <;> simp <;> linarith
        · simp only [c, d]
          constructor <;> simp <;> linarith
    · simp only [Set.mem_singleton_iff]
      intro hcon
      have him := congrArg Complex.im hcon
      simp at him
      rcases hy with h | h <;> subst h <;> simp only [c, d] at him <;> linarith
  have hmem_v : ∀ (x : ℝ) (y : ℝ), y ∈ [[c, d]] → (x = a ∨ x = b) →
      ((x : ℂ) + y * I) ∈
        (Icc a b ×ℂ Icc c d) \ {ρ} := by
    intro x y hy hx
    rw [uIcc_of_le hcd] at hy
    constructor
    · constructor
      · rcases hx with h | h <;> subst h
        · simp only [a, b]
          constructor <;> simp <;> linarith
        · simp only [a, b]
          constructor <;> simp <;> linarith
      · simpa using hy
    · simp only [Set.mem_singleton_iff]
      intro hcon
      have hre := congrArg Complex.re hcon
      simp at hre
      rcases hx with h | h <;> subst h <;> simp only [a, b] at hre <;> linarith
  -- pointwise boundary identity: Q·F = u + v off the centre, inside the square
  have hpt : ∀ s ∈ (Icc a b ×ℂ Icc c d) \ {ρ},
      Q s * F s = u s + v s := by
    intro s hs
    have hsne : s ≠ ρ := hs.2
    rw [hdec s hs]
    show (res * (s - ρ)⁻¹ + g s) * F s
      = res * F ρ * (s - ρ)⁻¹ + (res * dslope F ρ s + g s * F s)
    rw [dslope_of_ne F hsne]
    simp only [slope_def_field]
    field_simp
    ring
  -- assemble: rewrite each of the four boundary integrals
  have hsplit : rectangleBoundaryIntegral (fun s => Q s * F s) a b c d
      = rectangleBoundaryIntegral u a b c d
        + rectangleBoundaryIntegral v a b c d := by
    unfold rectangleBoundaryIntegral
    -- integrability of u and v on each segment
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
    -- rewrite the four integrals of Q·F as integrals of u + v
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

end CriticalLinePhasor.RectResidue

#print axioms CriticalLinePhasor.RectResidue.differentiable_dslope_of_entire
#print axioms CriticalLinePhasor.RectResidue.square_residue_of_simple_pole
