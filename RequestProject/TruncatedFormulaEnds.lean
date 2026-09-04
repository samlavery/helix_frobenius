import Mathlib
import RequestProject.SelbergTruncatedFormula

/-!
# The END terms of the truncated explicit formula, extracted as residues (ledger 565)

The Archimedean factor `E = weilArch` of `ξ′/ξ` splits into the TWO ENDS
`E₀(s) = 1/s + 1/(s−1) − ½ log π` and the CLOCK `Ψ(s) = ½ Γ′/Γ(s/2)`. Against a kernel
`K(s) = G(s−s₀)/(s−s₀)` (`G` entire, `G(0) = 1`, decay ≥ 1 on the strip) the ends integrate by
residues: the poles of `E₀` at `s = 1` and `s = 0` inside the strip give the END terms `K(1)` and
`K(0)` — i.e. `K(1 − s₀)` and `K(−s₀)` in the kernel variable — the two ends of the double-ended
helix read at the front. The clock stays as a named line integral: its residues are the trivial
zeros, and their extraction needs the digamma partial fraction, absent from Mathlib (ledger 527).

Main results, for both compiled kernels (cubic B-spline, Selberg's linear taper):
  `ξ′/ξ(s₀) + Σ′_ρ m_ρ K(ρ−s₀) = E₀(s₀) + K(1−s₀) + K(−s₀) + (1/2π)[Ψ-lines] − Σ_n W(log n)Λ(n)n^{−s₀}`
and the classical form (Re s₀ > 0, ζ(s₀) ≠ 0):
  `Σ_n W(log n)Λ(n)n^{−s₀} = −ζ′/ζ(s₀) + K(1−s₀) + K(−s₀) − Σ′_ρ m_ρ K(ρ−s₀) + [(1/2π)Ψ-lines − Ψ(s₀)]`.

No `sorry`, no `axiom`.
-/

open Complex Set MeasureTheory Filter Topology
open scoped Interval Real FourierTransform

noncomputable section

namespace CriticalLinePhasor.ContourArgument

/-! ## 1. Ends and clock -/

/-- The two ends of the Archimedean factor: `E₀(s) = 1/s + 1/(s−1) − ½ log π`. -/
def weilEnds (s : ℂ) : ℂ := 1 / s + 1 / (s - 1) - ((Real.log Real.pi : ℝ) : ℂ) / 2

/-- The Archimedean clock: `Ψ(s) = ½ Γ′/Γ(s/2)`. -/
def weilClock (s : ℂ) : ℂ := logDeriv Complex.Gamma (s / 2) / 2

theorem weilArch_eq (s : ℂ) : weilArch s = weilEnds s + weilClock s := by
  unfold weilArch weilEnds weilClock
  ring

/-- The ends are odd up to the constant: `E₀(s) + E₀(1−s) = −log π`. -/
theorem weilEnds_add_reflect {s : ℂ} (h0 : s ≠ 0) (h1 : s ≠ 1) :
    weilEnds s + weilEnds (1 - s) = -((Real.log Real.pi : ℝ) : ℂ) := by
  unfold weilEnds
  have h1' : s - 1 ≠ 0 := sub_ne_zero.mpr h1
  have h2 : (1 : ℂ) - s ≠ 0 := sub_ne_zero.mpr (Ne.symm h1)
  have h3 : (1 : ℂ) - s - 1 ≠ 0 := by
    intro h; apply h0; linear_combination -h
  field_simp
  ring

theorem weilEnds_line_continuous {σ : ℝ} (h0 : σ ≠ 0) (h1 : σ ≠ 1) :
    Continuous (fun t : ℝ => weilEnds ((σ : ℂ) + t * I)) := by
  unfold weilEnds
  have hne0 : ∀ t : ℝ, (σ : ℂ) + t * I ≠ 0 := by
    intro t h
    have := congrArg Complex.re h
    simp at this
    exact h0 this
  have hne1 : ∀ t : ℝ, (σ : ℂ) + t * I - 1 ≠ 0 := by
    intro t h
    have := congrArg Complex.re h
    simp at this
    exact h1 (by linarith)
  refine (Continuous.add (Continuous.div continuous_const (by fun_prop) hne0)
    (Continuous.div continuous_const (by fun_prop) hne1)).sub continuous_const

theorem weilEnds_line_bound {σ : ℝ} (h0 : σ ≠ 0) (h1 : σ ≠ 1) (t : ℝ) :
    ‖weilEnds ((σ : ℂ) + t * I)‖ ≤ 1 / |σ| + 1 / |σ - 1| + |Real.log Real.pi| / 2 := by
  unfold weilEnds
  have hre0 : |((σ : ℂ) + t * I).re| ≤ ‖(σ : ℂ) + t * I‖ := Complex.abs_re_le_norm _
  have hre1 : |((σ : ℂ) + t * I - 1).re| ≤ ‖(σ : ℂ) + t * I - 1‖ := Complex.abs_re_le_norm _
  have e0 : ((σ : ℂ) + t * I).re = σ := by simp
  have e1 : ((σ : ℂ) + t * I - 1).re = σ - 1 := by simp
  rw [e0] at hre0
  rw [e1] at hre1
  have hσ0 : 0 < |σ| := abs_pos.mpr h0
  have hσ1 : 0 < |σ - 1| := abs_pos.mpr (sub_ne_zero.mpr h1)
  have hn0 : 0 < ‖(σ : ℂ) + t * I‖ := lt_of_lt_of_le hσ0 hre0
  have hn1 : 0 < ‖(σ : ℂ) + t * I - 1‖ := lt_of_lt_of_le hσ1 hre1
  calc ‖1 / ((σ : ℂ) + t * I) + 1 / ((σ : ℂ) + t * I - 1) - ((Real.log Real.pi : ℝ) : ℂ) / 2‖
      ≤ ‖1 / ((σ : ℂ) + t * I) + 1 / ((σ : ℂ) + t * I - 1)‖
          + ‖((Real.log Real.pi : ℝ) : ℂ) / 2‖ := norm_sub_le _ _
    _ ≤ ‖1 / ((σ : ℂ) + t * I)‖ + ‖1 / ((σ : ℂ) + t * I - 1)‖
          + ‖((Real.log Real.pi : ℝ) : ℂ) / 2‖ := by gcongr; exact norm_add_le _ _
    _ = 1 / ‖(σ : ℂ) + t * I‖ + 1 / ‖(σ : ℂ) + t * I - 1‖ + |Real.log Real.pi| / 2 := by
        have h2 : ‖((Real.log Real.pi : ℝ) : ℂ) / 2‖ = |Real.log Real.pi| / 2 := by
          rw [norm_div, Complex.norm_real, Real.norm_eq_abs]
          norm_num
        rw [norm_div, norm_div, norm_one, h2]
    _ ≤ 1 / |σ| + 1 / |σ - 1| + |Real.log Real.pi| / 2 := by
        gcongr

/-! ## 2. The two ends as residues -/

/-- **The two ends as residues.** For `K(s) = G(s−s₀)/(s−s₀)` with `G` entire, `G(0) = 1`, decay
order `≥ 1` on the strip, and `a < 0 < 1 < b`, `a < Re s₀ < b`, `s₀ ∉ {0, 1}`:
`∮_strip K·E₀ = 2πi [E₀(s₀) + K(0) + K(1)]`. -/
theorem stripBoundary_kernel_mul_ends {G : ℂ → ℂ} (hG : Differentiable ℂ G) (hG0 : G 0 = 1)
    {s₀ : ℂ} {a b C : ℝ} (hC : 0 ≤ C) (ha : a < 0) (hb : 1 < b)
    (hdec : ∀ x ∈ Icc a b, ∀ T : ℝ, ‖G (x + T * I - s₀)‖ ≤ C / (1 + |T|) ^ 1)
    (hs₀a : a < s₀.re) (hs₀b : s₀.re < b) (h0 : s₀ ≠ 0) (h1 : s₀ ≠ 1) :
    stripBoundary (fun s => G (s - s₀) / (s - s₀) * weilEnds s) a b
      = 2 * Real.pi * I * (weilEnds s₀ + G (0 - s₀) / (0 - s₀) + G (1 - s₀) / (1 - s₀)) := by
  have hab : a ≤ b := by linarith
  set F : ℂ → ℂ := fun s => G (s - s₀) with hFdef
  have hFd : Differentiable ℂ F := hG.comp (differentiable_id.sub_const s₀)
  have hdecF : ∀ x ∈ Icc a b, ∀ T : ℝ, ‖F (x + T * I)‖ ≤ C / (1 + |T|) ^ 1 := hdec
  have r₀ : stripBoundary (fun s => F s * (s - s₀)⁻¹) a b = 2 * Real.pi * I * F s₀ :=
    stripBoundary_div_sub_eq₁ hFd hC hab hdecF hs₀a hs₀b
  have rz : stripBoundary (fun s => F s * (s - 0)⁻¹) a b = 2 * Real.pi * I * F 0 :=
    stripBoundary_div_sub_eq₁ hFd hC hab hdecF (by simp; exact ha) (by simp; linarith)
  have ro : stripBoundary (fun s => F s * (s - 1)⁻¹) a b = 2 * Real.pi * I * F 1 :=
    stripBoundary_div_sub_eq₁ hFd hC hab hdecF (by simp; linarith) (by simp; exact hb)
  set c : ℂ := ((Real.log Real.pi : ℝ) : ℂ) / 2 with hc
  have hs1 : s₀ - 1 ≠ 0 := sub_ne_zero.mpr h1
  have hpt : ∀ σ : ℝ, (σ = a ∨ σ = b) → ∀ t : ℝ,
      G ((σ : ℂ) + t * I - s₀) / ((σ : ℂ) + t * I - s₀) * weilEnds ((σ : ℂ) + t * I)
        = (1 / s₀) * (F ((σ : ℂ) + t * I) * (((σ : ℂ) + t * I) - s₀)⁻¹
              - F ((σ : ℂ) + t * I) * (((σ : ℂ) + t * I) - 0)⁻¹)
          + (1 / (s₀ - 1)) * (F ((σ : ℂ) + t * I) * (((σ : ℂ) + t * I) - s₀)⁻¹
              - F ((σ : ℂ) + t * I) * (((σ : ℂ) + t * I) - 1)⁻¹)
          - c * (F ((σ : ℂ) + t * I) * (((σ : ℂ) + t * I) - s₀)⁻¹) := by
    intro σ hσ t
    have hne1 : (σ : ℂ) + t * I - s₀ ≠ 0 := by
      intro h
      have := congrArg Complex.re h
      simp at this
      rcases hσ with rfl | rfl <;> linarith
    have hne0 : (σ : ℂ) + t * I ≠ 0 := by
      intro h
      have := congrArg Complex.re h
      simp at this
      rcases hσ with rfl | rfl <;> linarith
    have hne2 : (σ : ℂ) + t * I - 1 ≠ 0 := by
      intro h
      have := congrArg Complex.re h
      simp at this
      rcases hσ with rfl | rfl <;> linarith
    simp only [weilEnds, hFdef, sub_zero, hc]
    field_simp
    ring
  have hσab : ∀ σ : ℝ, (σ = a ∨ σ = b) → σ ∈ Icc a b := by
    intro σ hσ
    rcases hσ with rfl | rfl
    · exact ⟨le_refl _, hab⟩
    · exact ⟨hab, le_refl _⟩
  have hint : ∀ σ : ℝ, (σ = a ∨ σ = b) → ∀ p : ℂ, (p = s₀ ∨ p = 0 ∨ p = 1) →
      Integrable (fun t : ℝ => F (σ + t * I) * ((σ : ℂ) + t * I - p)⁻¹) := by
    intro σ hσ p hp
    have hdecσ : LineDecay F σ C 1 := fun t => hdecF σ (hσab σ hσ) t
    have hpre : a < p.re ∧ p.re < b := by
      rcases hp with rfl | rfl | rfl
      · exact ⟨hs₀a, hs₀b⟩
      · simp; exact ⟨ha, by linarith⟩
      · simp; exact ⟨by linarith, hb⟩
    have hp' : σ ≠ p.re := by
      rcases hσ with rfl | rfl <;> linarith [hpre.1, hpre.2]
    exact integrable_line_mul_inv_sub₁ (hFd.continuous.comp (by fun_prop)) hC hdecσ hp'
  have I₀a := hint a (Or.inl rfl) s₀ (Or.inl rfl)
  have I₀b := hint b (Or.inr rfl) s₀ (Or.inl rfl)
  have Iza := hint a (Or.inl rfl) 0 (Or.inr (Or.inl rfl))
  have Izb := hint b (Or.inr rfl) 0 (Or.inr (Or.inl rfl))
  have Ioa := hint a (Or.inl rfl) 1 (Or.inr (Or.inr rfl))
  have Iob := hint b (Or.inr rfl) 1 (Or.inr (Or.inr rfl))
  have e1 := stripBoundary_sub (F := fun s => F s * (s - s₀)⁻¹) (G := fun s => F s * (s - 0)⁻¹)
    I₀a I₀b Iza Izb
  have e2 := stripBoundary_sub (F := fun s => F s * (s - s₀)⁻¹) (G := fun s => F s * (s - 1)⁻¹)
    I₀a I₀b Ioa Iob
  have e3 := stripBoundary_add
    (F := fun s => (1 / s₀) * (F s * (s - s₀)⁻¹ - F s * (s - 0)⁻¹))
    (G := fun s => (1 / (s₀ - 1)) * (F s * (s - s₀)⁻¹ - F s * (s - 1)⁻¹))
    ((I₀a.sub Iza).const_mul _) ((I₀b.sub Izb).const_mul _)
    ((I₀a.sub Ioa).const_mul _) ((I₀b.sub Iob).const_mul _)
  have e4 := stripBoundary_sub
    (F := fun s => (1 / s₀) * (F s * (s - s₀)⁻¹ - F s * (s - 0)⁻¹)
      + (1 / (s₀ - 1)) * (F s * (s - s₀)⁻¹ - F s * (s - 1)⁻¹))
    (G := fun s => c * (F s * (s - s₀)⁻¹))
    (((I₀a.sub Iza).const_mul _).add ((I₀a.sub Ioa).const_mul _))
    (((I₀b.sub Izb).const_mul _).add ((I₀b.sub Iob).const_mul _))
    (I₀a.const_mul _) (I₀b.const_mul _)
  rw [stripBoundary_congr (G := fun s => (1 / s₀) * (F s * (s - s₀)⁻¹ - F s * (s - 0)⁻¹)
      + (1 / (s₀ - 1)) * (F s * (s - s₀)⁻¹ - F s * (s - 1)⁻¹) - c * (F s * (s - s₀)⁻¹)) hpt,
    e4, e3, stripBoundary_const_mul, stripBoundary_const_mul, stripBoundary_const_mul, e1, e2,
    r₀, rz, ro]
  have hF0 : F s₀ = 1 := by
    show G (s₀ - s₀) = 1
    rw [sub_self, hG0]
  have hFz : F 0 = G (0 - s₀) := rfl
  have hFo : F 1 = G (1 - s₀) := rfl
  rw [hF0, hFz, hFo]
  unfold weilEnds
  have hz : (0 : ℂ) - s₀ ≠ 0 := by rw [zero_sub]; exact neg_ne_zero.mpr h0
  have ho : (1 : ℂ) - s₀ ≠ 0 := sub_ne_zero.mpr (Ne.symm h1)
  rw [hc]
  field_simp
  ring

/-! ## 3. The Archimedean lines with the ends extracted -/

/-- **The Archimedean lines, ends extracted.** With `K(s) = G(s−s₀)/(s−s₀)` as above, continuous
with decay 2 on the two lines, `K·E` integrable on them, and the left line integral of `K`
vanishing (the reflected profile has no mass at `0`):
`∫ K(b+it)E(b+it)dt + ∫ K(a+it)E(1−a−it)dt = 2π[E₀(s₀) + K(0) + K(1)] + [the same with Ψ]`. -/
theorem archLines_ends {G : ℂ → ℂ} (hG : Differentiable ℂ G) (hG0 : G 0 = 1) {s₀ : ℂ}
    {a b C C' : ℝ} (hC : 0 ≤ C) (hC' : 0 ≤ C') (ha : a < 0) (hb : 1 < b)
    (hdec : ∀ x ∈ Icc a b, ∀ T : ℝ, ‖G (x + T * I - s₀)‖ ≤ C / (1 + |T|) ^ 1)
    (hs₀a : a < s₀.re) (hs₀b : s₀.re < b) (h0 : s₀ ≠ 0) (h1 : s₀ ≠ 1)
    (K : ℂ → ℂ) (hK : ∀ s, K s = G (s - s₀) / (s - s₀))
    (hKc : ∀ σ : ℝ, (σ = a ∨ σ = b) → Continuous (fun t : ℝ => K ((σ : ℂ) + t * I)))
    (hKdec : ∀ σ : ℝ, (σ = a ∨ σ = b) → LineDecay K σ C' 2)
    (hAb : Integrable (fun t : ℝ => K ((b : ℂ) + t * I) * weilArch ((b : ℂ) + t * I)))
    (hAa : Integrable (fun t : ℝ => K ((a : ℂ) + t * I) * weilArch (1 - ((a : ℂ) + t * I))))
    (hleft : ∫ t : ℝ, K ((a : ℂ) + t * I) = 0) :
    (∫ t : ℝ, K ((b : ℂ) + t * I) * weilArch ((b : ℂ) + t * I))
      + (∫ t : ℝ, K ((a : ℂ) + t * I) * weilArch (1 - ((a : ℂ) + t * I)))
    = 2 * π * (weilEnds s₀ + K 0 + K 1)
      + ((∫ t : ℝ, K ((b : ℂ) + t * I) * weilClock ((b : ℂ) + t * I))
        + (∫ t : ℝ, K ((a : ℂ) + t * I) * weilClock (1 - ((a : ℂ) + t * I)))) := by
  have hab : a ≤ b := by linarith
  -- the strip residue for `K·E₀`
  have hres := stripBoundary_kernel_mul_ends hG hG0 hC ha hb hdec hs₀a hs₀b h0 h1
  have hKfun : (fun s => G (s - s₀) / (s - s₀) * weilEnds s) = fun s => K s * weilEnds s := by
    funext s; rw [hK]
  rw [hKfun] at hres
  have hK0 : G (0 - s₀) / (0 - s₀) = K 0 := (hK 0).symm
  have hK1 : G (1 - s₀) / (1 - s₀) = K 1 := (hK 1).symm
  rw [hK0, hK1] at hres
  unfold stripBoundary lineIntegral at hres
  beta_reduce at hres
  -- integrability of `K` and `K·E₀` on the lines
  have hKint : ∀ σ : ℝ, (σ = a ∨ σ = b) → Integrable (fun t : ℝ => K ((σ : ℂ) + t * I)) :=
    fun σ hσ => integrable_line_of_decay' (hKc σ hσ) (le_refl 2) hC' (hKdec σ hσ)
  have hE₀int : ∀ σ : ℝ, (σ = a ∨ σ = b) →
      Integrable (fun t : ℝ => K ((σ : ℂ) + t * I) * weilEnds ((σ : ℂ) + t * I)) := by
    intro σ hσ
    have h0' : σ ≠ 0 := by rcases hσ with rfl | rfl <;> linarith
    have h1' : σ ≠ 1 := by rcases hσ with rfl | rfl <;> linarith
    exact (hKint σ hσ).mul_bdd (weilEnds_line_continuous h0' h1').aestronglyMeasurable
      (Eventually.of_forall (weilEnds_line_bound h0' h1'))
  have hE₀refl : Integrable (fun t : ℝ => K ((a : ℂ) + t * I) * weilEnds (1 - ((a : ℂ) + t * I))) := by
    have h0' : (1 - a) ≠ 0 := by linarith
    have h1' : (1 - a) ≠ 1 := by linarith
    have hcont : Continuous (fun t : ℝ => weilEnds (1 - ((a : ℂ) + t * I))) := by
      have := weilEnds_line_continuous (σ := 1 - a) h0' h1'
      have hcomp : (fun t : ℝ => weilEnds (1 - ((a : ℂ) + t * I)))
          = fun t : ℝ => weilEnds (((1 - a : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * I) := by
        funext t; congr 1; push_cast; ring
      rw [hcomp]
      exact this.comp continuous_neg
    refine (hKint a (Or.inl rfl)).mul_bdd hcont.aestronglyMeasurable
      (c := 1 / |1 - a| + 1 / |1 - a - 1| + |Real.log Real.pi| / 2)
      (Eventually.of_forall fun t => ?_)
    have := weilEnds_line_bound (σ := 1 - a) h0' h1' (-t)
    have hcomp : (1 - ((a : ℂ) + t * I)) = (((1 - a : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * I) := by
      push_cast; ring
    rw [hcomp]
    exact this
  -- split `E = E₀ + Ψ` on both lines
  have hsplitb : ∫ t : ℝ, K ((b : ℂ) + t * I) * weilArch ((b : ℂ) + t * I)
      = (∫ t : ℝ, K ((b : ℂ) + t * I) * weilEnds ((b : ℂ) + t * I))
        + ∫ t : ℝ, K ((b : ℂ) + t * I) * weilClock ((b : ℂ) + t * I) := by
    have hΨ : Integrable (fun t : ℝ => K ((b : ℂ) + t * I) * weilClock ((b : ℂ) + t * I)) := by
      refine (hAb.sub (hE₀int b (Or.inr rfl))).congr (Eventually.of_forall fun t => ?_)
      simp only [Pi.sub_apply]
      rw [weilArch_eq]; ring
    rw [← integral_add (hE₀int b (Or.inr rfl)) hΨ]
    congr 1; funext t; rw [weilArch_eq]; ring
  have hsplita : ∫ t : ℝ, K ((a : ℂ) + t * I) * weilArch (1 - ((a : ℂ) + t * I))
      = (∫ t : ℝ, K ((a : ℂ) + t * I) * weilEnds (1 - ((a : ℂ) + t * I)))
        + ∫ t : ℝ, K ((a : ℂ) + t * I) * weilClock (1 - ((a : ℂ) + t * I)) := by
    have hΨ : Integrable (fun t : ℝ => K ((a : ℂ) + t * I) * weilClock (1 - ((a : ℂ) + t * I))) := by
      refine (hAa.sub hE₀refl).congr (Eventually.of_forall fun t => ?_)
      simp only [Pi.sub_apply]
      rw [weilArch_eq]; ring
    rw [← integral_add hE₀refl hΨ]
    congr 1; funext t; rw [weilArch_eq]; ring
  -- the reflected ends on the left line: `E₀(1−s) = −log π − E₀(s)`
  have hrefl : ∫ t : ℝ, K ((a : ℂ) + t * I) * weilEnds (1 - ((a : ℂ) + t * I))
      = -((Real.log Real.pi : ℝ) : ℂ) * (∫ t : ℝ, K ((a : ℂ) + t * I))
        - ∫ t : ℝ, K ((a : ℂ) + t * I) * weilEnds ((a : ℂ) + t * I) := by
    rw [← integral_const_mul, ← integral_sub ((hKint a (Or.inl rfl)).const_mul _)
      (hE₀int a (Or.inl rfl))]
    congr 1
    funext t
    have h0' : (a : ℂ) + t * I ≠ 0 := by
      intro h; have := congrArg Complex.re h; simp at this; linarith
    have h1' : (a : ℂ) + t * I ≠ 1 := by
      intro h; have := congrArg Complex.re h; simp at this; linarith
    have := weilEnds_add_reflect h0' h1'
    linear_combination K ((a : ℂ) + t * I) * this
  rw [hsplitb, hsplita, hrefl, hleft]
  -- `hres : I * ∫_b K E₀ − I * ∫_a K E₀ = 2πi (E₀(s₀) + K 0 + K 1)`
  linear_combination (-I) * hres
    + ((∫ t : ℝ, K ((b : ℂ) + t * I) * weilEnds ((b : ℂ) + t * I))
      - (∫ t : ℝ, K ((a : ℂ) + t * I) * weilEnds ((a : ℂ) + t * I))
      - 2 * π * (weilEnds s₀ + K 0 + K 1)) * Complex.I_sq

/-! ## 4. The instances: the left line integral of each kernel vanishes -/

theorem cubicKernel_left_line_integral {L : ℝ} (hL : 0 < L) {s₀ : ℂ} {a : ℝ} (ha : a < s₀.re)
    {C : ℝ} (hC : 0 ≤ C) (hdec : LineDecay (fun s => cubicKernel L (s - s₀)) a C 4) :
    ∫ t : ℝ, cubicKernel L ((a : ℂ) + t * I - s₀) = 0 := by
  set w₀ : ℂ := (a : ℂ) - s₀ with hw₀
  have hw₀re : w₀.re < 0 := by rw [hw₀]; simp; linarith
  set φ : ℝ → ℂ := fun v => (cubicProfileLeft L v : ℂ) * Complex.exp (w₀ * v) with hφ
  have hφc : Continuous φ := by
    rw [hφ]
    exact (Complex.continuous_ofReal.comp (cubicProfileLeft_continuous L)).mul (by fun_prop)
  have hφi : Integrable φ := cubicProfileLeft_mul_exp_integrable hw₀re
  set Φ : ℝ → ℂ := fun t => cubicKernel L ((a : ℂ) + t * I - s₀) with hΦdef
  have hΦ : ∀ t : ℝ, Φ t = ∫ v : ℝ, φ v * Complex.exp (I * t * v) := by
    intro t
    rw [hΦdef]
    have hw : ((a : ℂ) + t * I - s₀).re < 0 := by simp; linarith
    show cubicKernel L ((a : ℂ) + t * I - s₀) = _
    rw [cubicKernel_eq_laplace_left hL hw]
    congr 1
    funext v
    rw [hφ]
    show (cubicProfileLeft L v : ℂ) * Complex.exp (((a : ℂ) + t * I - s₀) * v)
      = (cubicProfileLeft L v : ℂ) * Complex.exp (w₀ * v) * Complex.exp (I * t * v)
    rw [mul_assoc, ← Complex.exp_add]
    congr 1
    congr 1
    rw [hw₀]
    ring
  have hΦi : Integrable Φ :=
    integrable_line_of_decay' (F := fun s => cubicKernel L (s - s₀))
      (cubicKernel_line_continuous L (by linarith : a ≠ s₀.re)) (by norm_num) hC hdec
  have h := line_transform_inversion hφc hφi hΦ hΦi 0
  simp only [Complex.ofReal_zero, mul_zero, neg_zero, Complex.exp_zero, mul_one] at h
  rw [hΦdef] at h
  rw [h, hφ]
  simp only [cubicProfileLeft_eq_zero hL hL.le, Complex.ofReal_zero, zero_mul, mul_zero]

theorem linKernel_left_line_integral {L : ℝ} (hL : 0 < L) {s₀ : ℂ} {a : ℝ} (ha : a < s₀.re)
    {C : ℝ} (hC : 0 ≤ C) (hdec : LineDecay (fun s => linKernel L (s - s₀)) a C 2) :
    ∫ t : ℝ, linKernel L ((a : ℂ) + t * I - s₀) = 0 := by
  set w₀ : ℂ := (a : ℂ) - s₀ with hw₀
  have hw₀re : w₀.re < 0 := by rw [hw₀]; simp; linarith
  set φ : ℝ → ℂ := fun v => (linProfileLeft L v : ℂ) * Complex.exp (w₀ * v) with hφ
  have hφc : Continuous φ := by
    rw [hφ]
    exact (Complex.continuous_ofReal.comp (linProfileLeft_continuous L)).mul (by fun_prop)
  have hφi : Integrable φ := linProfileLeft_mul_exp_integrable hw₀re
  set Φ : ℝ → ℂ := fun t => linKernel L ((a : ℂ) + t * I - s₀) with hΦdef
  have hΦ : ∀ t : ℝ, Φ t = ∫ v : ℝ, φ v * Complex.exp (I * t * v) := by
    intro t
    rw [hΦdef]
    have hw : ((a : ℂ) + t * I - s₀).re < 0 := by simp; linarith
    show linKernel L ((a : ℂ) + t * I - s₀) = _
    rw [linKernel_eq_laplace_left hL hw]
    congr 1
    funext v
    rw [hφ]
    show (linProfileLeft L v : ℂ) * Complex.exp (((a : ℂ) + t * I - s₀) * v)
      = (linProfileLeft L v : ℂ) * Complex.exp (w₀ * v) * Complex.exp (I * t * v)
    rw [mul_assoc, ← Complex.exp_add]
    congr 1
    congr 1
    rw [hw₀]
    ring
  have hΦi : Integrable Φ :=
    integrable_line_of_decay' (F := fun s => linKernel L (s - s₀))
      (linKernel_line_continuous L (by linarith : a ≠ s₀.re)) (le_refl 2) hC hdec
  have h := line_transform_inversion hφc hφi hΦ hΦi 0
  simp only [Complex.ofReal_zero, mul_zero, neg_zero, Complex.exp_zero, mul_one] at h
  rw [hΦdef] at h
  rw [h, hφ]
  simp only [linProfileLeft_eq_zero hL hL.le, Complex.ofReal_zero, zero_mul, mul_zero]

/-- Decay of order `k ≥ 1` implies decay of order `1` with the same constant. -/
theorem strip_decay_one_of {G : ℂ → ℂ} {s₀ : ℂ} {a b C : ℝ} {k : ℕ} (hk : 1 ≤ k) (hC : 0 ≤ C)
    (hdec : ∀ x ∈ Icc a b, ∀ T : ℝ, ‖G (x + T * I - s₀)‖ ≤ C / (1 + |T|) ^ k) :
    ∀ x ∈ Icc a b, ∀ T : ℝ, ‖G (x + T * I - s₀)‖ ≤ C / (1 + |T|) ^ 1 := by
  intro x hx T
  refine le_trans (hdec x hx T) ?_
  apply div_le_div_of_nonneg_left hC (by positivity)
  exact pow_le_pow_right₀ (by linarith [abs_nonneg T]) hk

/-! ## 5. The truncated formulas with the ends extracted -/

/-- **Cubic taper, ends extracted.** -/
theorem truncated_explicit_formula_cubic_ends {L : ℝ} (hL : 0 < L) {s₀ : ℂ}
    (hs₀ : s₀ ∉ ZD.NontrivialZeros) (h0 : s₀ ≠ 0) (h1 : s₀ ≠ 1) {a b : ℝ} (ha : a < 0) (hb : 1 < b)
    (hs₀a : a < s₀.re) (hs₀b : s₀.re < b) :
    logDeriv ZD.riemannXi s₀ + ∑' ρ : Zero, (ZD.xiOrderNat ρ.val : ℂ) * cubicKernel L (ρ.val - s₀)
      = (weilEnds s₀ + cubicKernel L (1 - s₀) + cubicKernel L (-s₀))
        + (1 / (2 * π)) * ((∫ t : ℝ, cubicKernel L ((b : ℂ) + t * I - s₀) * weilClock ((b : ℂ) + t * I))
          + (∫ t : ℝ, cubicKernel L ((a : ℂ) + t * I - s₀) * weilClock (1 - ((a : ℂ) + t * I))))
        - ∑' n : ℕ, (cubicProfile L (Real.log n) : ℂ) * LSeries.term vonMangoldtC s₀ n := by
  have hab : a ≤ b := by linarith
  have hmain := truncated_explicit_formula_cubic hL hs₀ ha hb hs₀a hs₀b
  obtain ⟨C, hC, hdecl⟩ := cubicKernel_line_decay hL hab hs₀a hs₀b
  obtain ⟨C₀, hC₀, hdecG⟩ := cubicG_strip_decay hL hab hs₀b
  set K : ℂ → ℂ := fun s => cubicKernel L (s - s₀) with hKdef
  have hK : ∀ s, K s = cubicG L (s - s₀) / (s - s₀) := fun s => rfl
  have hKc : ∀ σ : ℝ, (σ = a ∨ σ = b) → Continuous (fun t : ℝ => K ((σ : ℂ) + t * I)) := by
    intro σ hσ
    apply cubicKernel_line_continuous
    rcases hσ with rfl | rfl <;> linarith
  have hKdec : ∀ σ : ℝ, (σ = a ∨ σ = b) → LineDecay K σ C 2 := by
    intro σ hσ t
    refine le_trans (hdecl σ hσ t) ?_
    apply div_le_div_of_nonneg_left hC (by positivity)
    exact pow_le_pow_right₀ (by linarith [abs_nonneg t]) (by norm_num)
  have hKint : ∀ σ : ℝ, (σ = a ∨ σ = b) → Integrable (fun t : ℝ => K ((σ : ℂ) + t * I)) :=
    fun σ hσ => integrable_line_of_decay' (hKc σ hσ) (le_refl 2) hC (hKdec σ hσ)
  -- `K·E` integrable on the two lines (as in the assembly)
  have hθb : Continuous (fun t : ℝ => (b : ℂ) + t * I) := by fun_prop
  have hreb : ∀ t : ℝ, ((b : ℂ) + t * I).re = b := by intro t; simp
  have hAb : Integrable (fun t : ℝ => K ((b : ℂ) + t * I) * weilArch ((b : ℂ) + t * I)) := by
    have hLint : Integrable (fun t : ℝ => K ((b : ℂ) + t * I) * LSeries vonMangoldtC (b + t * I)) :=
      lseries_line_integrable (hKint b (Or.inr rfl)) hθb hreb hb
    have h := (line_mul_logDeriv_xi_integrable' (F := K) (le_refl 4) hC ha hb (Or.inr rfl)
      (hKc b (Or.inr rfl)) (hdecl b (Or.inr rfl))).add hLint
    refine h.congr (Eventually.of_forall (fun t => ?_))
    simp only [Pi.add_apply]
    rw [logDeriv_xi_eq_arch_sub_lseries (by rw [hreb]; exact hb)]
    ring
  have hθa : Continuous (fun t : ℝ => 1 - ((a : ℂ) + t * I)) := by fun_prop
  have hrea : ∀ t : ℝ, (1 - ((a : ℂ) + t * I)).re = 1 - a := by intro t; simp
  have h1a : 1 < 1 - a := by linarith
  have hAa : Integrable (fun t : ℝ => K ((a : ℂ) + t * I) * weilArch (1 - ((a : ℂ) + t * I))) := by
    have hLint : Integrable (fun t : ℝ =>
        K ((a : ℂ) + t * I) * LSeries vonMangoldtC (1 - ((a : ℂ) + t * I))) :=
      lseries_line_integrable (hKint a (Or.inl rfl)) hθa hrea h1a
    have h := hLint.sub (line_mul_logDeriv_xi_integrable' (F := K) (le_refl 4) hC ha hb
      (Or.inl rfl) (hKc a (Or.inl rfl)) (hdecl a (Or.inl rfl)))
    refine h.congr (Eventually.of_forall (fun t => ?_))
    simp only [Pi.sub_apply]
    rw [logDeriv_xi_reflect, logDeriv_xi_eq_arch_sub_lseries (by rw [hrea]; exact h1a)]
    ring
  have hleft : ∫ t : ℝ, K ((a : ℂ) + t * I) = 0 :=
    cubicKernel_left_line_integral hL hs₀a hC (hdecl a (Or.inl rfl))
  have hends := archLines_ends (cubicG_differentiable L) (cubicG_zero hL.ne') hC₀ hC ha hb
    (strip_decay_one_of (by norm_num) hC₀ hdecG) hs₀a hs₀b h0 h1 K hK hKc hKdec hAb hAa hleft
  have hK0 : K 0 = cubicKernel L (-s₀) := by rw [hKdef]; simp
  have hK1 : K 1 = cubicKernel L (1 - s₀) := rfl
  rw [hK0, hK1] at hends
  simp only [hKdef] at hends
  rw [hmain, hends]
  have h2π : (1 / (2 * (π : ℂ))) * (2 * π) = 1 := by
    have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    field_simp
  linear_combination (weilEnds s₀ + cubicKernel L (-s₀) + cubicKernel L (1 - s₀)) * h2π

/-- **Selberg taper, ends extracted.** -/
theorem truncated_explicit_formula_selberg_ends {L : ℝ} (hL : 0 < L) {s₀ : ℂ}
    (hs₀ : s₀ ∉ ZD.NontrivialZeros) (h0 : s₀ ≠ 0) (h1 : s₀ ≠ 1) {a b : ℝ} (ha : a < 0) (hb : 1 < b)
    (hs₀a : a < s₀.re) (hs₀b : s₀.re < b) :
    logDeriv ZD.riemannXi s₀ + ∑' ρ : Zero, (ZD.xiOrderNat ρ.val : ℂ) * linKernel L (ρ.val - s₀)
      = (weilEnds s₀ + linKernel L (1 - s₀) + linKernel L (-s₀))
        + (1 / (2 * π)) * ((∫ t : ℝ, linKernel L ((b : ℂ) + t * I - s₀) * weilClock ((b : ℂ) + t * I))
          + (∫ t : ℝ, linKernel L ((a : ℂ) + t * I - s₀) * weilClock (1 - ((a : ℂ) + t * I))))
        - ∑' n : ℕ, (linProfile L (Real.log n) : ℂ) * LSeries.term vonMangoldtC s₀ n := by
  have hab : a ≤ b := by linarith
  have hmain := truncated_explicit_formula_selberg hL hs₀ ha hb hs₀a hs₀b
  obtain ⟨C, hC, hdecl⟩ := linKernel_line_decay hL hab hs₀a hs₀b
  obtain ⟨C₀, hC₀, hdecG⟩ := linG_strip_decay hL hab hs₀b
  set K : ℂ → ℂ := fun s => linKernel L (s - s₀) with hKdef
  have hK : ∀ s, K s = linG L (s - s₀) / (s - s₀) := fun s => rfl
  have hKc : ∀ σ : ℝ, (σ = a ∨ σ = b) → Continuous (fun t : ℝ => K ((σ : ℂ) + t * I)) := by
    intro σ hσ
    apply linKernel_line_continuous
    rcases hσ with rfl | rfl <;> linarith
  have hKint : ∀ σ : ℝ, (σ = a ∨ σ = b) → Integrable (fun t : ℝ => K ((σ : ℂ) + t * I)) :=
    fun σ hσ => integrable_line_of_decay' (hKc σ hσ) (le_refl 2) hC (hdecl σ hσ)
  -- `K·ξ′/ξ` integrable on the lines (kernel decay 2)
  have hlineInt : ∀ σ : ℝ, (σ = a ∨ σ = b) →
      Integrable (fun t : ℝ => K ((σ : ℂ) + t * I) * logDeriv ZD.riemannXi (σ + t * I)) := by
    intro σ hσ
    obtain ⟨A, hA⟩ := ZD.xi_logDeriv_partial_fraction
    have hpt : ∀ t : ℝ, K ((σ : ℂ) + t * I) * logDeriv ZD.riemannXi (σ + t * I)
        = A * K ((σ : ℂ) + t * I) + ∑' ρ : Zero, hadamardLineTerm K σ ρ t := by
      intro t
      rw [logDeriv_apply, hA _ (line_not_zero ha hb hσ t)]
      unfold hadamardLineTerm hadamardTerm
      rw [mul_add, ← tsum_mul_left]
      congr 1
      ring
    have hfun : (fun t : ℝ => K ((σ : ℂ) + t * I) * logDeriv ZD.riemannXi (σ + t * I))
        = fun t : ℝ => A * K ((σ : ℂ) + t * I) + ∑' ρ : Zero, hadamardLineTerm K σ ρ t :=
      funext hpt
    rw [hfun]
    exact ((hKint σ hσ).const_mul A).add (integrable_tsum_of_summable_integral_norm
      (fun ρ => lin_hadamardLineTerm_integrable hC ha hb hσ (hKc σ hσ) (hdecl σ hσ) ρ)
      (lin_summable_hadamardLineTerm_integral_norm hC ha hb hσ (hdecl σ hσ)))
  have hθb : Continuous (fun t : ℝ => (b : ℂ) + t * I) := by fun_prop
  have hreb : ∀ t : ℝ, ((b : ℂ) + t * I).re = b := by intro t; simp
  have hAb : Integrable (fun t : ℝ => K ((b : ℂ) + t * I) * weilArch ((b : ℂ) + t * I)) := by
    have hLint : Integrable (fun t : ℝ => K ((b : ℂ) + t * I) * LSeries vonMangoldtC (b + t * I)) :=
      lseries_line_integrable (hKint b (Or.inr rfl)) hθb hreb hb
    have h := (hlineInt b (Or.inr rfl)).add hLint
    refine h.congr (Eventually.of_forall (fun t => ?_))
    simp only [Pi.add_apply]
    rw [logDeriv_xi_eq_arch_sub_lseries (by rw [hreb]; exact hb)]
    ring
  have hθa : Continuous (fun t : ℝ => 1 - ((a : ℂ) + t * I)) := by fun_prop
  have hrea : ∀ t : ℝ, (1 - ((a : ℂ) + t * I)).re = 1 - a := by intro t; simp
  have h1a : 1 < 1 - a := by linarith
  have hAa : Integrable (fun t : ℝ => K ((a : ℂ) + t * I) * weilArch (1 - ((a : ℂ) + t * I))) := by
    have hLint : Integrable (fun t : ℝ =>
        K ((a : ℂ) + t * I) * LSeries vonMangoldtC (1 - ((a : ℂ) + t * I))) :=
      lseries_line_integrable (hKint a (Or.inl rfl)) hθa hrea h1a
    have h := hLint.sub (hlineInt a (Or.inl rfl))
    refine h.congr (Eventually.of_forall (fun t => ?_))
    simp only [Pi.sub_apply]
    rw [logDeriv_xi_reflect, logDeriv_xi_eq_arch_sub_lseries (by rw [hrea]; exact h1a)]
    ring
  have hleft : ∫ t : ℝ, K ((a : ℂ) + t * I) = 0 :=
    linKernel_left_line_integral hL hs₀a hC (hdecl a (Or.inl rfl))
  have hends := archLines_ends (linG_differentiable L) (linG_zero hL.ne') hC₀ hC ha hb
    hdecG hs₀a hs₀b h0 h1 K hK hKc hdecl hAb hAa hleft
  have hK0 : K 0 = linKernel L (-s₀) := by rw [hKdef]; simp
  have hK1 : K 1 = linKernel L (1 - s₀) := rfl
  rw [hK0, hK1] at hends
  simp only [hKdef] at hends
  rw [hmain, hends]
  have h2π : (1 / (2 * (π : ℂ))) * (2 * π) = 1 := by
    have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    field_simp
  linear_combination (weilEnds s₀ + linKernel L (-s₀) + linKernel L (1 - s₀)) * h2π

/-! ## 6. The classical form -/

/-- **Selberg's identity in classical form** (Titchmarsh 14.20 with the trivial-zero sum left as
the clock remainder): for `Re s₀ > 0`, `s₀ ≠ 1`, `ζ(s₀) ≠ 0`, `s₀` off the zero set, `a < 0 < 1 < b`,
`a < Re s₀ < b`:
`Σ_n Λ_x(n)Λ(n)n^{−s₀} = −ζ′/ζ(s₀) + K₁(1−s₀) + K₁(−s₀) − Σ′_ρ m_ρ K₁(ρ−s₀) + [(1/2π)Ψ-lines − Ψ(s₀)]`. -/
theorem selberg_identity_classical {L : ℝ} (hL : 0 < L) {s₀ : ℂ}
    (hs₀ : s₀ ∉ ZD.NontrivialZeros) (hre : 0 < s₀.re) (h1 : s₀ ≠ 1) (hz : riemannZeta s₀ ≠ 0)
    {a b : ℝ} (ha : a < 0) (hb : 1 < b) (hs₀a : a < s₀.re) (hs₀b : s₀.re < b) :
    ∑' n : ℕ, (linProfile L (Real.log n) : ℂ) * LSeries.term vonMangoldtC s₀ n
      = -logDeriv riemannZeta s₀ + linKernel L (1 - s₀) + linKernel L (-s₀)
        - ∑' ρ : Zero, (ZD.xiOrderNat ρ.val : ℂ) * linKernel L (ρ.val - s₀)
        + ((1 / (2 * π)) * ((∫ t : ℝ, linKernel L ((b : ℂ) + t * I - s₀) * weilClock ((b : ℂ) + t * I))
            + (∫ t : ℝ, linKernel L ((a : ℂ) + t * I - s₀) * weilClock (1 - ((a : ℂ) + t * I))))
          - weilClock s₀) := by
  have h0 : s₀ ≠ 0 := by
    intro h; rw [h] at hre; simp at hre
  have hends := truncated_explicit_formula_selberg_ends hL hs₀ h0 h1 ha hb hs₀a hs₀b
  have hsplice := CriticalLinePhasor.SeatingLedger.logDeriv_riemannXi_splice hre h1 hz
  have hξ : logDeriv ZD.riemannXi s₀ = weilEnds s₀ + weilClock s₀ + logDeriv riemannZeta s₀ := by
    rw [hsplice]; unfold weilEnds weilClock; ring
  rw [hξ] at hends
  linear_combination hends

/-- The same for the cubic taper. -/
theorem cubic_identity_classical {L : ℝ} (hL : 0 < L) {s₀ : ℂ}
    (hs₀ : s₀ ∉ ZD.NontrivialZeros) (hre : 0 < s₀.re) (h1 : s₀ ≠ 1) (hz : riemannZeta s₀ ≠ 0)
    {a b : ℝ} (ha : a < 0) (hb : 1 < b) (hs₀a : a < s₀.re) (hs₀b : s₀.re < b) :
    ∑' n : ℕ, (cubicProfile L (Real.log n) : ℂ) * LSeries.term vonMangoldtC s₀ n
      = -logDeriv riemannZeta s₀ + cubicKernel L (1 - s₀) + cubicKernel L (-s₀)
        - ∑' ρ : Zero, (ZD.xiOrderNat ρ.val : ℂ) * cubicKernel L (ρ.val - s₀)
        + ((1 / (2 * π)) * ((∫ t : ℝ, cubicKernel L ((b : ℂ) + t * I - s₀) * weilClock ((b : ℂ) + t * I))
            + (∫ t : ℝ, cubicKernel L ((a : ℂ) + t * I - s₀) * weilClock (1 - ((a : ℂ) + t * I))))
          - weilClock s₀) := by
  have h0 : s₀ ≠ 0 := by
    intro h; rw [h] at hre; simp at hre
  have hends := truncated_explicit_formula_cubic_ends hL hs₀ h0 h1 ha hb hs₀a hs₀b
  have hsplice := CriticalLinePhasor.SeatingLedger.logDeriv_riemannXi_splice hre h1 hz
  have hξ : logDeriv ZD.riemannXi s₀ = weilEnds s₀ + weilClock s₀ + logDeriv riemannZeta s₀ := by
    rw [hsplice]; unfold weilEnds weilClock; ring
  rw [hξ] at hends
  linear_combination hends

end CriticalLinePhasor.ContourArgument

#print axioms CriticalLinePhasor.ContourArgument.stripBoundary_kernel_mul_ends
#print axioms CriticalLinePhasor.ContourArgument.selberg_identity_classical
#print axioms CriticalLinePhasor.ContourArgument.cubic_identity_classical
