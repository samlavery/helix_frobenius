import RequestProject.DVPSeatLogDeriv
import RequestProject.VonMangoldtEFStandalone

/-!
# The bridge pillar, off the Euler half-plane

`VMEFStandalone.bridge_pillar` states `ζ′/ζ = ξ′/ξ − 1/s − 1/(s−1) − Γℝ′/Γℝ`
under `1 < Re s`.  Reading its proof, that hypothesis is used for exactly
four things: `s ≠ 0`, `s ≠ 1`, `0 < Re s` (for `Γℝ ≠ 0` and to exclude the
poles `s = −2n`), and `ζ(s) ≠ 0`.  The identity itself is algebra on the
factorizations `ξ = (s(s−1)/2)·Λ̂` and `Λ̂ = Γℝ·ζ`.

Replacing the hypothesis by those four conditions extends the identity to the
region the SEAT actually uses.  For an admissible anchor `w` in the shallow
channel, `s = ½ + iw` has `Re s = ½ − Im w > 0`, and `ζ(s) ≠ 0` is precisely
the anchor hypothesis `(½ + iw) ∉ ZD.NontrivialZeros` in that range.  So the
seat's own hypotheses now deliver the bridge.

WHAT THIS DOES NOT DO: `euler_pillar` (`L(Λ,s) = −ζ′/ζ`) still needs
`1 < Re s`, since the Dirichlet series diverges otherwise.  This extends the
ξ↔ζ half of the chain to the anchors; converting `ζ′/ζ` there into a prime
sum still requires the explicit formula proper (a contour shift), which is
NOT done here.
-/

open Complex

noncomputable section

namespace CriticalLinePhasor.DVP

open VMEFStandalone

theorem bridge_pillar_general (s : ℂ) (hs_ne0 : s ≠ 0) (hs_ne1 : s ≠ 1)
    (hs_re_pos : 0 < s.re) (hζ_ne : riemannZeta s ≠ 0) :
    deriv riemannZeta s / riemannZeta s =
      deriv riemannXi s / riemannXi s -
        1 / s - 1 / (s - 1) - logDeriv Complex.Gammaℝ s := by
  have hs_sub_ne : s - 1 ≠ 0 := sub_ne_zero.mpr hs_ne1
  have hs_div_ne : s / 2 ≠ 0 := div_ne_zero hs_ne0 two_ne_zero
  have hΓℝ_ne : Complex.Gammaℝ s ≠ 0 := Complex.Gammaℝ_ne_zero_of_re_pos hs_re_pos
  have hcompleted_ne : completedRiemannZeta s ≠ 0 := by
    intro hcomp; apply hζ_ne
    rw [riemannZeta_def_of_ne_zero hs_ne0, hcomp, zero_div]
  have hxi_classical : riemannXi s = (s * (s - 1) / 2) * completedRiemannZeta s :=
    riemannXi_eq_classical_of_ne_zero_of_ne_one s hs_ne0 hs_ne1
  have hxi_ne : riemannXi s ≠ 0 := by
    rw [hxi_classical]
    exact mul_ne_zero
      (div_ne_zero (mul_ne_zero hs_ne0 hs_sub_ne) two_ne_zero) hcompleted_ne
  have hΓℝ_diff : DifferentiableAt ℂ Complex.Gammaℝ s := by
    have h_ne : ∀ n : ℕ, s ≠ -(2 * (n : ℂ)) := by
      intro n heq
      have hre : s.re = -(2 * (n : ℝ)) := by
        rw [heq]; simp
      have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      rw [hre] at hs_re_pos
      linarith
    have h_half_ne : ∀ m : ℕ, s / 2 ≠ -(m : ℂ) := by
      intro m heq
      have : s = -(2 * (m : ℂ)) := by linear_combination 2 * heq
      exact h_ne m this
    have hΓ_diff : DifferentiableAt ℂ Complex.Gamma (s / 2) :=
      Complex.differentiableAt_Gamma _ h_half_ne
    have hcpow_diff :
        DifferentiableAt ℂ (fun t : ℂ => (Real.pi : ℂ) ^ (-t / 2)) s := by
      refine DifferentiableAt.const_cpow
        ((differentiableAt_id.neg).div_const 2) ?_
      left; exact_mod_cast Real.pi_pos.ne'
    have hcomp :
        DifferentiableAt ℂ (fun t : ℂ => Complex.Gamma (t / 2)) s :=
      hΓ_diff.comp s (differentiableAt_id.div_const 2)
    have h_product :
        DifferentiableAt ℂ
          (fun t : ℂ => (Real.pi : ℂ) ^ (-t / 2) * Complex.Gamma (t / 2)) s :=
      hcpow_diff.mul hcomp
    have h_eq :
        Complex.Gammaℝ = fun t : ℂ => (Real.pi : ℂ) ^ (-t / 2) * Complex.Gamma (t / 2) := by
      funext t; exact Complex.Gammaℝ_def t
    rw [h_eq]; exact h_product
  have hζ_diff : DifferentiableAt ℂ riemannZeta s := differentiableAt_riemannZeta hs_ne1
  have hcompleted_diff : DifferentiableAt ℂ completedRiemannZeta s :=
    differentiableAt_completedZeta hs_ne0 hs_ne1
  set p : ℂ → ℂ := fun z => z * (z - 1) / 2 with hp_def
  have hp_diff : DifferentiableAt ℂ p s := by
    show DifferentiableAt ℂ (fun z => z * (z - 1) / 2) s
    exact (differentiableAt_id.mul (differentiableAt_id.sub_const 1)).div_const 2
  have hp_ne : p s ≠ 0 := by
    show s * (s - 1) / 2 ≠ 0
    exact div_ne_zero (mul_ne_zero hs_ne0 hs_sub_ne) two_ne_zero
  have hriemannXi_eventually :
      riemannXi =ᶠ[nhds s] fun z => p z * completedRiemannZeta z := by
    have h_open_ne_zero : IsOpen ({0}ᶜ : Set ℂ) := isOpen_compl_singleton
    have h_open_ne_one : IsOpen ({1}ᶜ : Set ℂ) := isOpen_compl_singleton
    have h_mem : s ∈ ({0}ᶜ ∩ {1}ᶜ : Set ℂ) := by
      refine ⟨?_, ?_⟩ <;> simp [hs_ne0, hs_ne1]
    have h_open : IsOpen ({0}ᶜ ∩ {1}ᶜ : Set ℂ) := h_open_ne_zero.inter h_open_ne_one
    refine Filter.eventuallyEq_of_mem (h_open.mem_nhds h_mem) ?_
    intro z hz
    show riemannXi z = z * (z - 1) / 2 * completedRiemannZeta z
    exact riemannXi_eq_classical_of_ne_zero_of_ne_one z hz.1 hz.2
  have hxi_logDeriv_eq :
      logDeriv riemannXi s =
        logDeriv p s + logDeriv completedRiemannZeta s := by
    have h_deriv_eq :
        deriv riemannXi s = deriv (fun z => p z * completedRiemannZeta z) s :=
      Filter.EventuallyEq.deriv_eq hriemannXi_eventually
    have h_val_eq : riemannXi s = (fun z => p z * completedRiemannZeta z) s :=
      hriemannXi_eventually.self_of_nhds
    simp only [logDeriv_apply] at *
    rw [h_deriv_eq, h_val_eq]
    have := logDeriv_mul s hp_ne hcompleted_ne hp_diff hcompleted_diff
    simpa [logDeriv_apply] using this
  have hp_log :
      logDeriv p s = 1 / s + 1 / (s - 1) := by
    have hp_mul : p = fun z => (z / 2) * (z - 1) := by
      funext z
      show z * (z - 1) / 2 = (z / 2) * (z - 1)
      ring
    rw [hp_mul]
    have h_div2_ne : s / 2 ≠ 0 := hs_div_ne
    have h_sub1_ne : s - 1 ≠ 0 := hs_sub_ne
    have h_div2_diff : DifferentiableAt ℂ (fun z : ℂ => z / 2) s :=
      differentiableAt_id.div_const 2
    have h_sub1_diff : DifferentiableAt ℂ (fun z : ℂ => z - 1) s :=
      differentiableAt_id.sub_const 1
    rw [logDeriv_mul s h_div2_ne h_sub1_ne h_div2_diff h_sub1_diff]
    have hdiv2 : logDeriv (fun z : ℂ => z / 2) s = 1 / s := by
      rw [logDeriv_apply, deriv_div_const, deriv_id'']; field_simp
    have hsub1 : logDeriv (fun z : ℂ => z - 1) s = 1 / (s - 1) := by
      rw [logDeriv_apply]; simp
    rw [hdiv2, hsub1]
  have hriemann_eventually :
      riemannZeta =ᶠ[nhds s] fun z => completedRiemannZeta z / Complex.Gammaℝ z := by
    have h_open_re : IsOpen {z : ℂ | (0 : ℝ) < z.re} :=
      isOpen_lt continuous_const Complex.continuous_re
    have h_mem : s ∈ {z : ℂ | (0 : ℝ) < z.re} := by
      show (0 : ℝ) < s.re; linarith
    refine Filter.eventuallyEq_of_mem (h_open_re.mem_nhds h_mem) ?_
    intro z hz
    have hz_ne0 : z ≠ 0 := by
      intro h0; rw [h0] at hz; simp at hz
    exact riemannZeta_def_of_ne_zero hz_ne0
  have hζ_logDeriv :
      logDeriv riemannZeta s =
        logDeriv completedRiemannZeta s - logDeriv Complex.Gammaℝ s := by
    have h_deriv_eq :
        deriv riemannZeta s = deriv (fun z => completedRiemannZeta z / Complex.Gammaℝ z) s :=
      Filter.EventuallyEq.deriv_eq hriemann_eventually
    have h_val_eq : riemannZeta s = (fun z => completedRiemannZeta z / Complex.Gammaℝ z) s :=
      hriemann_eventually.self_of_nhds
    simp only [logDeriv_apply]
    rw [h_deriv_eq, h_val_eq]
    have := logDeriv_div s hcompleted_ne hΓℝ_ne hcompleted_diff hΓℝ_diff
    simpa [logDeriv_apply] using this
  have hζ_unfold : deriv riemannZeta s / riemannZeta s = logDeriv riemannZeta s := by
    rw [logDeriv_apply]
  have hxi_unfold : deriv riemannXi s / riemannXi s = logDeriv riemannXi s := by
    rw [logDeriv_apply]
  rw [hζ_unfold, hζ_logDeriv]
  have h_subst : logDeriv completedRiemannZeta s = logDeriv riemannXi s - logDeriv p s := by
    rw [eq_sub_iff_add_eq, add_comm]
    exact hxi_logDeriv_eq.symm
  rw [h_subst, hp_log, hxi_unfold]
  ring

/-- **Nonnegativity of real-part zero-term** at `σ > 1` for zeros in the
critical strip. Pure algebra. Ported from `RequestProject.LogDerivIdentity`. -/
theorem re_zero_term_nonneg (σ : ℝ) (hσ : 1 < σ) (ρ : ℂ) (hρ_re : 0 < ρ.re)
    (hρ_re' : ρ.re < 1) :
    0 ≤ ((1 : ℂ) / (↑σ - ρ) + 1 / ρ).re := by
  simp only [Complex.add_re, one_div, Complex.inv_re]
  apply add_nonneg
  · apply div_nonneg
    · simp [Complex.sub_re, Complex.ofReal_re]; linarith
    · exact Complex.normSq_nonneg _
  · apply div_nonneg
    · exact le_of_lt hρ_re
    · exact Complex.normSq_nonneg _

end CriticalLinePhasor.DVP

section AxiomAudit
#print axioms CriticalLinePhasor.DVP.bridge_pillar_general
end AxiomAudit
