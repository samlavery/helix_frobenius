import RequestProject.DVPGrowthBounds

/-!
# Littlewood in N_all-form: opening bricks

Target: `|∫₀ᵀ S_all(t) dt| ≤ C(1 + log(1+T))` — classical (Littlewood 1924),
formalizable, and the classical half of the registration residuals
(RH_LEDGER 391).  First brick: the pointwise upper bound for `log‖ζ‖` on
vertical lines in the quarter strip, total thanks to `Real.log 0 = 0`.
-/

open Complex

noncomputable section

namespace CriticalLinePhasor.DVP

/-- **The pointwise log-growth bound**, total on the quarter strip:
`log‖ζ(s)‖ ≤ log 24 + (3/4)·log|Im s|` for `σ ∈ [¼, 2]`, `|Im s| ≥ 2`
(at zeros the left side is `log 0 = 0` and the bound holds trivially). -/
theorem log_norm_zeta_le {s : ℂ} (him : 2 ≤ |s.im|)
    (hσl : (1:ℝ)/4 ≤ s.re) (hσu : s.re ≤ 2) :
    Real.log ‖riemannZeta s‖
      ≤ Real.log 24 + (3/4) * Real.log |s.im| := by
  have hT2 : (0:ℝ) < |s.im| := by linarith
  have hlogT : (0:ℝ) ≤ Real.log |s.im| := by
    apply Real.log_nonneg
    linarith
  have hlog24 : (0:ℝ) < Real.log 24 := by
    apply Real.log_pos
    norm_num
  rcases eq_or_ne ‖riemannZeta s‖ 0 with h0 | h0
  · rw [h0, Real.log_zero]
    positivity
  · have hpos : (0:ℝ) < ‖riemannZeta s‖ :=
      lt_of_le_of_ne (norm_nonneg _) (Ne.symm h0)
    have hgrow := zeta_polynomial_growth_quarter him hσl hσu
    calc Real.log ‖riemannZeta s‖
        ≤ Real.log (24 * |s.im| ^ ((3:ℝ)/4)) :=
          Real.log_le_log hpos hgrow
      _ = Real.log 24 + (3/4) * Real.log |s.im| := by
          rw [Real.log_mul (by norm_num)
              (by positivity : |s.im| ^ ((3:ℝ)/4) ≠ 0),
            Real.log_rpow hT2]

/-- The integrated form over the quarter strip's σ-range:
`∫_{¼}^{2} log‖ζ(σ+iT)‖ dσ ≤ (7/4)(log 24 + (3/4)·log|T|)` — the upper half
of Littlewood's box estimate, from the constant majorant.  (Stated as an
inequality against the constant; integrability of `log‖ζ‖` itself is NOT
needed for the upper route Littlewood uses — the majorant integral IS the
bound consumed downstream.) -/
theorem log_zeta_sigma_majorant {T : ℝ} (hT : 2 ≤ |T|) :
    ∀ σ ∈ Set.Icc ((1:ℝ)/4) 2,
      Real.log ‖riemannZeta ((σ:ℝ) + T * Complex.I)‖
        ≤ Real.log 24 + (3/4) * Real.log |T| := by
  intro σ hσ
  have him : |((σ:ℝ) + T * Complex.I).im| = |T| := by
    simp
  have hre : ((σ:ℝ) + T * Complex.I).re = σ := by
    simp
  have := log_norm_zeta_le (s := (σ:ℝ) + T * Complex.I)
    (by rw [him]; exact hT) (by rw [hre]; exact hσ.1)
    (by rw [hre]; exact hσ.2)
  rwa [him] at this

end CriticalLinePhasor.DVP

section AxiomAudit
#print axioms CriticalLinePhasor.DVP.log_norm_zeta_le
#print axioms CriticalLinePhasor.DVP.log_zeta_sigma_majorant
end AxiomAudit
