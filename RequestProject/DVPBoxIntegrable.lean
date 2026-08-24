import RequestProject.DVPPlanarKernel

/-!
# `ζ'/ζ` is integrable on every compact avoiding the pole

The covering assembly of 401: finitely many kernel-dominated zero-balls
plus continuity off them — packaged through `IsCompact.elim_finite_subcover`
so no case split is even needed (401 covers zero and nonzero points alike).
Boxes are the instance the Littlewood Fubini consumes.
-/

open Metric Complex MeasureTheory Topology Filter

noncomputable section

namespace CriticalLinePhasor.DVP

/-- **`logDeriv ζ` is integrable on every compact set avoiding `1`** —
zeros included. -/
theorem zeta_logDeriv_integrableOn_compact {K : Set ℂ} (hK : IsCompact K)
    (h1 : (1:ℂ) ∉ K) :
    IntegrableOn (logDeriv riemannZeta) K volume := by
  classical
  have hε : ∀ x ∈ K, ∃ ε, 0 < ε ∧
      IntegrableOn (logDeriv riemannZeta) (ball x ε) volume := by
    intro x hx
    obtain ⟨ε, hε0, hint⟩ := zeta_logDeriv_integrableOn_near x
      (by rintro rfl; exact h1 hx)
    exact ⟨ε, hε0, hint⟩
  choose! ε hε0 hint using hε
  have hcov : K ⊆ ⋃ x ∈ K, ball x (ε x) := by
    intro y hy
    exact Set.mem_biUnion hy (mem_ball_self (hε0 y hy))
  obtain ⟨t, hts, htfin, htcov⟩ := hK.elim_finite_subcover_image
    (fun x _ => isOpen_ball) hcov
  apply IntegrableOn.mono_set _ htcov
  exact (integrableOn_finite_biUnion htfin).mpr
    (fun i hi => hint i (hts hi))

/-- The box instance: `ζ'/ζ` is integrable on `[a,b] ×ℂ [t₀,t₁]` whenever
the box avoids the pole. -/
theorem zeta_logDeriv_integrableOn_box {a b t₀ t₁ : ℝ}
    (h1 : (1:ℂ) ∉ Complex.reProdIm (Set.Icc a b) (Set.Icc t₀ t₁)) :
    IntegrableOn (logDeriv riemannZeta)
      (Complex.reProdIm (Set.Icc a b) (Set.Icc t₀ t₁)) volume :=
  zeta_logDeriv_integrableOn_compact
    (isCompact_Icc.reProdIm isCompact_Icc) h1

/-- Boxes at positive height avoid the pole automatically. -/
theorem zeta_logDeriv_integrableOn_box_of_pos {a b t₀ t₁ : ℝ}
    (ht₀ : 0 < t₀) :
    IntegrableOn (logDeriv riemannZeta)
      (Complex.reProdIm (Set.Icc a b) (Set.Icc t₀ t₁)) volume := by
  apply zeta_logDeriv_integrableOn_box
  intro hmem
  rw [Complex.mem_reProdIm] at hmem
  have him : (1:ℂ).im ∈ Set.Icc t₀ t₁ := hmem.2
  simp only [Complex.one_im] at him
  linarith [him.1]

end CriticalLinePhasor.DVP

section AxiomAudit
#print axioms CriticalLinePhasor.DVP.zeta_logDeriv_integrableOn_compact
#print axioms CriticalLinePhasor.DVP.zeta_logDeriv_integrableOn_box
#print axioms CriticalLinePhasor.DVP.zeta_logDeriv_integrableOn_box_of_pos
end AxiomAudit
