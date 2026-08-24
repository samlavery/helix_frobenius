import RequestProject.DVPBoxIntegrable

/-!
# The box Fubini swap

For `f` integrable on the box `[a,b] ×ℂ [t₀,t₁]`, the iterated interval
integrals commute.  Transport through the measure-preserving identification
`ℂ ≃ᵐ ℝ × ℝ` (`re_add_im` collapses the composition), split the restricted
product measure, and apply `integral_integral_swap`.
-/

open Metric Complex MeasureTheory Topology Filter

noncomputable section

namespace CriticalLinePhasor.DVP

/-- **The box Fubini swap**: for `f` integrable on the closed box, the
iterated interval integrals in the two orders agree. -/
theorem box_integral_swap {f : ℂ → ℝ} {a b t₀ t₁ : ℝ}
    (hab : a ≤ b) (ht : t₀ ≤ t₁)
    (hf : IntegrableOn f
      (Complex.reProdIm (Set.Icc a b) (Set.Icc t₀ t₁)) volume) :
    ∫ x in a..b, (∫ t in t₀..t₁, f ((x:ℝ) + (t:ℝ) * Complex.I))
      = ∫ t in t₀..t₁, (∫ x in a..b, f ((x:ℝ) + (t:ℝ) * Complex.I)) := by
  set e : ℂ ≃ᵐ ℝ × ℝ := Complex.measurableEquivRealProd with hedef
  have hep : MeasurePreserving e volume (volume.prod volume) :=
    Complex.volume_preserving_equiv_real_prod
  have hpre : ((e : ℂ → ℝ × ℝ) ⁻¹' (Set.Icc a b ×ˢ Set.Icc t₀ t₁))
      = Complex.reProdIm (Set.Icc a b) (Set.Icc t₀ t₁) := by
    ext z
    simp only [hedef, Complex.measurableEquivRealProd, Complex.mem_reProdIm,
      Set.mem_prod, Set.mem_preimage, Set.mem_Icc]
    tauto
  have hS : MeasurableSet (Set.Icc a b ×ˢ Set.Icc t₀ t₁ : Set (ℝ × ℝ)) :=
    measurableSet_Icc.prod measurableSet_Icc
  have hres := hep.restrict_preimage hS
  rw [hpre] at hres
  set g : ℝ × ℝ → ℝ := fun p => f ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I)
    with hgdef
  have hge : g ∘ (e : ℂ → ℝ × ℝ) = f := by
    funext z
    show f ((z.re : ℂ) + (z.im : ℂ) * Complex.I) = f z
    rw [Complex.re_add_im]
  have hgmeas : AEStronglyMeasurable g
      ((volume.prod volume).restrict (Set.Icc a b ×ˢ Set.Icc t₀ t₁)) := by
    have h1 : AEStronglyMeasurable (g ∘ (e : ℂ → ℝ × ℝ))
        (volume.restrict (Complex.reProdIm (Set.Icc a b) (Set.Icc t₀ t₁))) := by
      rw [hge]
      exact hf.aestronglyMeasurable
    exact (hres.aestronglyMeasurable_comp_iff e.measurableEmbedding).mp h1
  have hgint : Integrable g
      ((volume.prod volume).restrict (Set.Icc a b ×ˢ Set.Icc t₀ t₁)) := by
    apply (hres.integrable_comp hgmeas).mp
    rw [hge]
    exact hf
  rw [← Measure.prod_restrict] at hgint
  have hswap := integral_integral_swap
    (f := fun x t => f ((x:ℝ) + (t:ℝ) * Complex.I)) hgint
  have hIcc : ∀ (c d : ℝ), c ≤ d → ∀ F : ℝ → ℝ,
      ∫ s in c..d, F s = ∫ s in Set.Icc c d, F s := by
    intro c d hcd F
    rw [intervalIntegral.integral_of_le hcd]
    exact (MeasureTheory.integral_Icc_eq_integral_Ioc).symm
  have hinner1 : (fun x : ℝ => ∫ t in t₀..t₁, f ((x:ℝ) + (t:ℝ) * Complex.I))
      = fun x : ℝ => ∫ t in Set.Icc t₀ t₁, f ((x:ℝ) + (t:ℝ) * Complex.I) := by
    funext x
    exact hIcc t₀ t₁ ht _
  have hinner2 : (fun t : ℝ => ∫ x in a..b, f ((x:ℝ) + (t:ℝ) * Complex.I))
      = fun t : ℝ => ∫ x in Set.Icc a b, f ((x:ℝ) + (t:ℝ) * Complex.I) := by
    funext t
    exact hIcc a b hab _
  calc ∫ x in a..b, (∫ t in t₀..t₁, f ((x:ℝ) + (t:ℝ) * Complex.I))
      = ∫ x in Set.Icc a b,
          (∫ t in Set.Icc t₀ t₁, f ((x:ℝ) + (t:ℝ) * Complex.I)) := by
        rw [hinner1, hIcc a b hab]
    _ = ∫ t in Set.Icc t₀ t₁,
          (∫ x in Set.Icc a b, f ((x:ℝ) + (t:ℝ) * Complex.I)) := hswap
    _ = ∫ t in t₀..t₁, (∫ x in a..b, f ((x:ℝ) + (t:ℝ) * Complex.I)) := by
        rw [hinner2, hIcc t₀ t₁ ht]

end CriticalLinePhasor.DVP

section AxiomAudit
#print axioms CriticalLinePhasor.DVP.box_integral_swap
end AxiomAudit
