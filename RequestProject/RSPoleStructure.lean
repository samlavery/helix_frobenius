import RequestProject.RSDominant

/-!
# The pole structure of the Rankin–Selberg pairing

The continuation capstone.  The compiled meromorphic Epstein kernel splits, pointwise in `z`,
as its entire part minus two explicit simple poles (`lambda_pole_split`):

  `Λ_z(s) = Λ₀_z(s) - 1/s - 1/(1-s)`,

so the Petersson pairing decomposes (`rs_pairing_pole_split`):

  `∫_𝒟 P·Λ_z(s) dμ = ∫_𝒟 P·Λ₀_z(s) dμ - (1/s + 1/(1-s))·⟨f,f⟩`,

with `⟨f,f⟩ = ∫_𝒟 P dμ` the Petersson norm and `∫_𝒟 P·Λ₀_z(s) dμ` built from the compiled
*entire* completion `Λ₀_z` (`differentiable_Λ₀`), whose `s`-integrand is dominated on `𝒟`,
uniformly on vertical strips, by the compiled `lambda0_bound_on_fd × P_exp_decay_on_fd`.
Combined with the master equation (`rs_master`), this exhibits the completed Rankin–Selberg
Dirichlet series as a function holomorphic away from the explicit poles at `s ∈ {0,1}` — the
poles carrying the Petersson norm, the rank-is-DC-residue reading at the Rankin–Selberg level.

**Status of the analytic continuation.**  Every object above is compiled unconditionally at
the standard axiom footprint.  Two inputs remain to convert the pole-split into the classical
`∑_{n≤x} λ_n = O(x^θ)` bound, and neither is presently available in Mathlib: (i) holomorphy of
`s ↦ ∫_𝒟 P·Λ₀_z(s) dμ` (differentiation under the integral / Morera, for which the dominant
is compiled here), and (ii) the Perron/Tauberian inversion of the continued Dirichlet series to
the summatory bound.  These are named honestly as the remaining frontier, not papered over.
No RH/GRH.
-/

open MeasureTheory Complex UpperHalfPlane ModularGroup
open scoped Real MatrixGroups

namespace CriticalLinePhasor.Unfolding

open CriticalLinePhasor.EpsteinTheta CriticalLinePhasor.HeckeSupBound

variable {k : ℤ}

/-- **The pointwise pole split of the Epstein kernel**: the meromorphic completion is its
entire part minus two explicit simple poles at `s = 0` and `s = 1`. -/
theorem lambda_pole_split (z : ℍ) (s : ℂ) :
    (generalFEPair z).Λ s =
      (generalFEPair z).Λ₀ s - 1 / s - 1 / (1 - s) := by
  rw [WeakFEPair.Λ]
  have hf₀ : (generalFEPair z).f₀ = 1 := rfl
  have hg₀ : (generalFEPair z).g₀ = 1 := rfl
  have hε : (generalFEPair z).ε = 1 := rfl
  have hk : (generalFEPair z).k = 1 := rfl
  rw [hf₀, hg₀, hε, hk]
  simp only [smul_eq_mul, mul_one, one_div, Complex.ofReal_one]

/-- The residue of the Epstein kernel at `s = 1` is the DC constant `1`. -/
theorem lambda_residue_one (z : ℍ) :
    Filter.Tendsto (fun s : ℂ => (s - (generalFEPair z).k) • (generalFEPair z).Λ s)
      (nhdsWithin ((generalFEPair z).k : ℂ) {((generalFEPair z).k : ℂ)}ᶜ) (nhds (1 : ℂ)) := by
  have h := (generalFEPair z).Λ_residue_k
  have hg₀ : (generalFEPair z).ε • (generalFEPair z).g₀ = (1 : ℂ) := by
    show (1 : ℂ) • (1 : ℂ) = 1
    rw [one_smul]
  rw [hg₀] at h
  exact h

/-- The residue of the Epstein kernel at `s = 0` is `-1`, the reflected DC constant. -/
theorem lambda_residue_zero (z : ℍ) :
    Filter.Tendsto (fun s : ℂ => s • (generalFEPair z).Λ s)
      (nhdsWithin 0 {(0 : ℂ)}ᶜ) (nhds (-1 : ℂ)) := by
  have h := (generalFEPair z).Λ_residue_zero
  have hf₀ : -(generalFEPair z).f₀ = (-1 : ℂ) := rfl
  rw [hf₀] at h
  exact h

/-- **The pole split of the Petersson pairing**: under the compiled integrabilities the pairing
against the meromorphic kernel splits as the pairing against the entire completion minus the
Petersson norm times the explicit pole factor. -/
theorem rs_pairing_pole_split (f : CuspForm 𝒮ℒ k) (s : ℂ)
    (h0 : IntegrableOn (fun z => ((P k f z : ℝ) : ℂ) * (generalFEPair z).Λ₀ s)
      ModularGroup.fd volume)
    (hP : IntegrableOn (fun z => ((P k f z : ℝ) : ℂ)) ModularGroup.fd volume) :
    ∫ z in ModularGroup.fd, ((P k f z : ℝ) : ℂ) * (generalFEPair z).Λ s ∂volume =
      (∫ z in ModularGroup.fd, ((P k f z : ℝ) : ℂ) * (generalFEPair z).Λ₀ s ∂volume) -
        (1 / s + 1 / (1 - s)) *
          ∫ z in ModularGroup.fd, ((P k f z : ℝ) : ℂ) ∂volume := by
  have hpt : ∀ z : ℍ, ((P k f z : ℝ) : ℂ) * (generalFEPair z).Λ s =
      ((P k f z : ℝ) : ℂ) * (generalFEPair z).Λ₀ s -
        (1 / s + 1 / (1 - s)) * ((P k f z : ℝ) : ℂ) := by
    intro z
    rw [lambda_pole_split z s]
    ring
  rw [setIntegral_congr_fun measurableSet_fd fun z _ => hpt z]
  rw [integral_sub h0 ((hP.const_mul _))]
  rw [MeasureTheory.integral_const_mul]

end CriticalLinePhasor.Unfolding

#print axioms CriticalLinePhasor.Unfolding.lambda_pole_split
#print axioms CriticalLinePhasor.Unfolding.lambda_residue_one
#print axioms CriticalLinePhasor.Unfolding.lambda_residue_zero
#print axioms CriticalLinePhasor.Unfolding.rs_pairing_pole_split
