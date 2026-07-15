import RequestProject.UnfoldingIdentity
import RequestProject.ParsevalExact

/-!
# The Rankin–Selberg integrand and its unfolded form

Slice five (a) of brick (iv).  The RS integrand is the invariant Petersson density `P` (the
compiled weight-`k` invariant `y^k‖f‖²`) times the complex Eisenstein height `(Im z)^s`.  Its
translation-periodicity (`rsIntegrand_periodic`) discharges the hypothesis of the compiled
unfolding identity, and the tile-side rewriting (`rsIntegrand_smul`, via the compiled GL-native
`P_invariant`) puts the unfolded sum into Eisenstein shape (`rs_unfolding`):

  `∫_{strip} P·(Im)^s  =  ∑'_q ∫_𝒟 P(z)·(Im (γ_q·z))^s`

— the left side is the Mellin transform of the exact energy readout (`rankin_energy_exact`
supplies `∫₀¹‖f‖²dx = Σ‖aₙ‖²e^{-4πny}` fiberwise), the right side is the Petersson pairing
against the Eisenstein kernel; the integrability side condition is discharged at
instantiation by the Eisenstein convergence bound.  No RH/GRH.
-/

open MeasureTheory Complex UpperHalfPlane ModularGroup Matrix.SpecialLinearGroup
open scoped Real MatrixGroups Pointwise

namespace CriticalLinePhasor.Unfolding

open CriticalLinePhasor.HeckeSupBound

variable {k : ℤ}

/-- The Rankin–Selberg integrand: the invariant Petersson density times the complex
Eisenstein height. -/
noncomputable def rsIntegrand (f : CuspForm 𝒮ℒ k) (s : ℂ) (z : ℍ) : ℂ :=
  (P k f z : ℂ) * (z.im : ℂ) ^ s

/-- The Petersson density is invariant under every modular matrix. -/
lemma P_smul (f : CuspForm 𝒮ℒ k) (γ : SL(2, ℤ)) (z : ℍ) :
    P k f (γ • z) = P k f z := by
  have hmem : (mapGL ℝ γ : GL (Fin 2) ℝ) ∈ 𝒮ℒ := ⟨γ, rfl⟩
  have haction : (mapGL ℝ γ) • z = γ • z := rfl
  rw [← haction]
  exact P_invariant f hmem z

/-- The RS integrand is translation-periodic: the hypothesis of the compiled unfolding. -/
lemma rsIntegrand_periodic (f : CuspForm 𝒮ℒ k) (s : ℂ) :
    ∀ (n : ℤ) (z : ℍ),
      rsIntegrand f s (ModularGroup.T ^ n • z) = rsIntegrand f s z := by
  intro n z
  rw [rsIntegrand, rsIntegrand, P_smul, ModularGroup.im_T_zpow_smul]

/-- On a tile, the RS integrand is the Petersson density times the translated height: the
Eisenstein shape of the unfolded sum. -/
lemma rsIntegrand_smul (f : CuspForm 𝒮ℒ k) (s : ℂ) (γ : SL(2, ℤ)) (z : ℍ) :
    rsIntegrand f s (γ • z) = (P k f z : ℂ) * (((γ • z).im : ℝ) : ℂ) ^ s := by
  rw [rsIntegrand, P_smul]

/-- **The unfolded Rankin–Selberg integral**: the strip integral of the RS integrand is the
coset sum of Petersson-against-Eisenstein-height integrals over the modular domain.  The
integrability side condition is discharged at instantiation by the Eisenstein convergence
bound on `Re s > 1`. -/
theorem rs_unfolding (f : CuspForm 𝒮ℒ k) (s : ℂ)
    (hFi : IntegrableOn (rsIntegrand f s) fdUnion (volume : Measure ℍ)) :
    ∫ z in strip, rsIntegrand f s z ∂(volume : Measure ℍ) =
      ∑' q : CosetQ, ∫ z in ModularGroup.fd,
        (P k f z : ℂ) * (((rep q • z).im : ℝ) : ℂ) ^ s ∂(volume : Measure ℍ) := by
  rw [unfolding_identity (rsIntegrand f s) (rsIntegrand_periodic f s) hFi]
  exact tsum_congr fun q => setIntegral_congr_fun measurableSet_fd fun z _ =>
    rsIntegrand_smul f s (rep q) z

end CriticalLinePhasor.Unfolding

#print axioms CriticalLinePhasor.Unfolding.rs_unfolding
