import RequestProject.RSIntegrand
import RequestProject.GenuineMaassCuspForm3D

/-!
# The Rankin--Selberg unfolding for a Maass form

The compiled unfolding identity never knew about holomorphy: `unfolding_identity` consumes an
arbitrary translation-periodic `F : ℍ → ℂ` together with integrability on the tiling, and its whole
content (fundamental-domain transfer, tile splitting, the Möbius change of variables) is
measure-theoretic.  So the Rankin--Selberg method transfers verbatim from holomorphic cusp forms to
Maass forms once the invariant density is supplied.

For a `GenuineMaassCuspForm3D` the density is `‖u‖²` with **no** weight factor — the wave is
already `SL(2,ℤ)`-invariant (`level_one_invariant`), where the holomorphic case needs `y^k‖f‖²` to
become invariant.  Everything else is the same argument, and `RSIntegrand`'s holomorphic version is
the template followed here line for line.

Why this matters: the left-hand strip integral computes through the Fourier--Whittaker expansion,
which for `GenuineMaassCuspForm3D` is *definitional* (`maassWave = waveFormH (maassFourierCoefficient M) K`),
so orthogonality in `x` gives `∑ₙ |λₙ|² ∫₀^∞ |K(ny)|² y^{s-2} dy`, and the substitution `t = ny`
factors the arithmetic out as `∑ₙ |λₙ|² n^{-s}` against a single archimedean integral.  The
right-hand side is the Petersson pairing against the Eisenstein height, whose poles are already
compiled (`RSPoleStructure.lambda_pole_split`).  That is the route to meromorphic continuation of
the Maass Rankin--Selberg series, i.e. of `ζ(s)·L(s, Sym² u)`.

**Scope.**  This file proves the unfolding step only: periodicity, the tile rewriting, and the
unfolded identity, all unconditional.  The Fourier-orthogonality evaluation of the strip integral,
the archimedean integral's nonvanishing, and the integrability side condition are *not* proven here.
This is the `r = 2` rung; Sato--Tate needs every rank.
-/

open MeasureTheory Complex UpperHalfPlane ModularGroup Matrix.SpecialLinearGroup
open scoped Real MatrixGroups Pointwise

namespace CriticalLinePhasor.Unfolding

open CriticalLinePhasor.ThreeDConverse

/-- The Maass Petersson density.  No weight factor is needed: the wave is already invariant. -/
noncomputable def maassP (M : GenuineMaassCuspForm3D) (z : ℍ) : ℝ :=
  ‖maassWave M.eigenData M.radialKernel z‖ ^ 2

/-- The Maass density is invariant under every modular matrix — the analogue of `P_smul`,
discharged directly by `level_one_invariant`. -/
lemma maassP_smul (M : GenuineMaassCuspForm3D) (γ : SL(2, ℤ)) (z : ℍ) :
    maassP M (γ • z) = maassP M z := by
  unfold maassP
  rw [M.level_one_invariant γ z]

/-- The Maass Rankin--Selberg integrand: the invariant density times the Eisenstein height. -/
noncomputable def maassRsIntegrand (M : GenuineMaassCuspForm3D) (s : ℂ) (z : ℍ) : ℂ :=
  (maassP M z : ℂ) * (z.im : ℂ) ^ s

/-- The Maass RS integrand is translation-periodic: the hypothesis of the compiled unfolding. -/
lemma maassRsIntegrand_periodic (M : GenuineMaassCuspForm3D) (s : ℂ) :
    ∀ (n : ℤ) (z : ℍ),
      maassRsIntegrand M s (ModularGroup.T ^ n • z) = maassRsIntegrand M s z := by
  intro n z
  rw [maassRsIntegrand, maassRsIntegrand, maassP_smul, ModularGroup.im_T_zpow_smul]

/-- On a tile the integrand is the density times the translated height — the Eisenstein shape. -/
lemma maassRsIntegrand_smul (M : GenuineMaassCuspForm3D) (s : ℂ) (γ : SL(2, ℤ)) (z : ℍ) :
    maassRsIntegrand M s (γ • z) =
      (maassP M z : ℂ) * (((γ • z).im : ℝ) : ℂ) ^ s := by
  rw [maassRsIntegrand, maassP_smul]

/-- **The unfolded Maass Rankin--Selberg integral.**  The strip integral of the Maass RS integrand
is the coset sum of density-against-Eisenstein-height integrals over the modular domain.

This is the Rankin--Selberg method for a Maass form, with every measure-theoretic step compiled and
no holomorphy used anywhere.  The integrability side condition is the only hypothesis, and it is
discharged at instantiation by the Eisenstein convergence bound together with `cusp_decay`. -/
theorem maass_rs_unfolding (M : GenuineMaassCuspForm3D) (s : ℂ)
    (hFi : IntegrableOn (maassRsIntegrand M s) fdUnion (volume : Measure ℍ)) :
    ∫ z in strip, maassRsIntegrand M s z ∂(volume : Measure ℍ) =
      ∑' q : CosetQ, ∫ z in ModularGroup.fd,
        (maassP M z : ℂ) * (((rep q • z).im : ℝ) : ℂ) ^ s ∂(volume : Measure ℍ) := by
  rw [unfolding_identity (maassRsIntegrand M s) (maassRsIntegrand_periodic M s) hFi]
  exact tsum_congr fun q => setIntegral_congr_fun measurableSet_fd fun z _ =>
    maassRsIntegrand_smul M s (rep q) z

/-- **Tiling-side integrability transfers from the strip**, exactly as in the holomorphic case
(`rsIntegrand_integrableOn_fdUnion`).  This step is form-independent: it needs only
`Γ_∞`-invariance of the integrand, which is `maassRsIntegrand_periodic`. -/
lemma maassRsIntegrand_integrableOn_fdUnion (M : GenuineMaassCuspForm3D) (s : ℂ)
    (hstrip : IntegrableOn (maassRsIntegrand M s) strip (volume : Measure ℍ)) :
    IntegrableOn (maassRsIntegrand M s) fdUnion (volume : Measure ℍ) := by
  have hinv : ∀ (g : gammaInfty) (z : ℍ),
      maassRsIntegrand M s (g • z) = maassRsIntegrand M s z := by
    rintro ⟨δ, hδ⟩ z
    obtain ⟨n, rfl⟩ := hδ
    exact maassRsIntegrand_periodic M s n z
  rw [isFundamentalDomain_fdUnion.integrableOn_iff isFundamentalDomain_strip hinv]
  exact hstrip

/-- **The Maass unfolding from strip-side integrability alone.**  Every remaining analytic
obligation of the unfolding step is now concentrated in one place: integrability of `‖u‖²(Im)^s`
on the strip, which is the cusp-decay/Eisenstein-convergence estimate. -/
theorem maass_rs_unfolding_of_strip (M : GenuineMaassCuspForm3D) (s : ℂ)
    (hstrip : IntegrableOn (maassRsIntegrand M s) strip (volume : Measure ℍ)) :
    ∫ z in strip, maassRsIntegrand M s z ∂(volume : Measure ℍ) =
      ∑' q : CosetQ, ∫ z in ModularGroup.fd,
        (maassP M z : ℂ) * (((rep q • z).im : ℝ) : ℂ) ^ s ∂(volume : Measure ℍ) :=
  maass_rs_unfolding M s (maassRsIntegrand_integrableOn_fdUnion M s hstrip)

end CriticalLinePhasor.Unfolding

#print axioms CriticalLinePhasor.Unfolding.maassP_smul
#print axioms CriticalLinePhasor.Unfolding.maassRsIntegrand_periodic
#print axioms CriticalLinePhasor.Unfolding.maass_rs_unfolding
#print axioms CriticalLinePhasor.Unfolding.maassRsIntegrand_integrableOn_fdUnion
#print axioms CriticalLinePhasor.Unfolding.maass_rs_unfolding_of_strip
