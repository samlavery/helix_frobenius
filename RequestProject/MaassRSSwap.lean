import RequestProject.LambdaHeightPairing
import RequestProject.RSSwap

/-!
# The sum–integral swap for the Maass pairing

`RSSwap.rs_swap` passes the coset sum through the Petersson integral.  Its mechanism is that the
summand is *exactly* the Rankin--Selberg integrand at the coset translate, so the domination the
interchange needs is the hypothesis-free lintegral unfolding evaluated against the strip
integrability.

Every input has a Maass counterpart already proved in this campaign:
`maassRsIntegrand_smul`, `maassRsIntegrand_integrableOn_strip`, `continuous_maassP`,
`maassP_nonneg`.  Ninth form-independent transfer.

**Provenance.**  This is `rs_swap` with the density and its four inputs replaced; nothing else
changed.

**Scope.**  This is the `r = 2` rung.  Sato--Tate needs every rank; this is not a route to it.
-/

open MeasureTheory Complex UpperHalfPlane ModularGroup Set Filter
open scoped Real Topology MatrixGroups ENNReal

namespace CriticalLinePhasor.Unfolding

open CriticalLinePhasor.EpsteinTheta CriticalLinePhasor.ThreeDConverse

theorem maass_rs_swap (M : GenuineMaassCuspForm3D) {s : ℂ} (hs : 1 < s.re) :
    ∫ z in ModularGroup.fd, ((maassP M z : ℝ) : ℂ) *
        (∑' q : CosetQ,
          ((gram z ((rep q).1 1 0, (rep q).1 1 1) : ℝ) : ℂ) ^ (-s)) ∂volume =
      ∑' q : CosetQ, ∫ z in ModularGroup.fd, ((maassP M z : ℝ) : ℂ) *
        ((gram z ((rep q).1 1 0, (rep q).1 1 1) : ℝ) : ℂ) ^ (-s) ∂volume := by
  have hkey : ∀ (q : CosetQ) (z : ℍ), ((maassP M z : ℝ) : ℂ) *
      ((gram z ((rep q).1 1 0, (rep q).1 1 1) : ℝ) : ℂ) ^ (-s) =
      maassRsIntegrand M s (rep q • z) := by
    intro q z
    rw [maassRsIntegrand_smul, im_smul_cpow]
  have hmeas : ∀ q : CosetQ, AEStronglyMeasurable (fun z : ℍ => ((maassP M z : ℝ) : ℂ) *
      ((gram z ((rep q).1 1 0, (rep q).1 1 1) : ℝ) : ℂ) ^ (-s))
      (volume.restrict ModularGroup.fd) := fun q =>
    ((Complex.continuous_ofReal.comp (continuous_maassP M)).mul
      (continuous_gram_cpow (rep_row_ne_zero' q) s)).aestronglyMeasurable.restrict
  have hdom : ∑' q : CosetQ, ∫⁻ z in ModularGroup.fd,
      ‖((maassP M z : ℝ) : ℂ) *
        ((gram z ((rep q).1 1 0, (rep q).1 1 1) : ℝ) : ℂ) ^ (-s)‖ₑ ∂volume ≠ ⊤ := by
    have hcongr : ∀ q : CosetQ, (∫⁻ z in ModularGroup.fd,
        ‖((maassP M z : ℝ) : ℂ) *
          ((gram z ((rep q).1 1 0, (rep q).1 1 1) : ℝ) : ℂ) ^ (-s)‖ₑ ∂volume) =
        ∫⁻ z in ModularGroup.fd, ‖maassRsIntegrand M s (rep q • z)‖ₑ ∂volume := by
      intro q
      exact lintegral_congr fun z => by rw [hkey]
    have hper : ∀ (n : ℤ) (z : ℍ),
        ‖maassRsIntegrand M s (ModularGroup.T ^ n • z)‖ₑ = ‖maassRsIntegrand M s z‖ₑ := by
      intro n z
      rw [maassRsIntegrand_periodic]
    have hunfold := lintegral_unfolding (fun z => ‖maassRsIntegrand M s z‖ₑ) hper
    have hfin := (maassRsIntegrand_integrableOn_strip M hs).2
    rw [tsum_congr hcongr, ← hunfold]
    exact hfin.ne
  have hpull : ∀ z : ℍ, ((maassP M z : ℝ) : ℂ) *
      (∑' q : CosetQ, ((gram z ((rep q).1 1 0, (rep q).1 1 1) : ℝ) : ℂ) ^ (-s)) =
      ∑' q : CosetQ, ((maassP M z : ℝ) : ℂ) *
        ((gram z ((rep q).1 1 0, (rep q).1 1 1) : ℝ) : ℂ) ^ (-s) := fun z =>
    (tsum_mul_left).symm
  rw [setIntegral_congr_fun measurableSet_fd fun z _ => hpull z,
    integral_tsum hmeas hdom]

end CriticalLinePhasor.Unfolding

#print axioms CriticalLinePhasor.Unfolding.maass_rs_swap
