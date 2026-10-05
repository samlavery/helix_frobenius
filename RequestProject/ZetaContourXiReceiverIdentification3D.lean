import RequestProject.ZetaContourGlobalIdentification3D
import RequestProject.XiChannelReceiver
import RequestProject.ZetaBound

/-!
# The global contour coordinate and the two-sided xi-channel receiver

The contour census is naturally taken in the upper half-plane.  This file proves the exact
two-sided extension needed by the xi-channel:

* conjugation transports every nontrivial zero to another nontrivial zero;
* the proved low-height zero-free region excludes a nontrivial zero on the real axis;
* therefore upper no-drift is equivalent to no-drift for the complete nontrivial zero set; and
* all-good-height contour/carrier agreement gives Mathlib's `RiemannHypothesis`.
-/

open Complex ComplexConjugate Filter Topology

namespace CriticalLinePhasor.ContourArgument

open CriticalLinePhasor
open CriticalLinePhasor.ResidueJump
open CriticalLinePhasor.ThreeDFocal

/-- Conjugation preserves the genuine nontrivial zero set, proved through the entire xi function. -/
theorem conj_mem_nontrivialZeros {ρ : ℂ} (hρ : ρ ∈ ZD.NontrivialZeros) :
    conj ρ ∈ ZD.NontrivialZeros := by
  apply (ZD.riemannXi_eq_zero_iff (conj ρ)).mp
  rw [riemannXi_conj, (ZD.riemannXi_eq_zero_iff ρ).mpr hρ, map_zero]

/-- A nontrivial zero cannot lie on the real axis.  This consumes the compiled zero-free strip
`|Im s| < 2`, not a zero-location premise. -/
theorem nontrivialZero_im_ne_zero {ρ : ℂ} (hρ : ρ ∈ ZD.NontrivialZeros) :
    ρ.im ≠ 0 := by
  intro him
  exact riemannZeta_ne_zero_of_im_lt_two hρ.1 hρ.2.1 (by simp [him]) hρ.2.2

/-- Upper-half-plane no drift extends to every nontrivial zero by conjugation; the real-axis case
is excluded by `nontrivialZero_im_ne_zero`. -/
theorem upperNoRadialDrift_iff_allNoRadialDrift (n : ℝ) (hn : 1 < n) :
    (∀ ρ ∈ ZD.NontrivialZeros, 0 < ρ.im →
        n ^ (ρ.re - carrierAbscissa) = 1) ↔
      ∀ ρ ∈ ZD.NontrivialZeros, n ^ (ρ.re - carrierAbscissa) = 1 := by
  constructor
  · intro hupper ρ hρ
    by_cases hpos : 0 < ρ.im
    · exact hupper ρ hρ hpos
    · have himne := nontrivialZero_im_ne_zero hρ
      have hρneg : ρ.im < 0 := lt_of_le_of_ne (le_of_not_gt hpos) himne
      have hneg : 0 < (conj ρ).im := by
        simp only [conj_im]
        exact neg_pos.mpr hρneg
      have hconj := hupper (conj ρ) (conj_mem_nontrivialZeros hρ) hneg
      simpa only [conj_re] using hconj
  · intro hall ρ hρ _hρim
    exact hall ρ hρ

/-- Every-good-height coordinate agreement is exactly no radial drift for the complete nontrivial
zero set.  The right side still contains no numerical midpoint. -/
theorem globalCoordinateIdentification_iff_allNoRadialDrift
    (χ₁ : DirichletCharacter ℂ 1) (n : ℝ) (hn : 1 < n) :
    (∀ (T : ℝ) (hT : GoodHeight T), classicalSContour hT = Smult T) ↔
      ∀ ρ ∈ ZD.NontrivialZeros, n ^ (ρ.re - carrierAbscissa) = 1 :=
  (globalCoordinateIdentification_iff_upperNoRadialDrift χ₁ n hn).trans
    (upperNoRadialDrift_iff_allNoRadialDrift n hn)

/-- The global contour/carrier identification gives Mathlib's literal zeta statement: the
half-unit follows from the area-law/no-drift theorem for every zero. -/
theorem riemannHypothesis_of_globalCoordinateIdentification
    (χ₁ : DirichletCharacter ℂ 1)
    (hid : ∀ (T : ℝ) (hT : GoodHeight T), classicalSContour hT = Smult T) :
    RiemannHypothesis := by
  have hall := (globalCoordinateIdentification_iff_allNoRadialDrift χ₁ 2 (by norm_num)).1 hid
  apply RHBridge.no_offline_zeros_implies_rh
  intro ρ hρ
  have hre : ρ.re = carrierAbscissa :=
    (noRadialDrift_iff_carrierAbscissa 2 ρ.re (by norm_num)).1 (hall ρ hρ)
  simpa only [carrierAbscissa_eq_half] using hre

end CriticalLinePhasor.ContourArgument

#print axioms CriticalLinePhasor.ContourArgument.conj_mem_nontrivialZeros
#print axioms CriticalLinePhasor.ContourArgument.nontrivialZero_im_ne_zero
#print axioms CriticalLinePhasor.ContourArgument.upperNoRadialDrift_iff_allNoRadialDrift
#print axioms CriticalLinePhasor.ContourArgument.globalCoordinateIdentification_iff_allNoRadialDrift
#print axioms CriticalLinePhasor.ContourArgument.riemannHypothesis_of_globalCoordinateIdentification
