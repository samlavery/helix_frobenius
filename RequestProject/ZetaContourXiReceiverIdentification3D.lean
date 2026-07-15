import RequestProject.ZetaContourGlobalIdentification3D
import RequestProject.XiChannelReceiver
import RequestProject.ZetaBound

/-!
# The global contour coordinate and the two-sided xi-channel receiver

The contour census is naturally taken in the upper half-plane.  This file proves the exact
two-sided extension needed by the xi-channel:

* conjugation transports every nontrivial zero to another nontrivial zero;
* the proved low-height zero-free region excludes a nontrivial zero on the real axis;
* therefore upper no-drift is equivalent to no-drift for the complete nontrivial zero set;
* all-good-height contour/carrier agreement is equivalent to off-real regularity of the
  independently defined xi-channel; and
* any self-adjoint receiver of that channel supplies the complete native 3D certificate for every
  upper zero.
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

/-- The global contour/carrier identification is equivalent to Mathlib's literal zeta statement.
The forward direction derives the half-unit from the area-law/no-drift theorem for every zero; the
reverse direction converts the literal statement back into the no-drift equation. -/
theorem globalCoordinateIdentification_iff_riemannHypothesis
    (χ₁ : DirichletCharacter ℂ 1) :
    (∀ (T : ℝ) (hT : GoodHeight T), classicalSContour hT = Smult T) ↔
      RiemannHypothesis := by
  rw [globalCoordinateIdentification_iff_allNoRadialDrift χ₁ 2 (by norm_num)]
  constructor
  · intro hall
    apply RHBridge.no_offline_zeros_implies_rh
    intro ρ hρ
    have hre : ρ.re = carrierAbscissa :=
      (noRadialDrift_iff_carrierAbscissa 2 ρ.re (by norm_num)).1 (hall ρ hρ)
    simpa only [carrierAbscissa_eq_half] using hre
  · intro hRH ρ hρ
    have hre : ρ.re = 1 / 2 := CriticalLinePhasor.XiChannel.rh_implies_line hRH hρ
    apply (noRadialDrift_iff_carrierAbscissa 2 ρ.re (by norm_num)).2
    simpa only [carrierAbscissa_eq_half] using hre

/-- The independently continued contour coordinate agrees with the native carrier coordinate at
every good height exactly when the independently defined xi-channel is regular off the real
spectral axis. -/
theorem globalCoordinateIdentification_iff_xiChannel_offReal_regular
    (χ₁ : DirichletCharacter ℂ 1) :
    (∀ (T : ℝ) (hT : GoodHeight T), classicalSContour hT = Smult T) ↔
      ∀ z : ℂ, z.im ≠ 0 →
        ∃ L, Tendsto CriticalLinePhasor.XiChannel.xiChannel (𝓝[≠] z) (𝓝 L) :=
  (globalCoordinateIdentification_iff_riemannHypothesis χ₁).trans
    CriticalLinePhasor.XiChannel.xiChannel_offReal_regular_iff_RH.symm

/-- A self-adjoint receiver of the xi-channel closes the global coordinate identity and hence
selects the complete native 3D certificate for every upper nontrivial zero. -/
theorem globalCoordinateIdentification_and_upperNative3D_of_selfAdjointXiReceiver
    (χ₁ : DirichletCharacter ℂ 1)
    {A : Type*} [CStarAlgebra A] {a : A} (ha : IsSelfAdjoint a)
    (hReg : ∀ z, z ∉ spectrum ℂ a →
      ∃ L, Tendsto CriticalLinePhasor.XiChannel.xiChannel (𝓝[≠] z) (𝓝 L)) :
    (∀ (T : ℝ) (hT : GoodHeight T), classicalSContour hT = Smult T) ∧
      ∀ ρ ∈ ZD.NontrivialZeros, 0 < ρ.im →
        Nonempty (PrincipalContourNative3DCertificate χ₁ ρ) := by
  have hRH : RiemannHypothesis :=
    CriticalLinePhasor.XiChannel.RiemannHypothesis_of_selfAdjoint_xiChannel_receiver ha hReg
  have hglobal := (globalCoordinateIdentification_iff_riemannHypothesis χ₁).2 hRH
  exact ⟨hglobal,
    (globalCoordinateIdentification_iff_upperNative3DCertificate χ₁).1 hglobal⟩

end CriticalLinePhasor.ContourArgument

#print axioms CriticalLinePhasor.ContourArgument.conj_mem_nontrivialZeros
#print axioms CriticalLinePhasor.ContourArgument.nontrivialZero_im_ne_zero
#print axioms CriticalLinePhasor.ContourArgument.upperNoRadialDrift_iff_allNoRadialDrift
#print axioms CriticalLinePhasor.ContourArgument.globalCoordinateIdentification_iff_allNoRadialDrift
#print axioms CriticalLinePhasor.ContourArgument.globalCoordinateIdentification_iff_riemannHypothesis
#print axioms CriticalLinePhasor.ContourArgument.globalCoordinateIdentification_iff_xiChannel_offReal_regular
#print axioms CriticalLinePhasor.ContourArgument.globalCoordinateIdentification_and_upperNative3D_of_selfAdjointXiReceiver
