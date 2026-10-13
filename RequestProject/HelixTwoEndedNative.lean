import RequestProject.HelixTwoEndedClosure
import RequestProject.GlobalHelixGaussianSourceRegistration
import RequestProject.GlobalHelixFiniteGaussianWeakFE

/-!
# The native 3D reflection supplies the two-ended pair (ledger 1253)

`HelixTwoEndedClosure` proves the exact two-ended split for any pair `(f, g)` with a reflection
`f (1/x) = ε·x^k·g x`. Here the pair is built from the house's 3D banks, and the reflection is the compiled
3D one:

* `helixBank x = gaussianLattice3DBankReadout x`: the Gaussian source bank on the 3D helix (every nonzero lattice
  mode at multiplicative height `n²x`, the zero mode as its own source channel), read at height `x`;
* `antiHelixBank x = gaussianLattice3DTransformedReadout (1/x)`: the same bank after the global helix involution and
  the exact height shear, with **conjugated** coefficients (`indexedReciprocalCoefficientFiber`, `starRingEnd`),
  read at the reflected height `1/x`;
* `native_reflection`: `helixBank (1/x) = x^{1/2}·antiHelixBank x`. This is
  `gaussianLattice3D_globalHelixReflection` read at `1/x`: the origin reflection with conjugation.

`nativePair` is the resulting pair (`k = ½`, `ε = 1`, constant modes `1`). Its `h_feq` is `native_reflection`;
integrability and the rapid decay of the nonconstant modes come from the compiled bank identities
(`gaussianLattice3DBankReadout_eq`, `gaussianLatticeTheta_continuousOn`, `gaussianLatticeTheta_sub_one_rapid`).

Results:
* `nativePair_Λ`: its completed transform is the completed zeta transform (`hurwitzEvenFEPair 0`). This is an
  identification of the two pairs' data at positive heights; nothing about the native split uses it.
* `completedRiemannZeta_native_cut`: for every `s ≠ 0, 1` and every cut `c > 0`,
  `completedRiemannZeta s = ½·[helix strand of the helix bank above c + anti-helix strand of the anti-helix bank
  above 1/c − the two constant-mode bookings]`, at `s/2`. The second strand integrates the anti-helix bank itself.
* `riemannZeta_eq_zero_iff_native_two_ended`: at height `Z` and every cut `c > 0`,
  `ζ(½ + i·log Z) = 0 ⟺ helixEndAt c + conj (helixEndAt (1/c)) = 0`, the ends built from the helix bank.

Scope: the Gaussian bank (all coefficients `1`, the trivial routing). The conductor-routed (η) bank and the
expansion of a strand as a phasor sum with incomplete-Γ windows are not in this file. `FocalEvent` is unchanged.
-/

open Complex Set MeasureTheory Filter Topology Asymptotics
open scoped ComplexConjugate

noncomputable section

namespace CriticalLinePhasor.HelixTwoEndedNative

open CriticalLinePhasor.GlobalHelix CriticalLinePhasor.HelixTwoEndedClosure HurwitzZeta

/-- The helix bank: the 3D Gaussian source bank, read at multiplicative height `x`. -/
def helixBank (x : ℝ) : ℂ := gaussianLattice3DBankReadout x

/-- The anti-helix bank: the bank after the global helix involution with conjugated coefficients, read at the
reflected height `1/x`. -/
def antiHelixBank (x : ℝ) : ℂ := gaussianLattice3DTransformedReadout (1 / x)

theorem helixBank_eq {x : ℝ} (hx : 0 < x) : helixBank x = (gaussianLatticeTheta x : ℂ) :=
  gaussianLattice3DBankReadout_eq x hx

theorem antiHelixBank_eq {x : ℝ} (hx : 0 < x) : antiHelixBank x = (gaussianLatticeTheta x : ℂ) := by
  unfold antiHelixBank
  rw [gaussianLattice3DTransformedReadout_eq (1 / x) (one_div_pos.mpr hx), one_div_one_div]

/-- **The helix's own reflection, on the two banks**: the compiled 3D reflection read at `1/x`. -/
theorem native_reflection {x : ℝ} (hx : 0 < x) :
    helixBank (1 / x) = ((x ^ (1 / 2 : ℝ) : ℝ) : ℂ) * antiHelixBank x := by
  have h := gaussianLattice3D_globalHelixReflection (one_div_pos.mpr hx)
  unfold helixBank antiHelixBank
  rw [h]
  congr 2
  rw [one_div x, Real.inv_rpow hx.le, one_div, inv_inv]

theorem helixBank_continuousOn : ContinuousOn helixBank (Ioi 0) :=
  (continuous_ofReal.comp_continuousOn gaussianLatticeTheta_continuousOn).congr
    fun _ hx => helixBank_eq hx

theorem antiHelixBank_continuousOn : ContinuousOn antiHelixBank (Ioi 0) :=
  (continuous_ofReal.comp_continuousOn gaussianLatticeTheta_continuousOn).congr
    fun _ hx => antiHelixBank_eq hx

/-- **The native two-ended pair**: helix bank, anti-helix bank, and the 3D reflection between them. -/
def nativePair : WeakFEPair ℂ where
  f := helixBank
  g := antiHelixBank
  k := 1 / 2
  ε := 1
  f₀ := 1
  g₀ := 1
  hf_int := helixBank_continuousOn.locallyIntegrableOn measurableSet_Ioi
  hg_int := antiHelixBank_continuousOn.locallyIntegrableOn measurableSet_Ioi
  hk := one_half_pos
  hε := one_ne_zero
  h_feq x hx := by
    rw [native_reflection hx, one_mul, smul_eq_mul]
  hf_top r := (gaussianLatticeTheta_sub_one_rapid r).congr'
    (by
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
      rw [helixBank_eq hx])
    EventuallyEq.rfl
  hg_top r := (gaussianLatticeTheta_sub_one_rapid r).congr'
    (by
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
      rw [antiHelixBank_eq hx])
    EventuallyEq.rfl

theorem nativePair_conj : ∀ x, 0 < x → nativePair.g x = conj (nativePair.f x) := fun x hx => by
  show antiHelixBank x = conj (helixBank x)
  rw [antiHelixBank_eq hx, helixBank_eq hx, Complex.conj_ofReal]

theorem nativePair_conj₀ : nativePair.g₀ = conj nativePair.f₀ := by
  simp [nativePair]

/-- The native pair and Mathlib's zero-shift even pair carry the same data at positive heights, so their completed
transforms agree. -/
theorem nativePair_Λ (s : ℂ) : nativePair.Λ s = (hurwitzEvenFEPair 0).Λ s := by
  have hfm : nativePair.f_modif = (hurwitzEvenFEPair 0).f_modif := by
    funext x
    simp only [WeakFEPair.f_modif, Pi.add_apply, Set.indicator_apply, mem_Ioi, mem_Ioo]
    by_cases hx : 0 < x
    · have h1 : nativePair.f x = (hurwitzEvenFEPair 0).f x := by
        show helixBank x = ((evenKernel 0 x : ℝ) : ℂ)
        rw [helixBank_eq hx, gaussianLatticeTheta_eq_evenKernel hx]
      rw [h1]
      simp [nativePair, hurwitzEvenFEPair]
    · have h1 : ¬ (1 : ℝ) < x := fun h => hx (zero_lt_one.trans h)
      have h2 : ¬ ((0 : ℝ) < x ∧ x < 1) := fun h => hx h.1
      simp only [h1, h2, ite_false]
  simp only [WeakFEPair.Λ, WeakFEPair.Λ₀, hfm]
  simp [nativePair, hurwitzEvenFEPair]

/-- **The completed zeta as the native two-ended sum, at every cut**: the helix bank's strand above `c` and the
anti-helix bank's strand above `1/c`, with their constant-mode bookings. -/
theorem completedRiemannZeta_native_cut {c : ℝ} (hc : 0 < c) {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    completedRiemannZeta s =
      (helixStrandAt nativePair c (s / 2) + helixStrandAt nativePair.symm c⁻¹ (1 / 2 - s / 2)
        - (c : ℂ) ^ (s / 2) / (s / 2) - (c : ℂ) ^ (s / 2 - 1 / 2) / (1 / 2 - s / 2)) / 2 := by
  have hs20 : s / 2 ≠ 0 := div_ne_zero hs0 two_ne_zero
  have hs2k : s / 2 ≠ (nativePair.k : ℂ) := by
    show s / 2 ≠ ((1 / 2 : ℝ) : ℂ)
    intro h
    apply hs1
    push_cast at h
    linear_combination 2 * h
  rw [completedRiemannZeta, completedHurwitzZetaEven, ← nativePair_Λ,
    Λ_two_ended_cut nativePair hc hs20 hs2k]
  simp only [nativePair]
  push_cast
  ring

/-- **The native two-ended closure at height `Z`, at every cut**: `ζ(½ + i·log Z) = 0` exactly when the helix
bank's end at `c` cancels the J-image of its end at `1/c`. -/
theorem riemannZeta_eq_zero_iff_native_two_ended (Z : ℝ) {c : ℝ} (hc : 0 < c) :
    riemannZeta (1 / 2 + (Real.log Z : ℂ) * I) = 0 ↔
      helixEndAt nativePair c ((1 / 2 + (Real.log Z : ℂ) * I) / 2) +
        conj (helixEndAt nativePair c⁻¹ ((1 / 2 + (Real.log Z : ℂ) * I) / 2)) = 0 := by
  set s : ℂ := 1 / 2 + (Real.log Z : ℂ) * I with hsdef
  have hs : s.re = 1 / 2 := by simp [hsdef]
  have hs0 : s ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    rw [hs] at this
    norm_num at this
  have hs20 : s / 2 ≠ 0 := div_ne_zero hs0 two_ne_zero
  have hs2 : (s / 2).re = nativePair.k / 2 := by
    rw [show nativePair.k = 1 / 2 from rfl, Complex.div_ofNat_re, hs]
  have hΓ : Gammaℝ s ≠ 0 := Gammaℝ_ne_zero_of_re_pos (by rw [hs]; norm_num)
  rw [riemannZeta_def_of_ne_zero hs0, div_eq_zero_iff, or_iff_left hΓ, completedRiemannZeta,
    completedHurwitzZetaEven, ← nativePair_Λ,
    Λ_axis_cut nativePair nativePair_conj nativePair_conj₀ hc hs2 hs20,
    show nativePair.ε = 1 from rfl, one_mul, div_eq_zero_iff, or_iff_left two_ne_zero]

end CriticalLinePhasor.HelixTwoEndedNative

end

#print axioms CriticalLinePhasor.HelixTwoEndedNative.native_reflection
#print axioms CriticalLinePhasor.HelixTwoEndedNative.nativePair
#print axioms CriticalLinePhasor.HelixTwoEndedNative.nativePair_Λ
#print axioms CriticalLinePhasor.HelixTwoEndedNative.completedRiemannZeta_native_cut
#print axioms CriticalLinePhasor.HelixTwoEndedNative.riemannZeta_eq_zero_iff_native_two_ended
