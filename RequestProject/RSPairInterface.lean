import RequestProject.RSAveragedThetaProfile3D

/-!
# The pair-level interface: Mellin readouts and self-duality of the averaged pair

Interface lemmas at the `WeakFEPair` level for the r = 2 continuation chain, read off the two
compiled pairs — the pointwise Epstein pair `generalFEPair z` (`GeneralEpsteinZeta.lean`) and
the Petersson-averaged pair `rsAveragedWeakFEPair f hk` (`RSAveragedThetaProfile3D.lean`):

* `epstein_mellin_eq` / `epstein_mellinConvergent`: on the chart's readout locus `1 < Re s`,
  the Mellin readout of the lattice bank minus its DC channel converges and equals the
  completed Epstein kernel `Λ_z(s)`, at every point `z` of the carrier at once;
* `rsAveraged_mellin_eq` / `rsAveraged_mellinConvergent`: the same readout for the averaged
  profile — the Mellin transform of `θ̄_f − ‖f‖²` is the completed second-moment transform
  `Λ̄(s)` of the averaged pair;
* `weakFEPair_symm_eq_self` / `rsAveragedWeakFEPair_symm`: a pair whose two profiles and two
  constant terms coincide and whose root number is `1` is literally its own reflection; the
  averaged pair is such a pair;
* `rsAveraged_selfdual_FE`: hence the compiled functional equation of the averaged pair closes
  on itself — `Λ̄(1−s) = Λ̄(s)` in self-dual form, the lattice weld carried through the
  Petersson average;
* `averagedThetaC_sub_mass`: the averaged tail at carrier height `t` is the
  fundamental-domain pairing of the Petersson density with the pointwise bank tail — the
  complex form of the integrand identity compiled in `RSAveragedThetaProfile3D.lean`.

Every proof here is a projection or repackaging of the compiled pairs and their Mathlib
`WeakFEPair` machinery; the new content is the interface shape, stated once so that the
continuation files consume it by `rw`.
-/

open MeasureTheory Complex UpperHalfPlane ModularGroup Filter Set
open scoped Real MatrixGroups Topology

namespace CriticalLinePhasor.Unfolding

open CriticalLinePhasor.HeckeSupBound CriticalLinePhasor.EpsteinTheta

variable {k : ℤ}

/-! ## Mellin readout of the pointwise Epstein pair -/

/-- **The Mellin readout of the pointwise bank tail is the completed Epstein kernel** on
`1 < Re s`: the `.2` component of the abstract pair's `hasMellin`, at every `z` at once. -/
theorem epstein_mellin_eq (z : ℍ) {s : ℂ} (hs : 1 < s.re) :
    mellin (fun t : ℝ => latticeThetaC z t - 1) s = (generalFEPair z).Λ s :=
  ((generalFEPair z).hasMellin (show (generalFEPair z).k < s.re from hs)).2

/-- **The Mellin transform of the pointwise bank tail converges** on `1 < Re s`: the `.1`
component of the abstract pair's `hasMellin`. -/
theorem epstein_mellinConvergent (z : ℍ) {s : ℂ} (hs : 1 < s.re) :
    MellinConvergent (fun t : ℝ => latticeThetaC z t - 1) s :=
  ((generalFEPair z).hasMellin (show (generalFEPair z).k < s.re from hs)).1

/-! ## Mellin readout of the averaged pair -/

/-- **The Mellin readout of the averaged profile tail is the completed second-moment
transform** on `1 < Re s`: the averaged pair's `hasMellin`, `.2` component. -/
theorem rsAveraged_mellin_eq (f : CuspForm 𝒮ℒ k) (hk : 0 ≤ k) {s : ℂ} (hs : 1 < s.re) :
    mellin (fun t : ℝ => averagedThetaC k f t - ((peterssonMass k f : ℝ) : ℂ)) s =
      (rsAveragedWeakFEPair f hk).Λ s :=
  ((rsAveragedWeakFEPair f hk).hasMellin
    (show (rsAveragedWeakFEPair f hk).k < s.re from hs)).2

/-- **The Mellin transform of the averaged profile tail converges** on `1 < Re s`: the
averaged pair's `hasMellin`, `.1` component. -/
theorem rsAveraged_mellinConvergent (f : CuspForm 𝒮ℒ k) (hk : 0 ≤ k) {s : ℂ}
    (hs : 1 < s.re) :
    MellinConvergent (fun t : ℝ => averagedThetaC k f t - ((peterssonMass k f : ℝ) : ℂ)) s :=
  ((rsAveragedWeakFEPair f hk).hasMellin
    (show (rsAveragedWeakFEPair f hk).k < s.re from hs)).1

/-! ## Self-duality of the averaged pair -/

/-- A `WeakFEPair` whose two profiles coincide, whose two constant terms coincide, and whose
root number is `1` is its own reflection: `symm` swaps the equal fields and inverts the root
number, and `1⁻¹ = 1`. -/
lemma weakFEPair_symm_eq_self {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (Q : WeakFEPair E) (hfg : Q.f = Q.g) (h₀ : Q.f₀ = Q.g₀) (hε : Q.ε = 1) :
    Q.symm = Q := by
  obtain ⟨qf, qg, qk, qε, qf₀, qg₀, h1, h2, h3, h4, h5, h6, h7⟩ := Q
  have hfg' : qf = qg := hfg
  have h₀' : qf₀ = qg₀ := h₀
  have hε' : qε = 1 := hε
  subst hfg' h₀' hε'
  simp only [WeakFEPair.symm, inv_one]

/-- **The averaged pair is its own reflection**: both profiles are `θ̄_f`, both constant terms
are the Petersson mass, and the root number is `1`. -/
theorem rsAveragedWeakFEPair_symm (f : CuspForm 𝒮ℒ k) (hk : 0 ≤ k) :
    (rsAveragedWeakFEPair f hk).symm = rsAveragedWeakFEPair f hk :=
  weakFEPair_symm_eq_self _ rfl rfl rfl

/-- **The self-dual functional equation of the averaged profile**, `Λ̄(1−s) = Λ̄(s)`: the
compiled functional equation `rsAveraged_functional_equation` with its reflected pair
recognised as the pair itself.  The reflection is the lattice weld carried through the
Petersson average — no candidate equation consumed. -/
theorem rsAveraged_selfdual_FE (f : CuspForm 𝒮ℒ k) (hk : 0 ≤ k) (s : ℂ) :
    (rsAveragedWeakFEPair f hk).Λ (1 - s) = (rsAveragedWeakFEPair f hk).Λ s := by
  rw [rsAveraged_functional_equation f hk s, rsAveragedWeakFEPair_symm f hk]

/-! ## The averaged tail as a fundamental-domain pairing -/

/-- **The averaged tail is the Petersson pairing of the pointwise bank tail**: at every
carrier height `t > 0`,

  `θ̄_f(t) − ‖f‖² = ∫_𝒟 P_f(z) · (Θ_z(t) − 1)`.

This is the complex form of the integrand identity inside
`peterssonMass_le_averagedTheta`, pushed through `ofReal`; it is the identity that lets the
Mellin transform of the averaged tail be exchanged with the average. -/
theorem averagedThetaC_sub_mass (f : CuspForm 𝒮ℒ k) (hk : 0 ≤ k) {t : ℝ} (ht : 0 < t) :
    averagedThetaC k f t - ((peterssonMass k f : ℝ) : ℂ) =
      ∫ z in ModularGroup.fd, ((P k f z : ℝ) : ℂ) * (latticeThetaC z t - 1) ∂volume := by
  have hsub : averagedTheta k f t - peterssonMass k f =
      ∫ z in ModularGroup.fd, P k f z * (latticeTheta z t - 1) ∂volume := by
    unfold averagedTheta peterssonMass
    rw [← MeasureTheory.integral_sub (integrableOn_P_mul_theta f hk ht)
      (integrableOn_P_fd f)]
    refine setIntegral_congr_fun measurableSet_fd fun z _ => ?_
    ring
  unfold averagedThetaC
  rw [← Complex.ofReal_sub, hsub, ← integral_complex_ofReal]
  refine setIntegral_congr_fun measurableSet_fd fun z _ => ?_
  unfold latticeThetaC
  push_cast
  ring

end CriticalLinePhasor.Unfolding

#print axioms CriticalLinePhasor.Unfolding.epstein_mellin_eq
#print axioms CriticalLinePhasor.Unfolding.epstein_mellinConvergent
#print axioms CriticalLinePhasor.Unfolding.rsAveraged_mellin_eq
#print axioms CriticalLinePhasor.Unfolding.rsAveraged_mellinConvergent
#print axioms CriticalLinePhasor.Unfolding.weakFEPair_symm_eq_self
#print axioms CriticalLinePhasor.Unfolding.rsAveragedWeakFEPair_symm
#print axioms CriticalLinePhasor.Unfolding.rsAveraged_selfdual_FE
#print axioms CriticalLinePhasor.Unfolding.averagedThetaC_sub_mass
