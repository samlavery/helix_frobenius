import RequestProject.HolomorphicUnderIntegral

/-!
# The registration template: the anatomy of a crossing

Campaign 3 opener.  The compiled `r = 2` crossing (`rs_master` and its chain)
is dissected into its four slots, and the mechanism's vehicle is proved
abstractly, so that building a crossing at any rank reduces to filling the
slots — three of which already exist at `r = 3`.

**The bill of materials of the `r = 2` crossing** (read off `rs_master`'s own
proof):
S1, the load — the invariant rail product (`P k f`, modularity used twice;
the only slot where arithmetic enters);
S2, the kernel family — the domain-parameterized completed lattice function
with its own reflection at every point (`generalFEPair z`, Epstein/lattice
Poisson; coefficient-blind, as the vacuity theorem demands of any kernel);
S3, the unfolding — orbit parameterization plus interchange
(`gram_sum_factor`, `rs_swap`), whose diagonal collapse at two rails is
abelian Fourier orthogonality;
S4, the readout — the Mellin emergence of the `Γ`-factors and the target
series (`rankin_selberg_equation_gram`).

**The vehicle, abstractly (this file):** a load paired against a pointwise
self-reflecting kernel family inherits the reflection outright
(`pairing_reflects` — one interchange of reflection and integral), and if the
pairing is entire and unfolds to `G·L` on a right region, the target acquires
its completed continuation and functional equation
(`crossing_package`).  The arithmetic difficulty of any crossing therefore
lives **entirely in the unfolding field** — S3 — everything else is
transport.

**The `r = 3` slot map.**  S1′: the tri-rail load (definable — the triple
product of the seed's waveform on three co-hosted rails).  S2′: the rank-3
lattice completion with reflection — **compiled**
(`CarrierLatticePoisson`, `matrixTheta_inv` at rank 3).  S3′: the tri-rail
unfolding identity — the Garrett slot: the unique trilinear invariant
functional exists (bench-verified, dimension one at balanced weights, the
K-type model); its integral realization is the campaign's heart and the one
open field.  S4′: Mellin readout — machinery.  Numerical pre-verification of
any S3′ candidate is cheap on the existing bench: compute both sides at
sample points before proving.  No `axiom`, no `sorry`.
-/

open MeasureTheory Complex

namespace CriticalLinePhasor.RegistrationTemplate

variable {D : Type*} [MeasurableSpace D] (μ : Measure D)

/-- **The crossing data**: a load, a kernel family with pointwise reflection,
integrability of the pairing, and the unfolding identity on a right region.
The `unfold` field is the arithmetic heart; every other field is transport. -/
structure CrossingData where
  load : D → ℂ
  kernel : D → ℂ → ℂ
  w : ℂ
  ε : ℂ
  kernel_refl : ∀ z : D, ∀ s : ℂ, kernel z s = ε * kernel z (w - s)
  integrable : ∀ s : ℂ, Integrable (fun z => load z * kernel z s) μ
  G : ℂ → ℂ
  L : ℂ → ℂ
  σ₀ : ℝ
  unfold : ∀ s : ℂ, σ₀ < s.re →
    ∫ z, load z * kernel z s ∂μ = G s * L s

variable {μ}

/-- The pairing of the crossing. -/
noncomputable def CrossingData.pairing (X : CrossingData μ) (s : ℂ) : ℂ :=
  ∫ z, X.load z * X.kernel z s ∂μ

/-- **The vehicle, part one**: the pairing inherits the kernel family's
reflection outright — the load never interferes. -/
theorem pairing_reflects (X : CrossingData μ) (s : ℂ) :
    X.pairing s = X.ε * X.pairing (X.w - s) := by
  unfold CrossingData.pairing
  rw [← MeasureTheory.integral_const_mul]
  apply MeasureTheory.integral_congr_ae
  filter_upwards with z
  rw [X.kernel_refl z s]
  ring

/-- **The vehicle, part two**: if the pairing is entire, the crossing outputs
the completed package — an entire function with the functional equation whose
chart on the right region is `G·L`. -/
theorem crossing_package (X : CrossingData μ)
    (hF : Differentiable ℂ X.pairing) :
    ∃ F : ℂ → ℂ, Differentiable ℂ F ∧
      (∀ s : ℂ, F s = X.ε * F (X.w - s)) ∧
      (∀ s : ℂ, X.σ₀ < s.re → F s = X.G s * X.L s) :=
  ⟨X.pairing, hF, fun s => pairing_reflects X s, fun s hs => X.unfold s hs⟩

/-- The pairing's chart on the right region, in pairing form. -/
theorem chart (X : CrossingData μ) {s : ℂ} (hs : X.σ₀ < s.re) :
    X.pairing s = X.G s * X.L s :=
  X.unfold s hs

/-- The reflection forces the pairing's chart on the *left* region as well:
the completed continuation of `G·L` beyond its convergence region, with the
reflected chart `ε·(G·L)(w−s)`. -/
theorem left_chart (X : CrossingData μ) (s : ℂ)
    (hs : X.σ₀ < (X.w - s).re) :
    X.pairing s = X.ε * (X.G (X.w - s) * X.L (X.w - s)) := by
  rw [pairing_reflects X s, chart X hs]

end CriticalLinePhasor.RegistrationTemplate

#print axioms CriticalLinePhasor.RegistrationTemplate.pairing_reflects
#print axioms CriticalLinePhasor.RegistrationTemplate.crossing_package
#print axioms CriticalLinePhasor.RegistrationTemplate.left_chart
