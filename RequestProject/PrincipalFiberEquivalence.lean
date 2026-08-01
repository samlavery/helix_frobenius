import RequestProject.UniversalFiberEquivalence
import RequestProject.SpectralFiberIsLFunction

/-!
# Relational equality, principal character: packaging the compiled eta route

The principal capstone of the fiber-equivalence family — and, unlike its Dirichlet
and universal siblings, **every relation here was already compiled**:
`SpectralFiberIsLFunction.lean` carries the eta conduction `etaW`, the punctured-
strip readout `etaSpectralFiber_readout_tendsto_zeta`, the recovery of ζ itself
(`etaSpectralFiber_readout_recovers_zeta` — the rescaled readout of the genuine
`Vec3` spectral fiber converges to `riemannZeta` wherever the conduction factor is
invertible), and `riemannZeta_eq_principal_LFunction`.  This file only packages
those theorems in the family's structure shape and adds the uniqueness-core
application (`eta_entire_reading_unique` — at most one entire reading, the
identity-theorem core on the punctured strip).

The pole is booked as geometry: the conduction factor `1 − 2^{1−s}` vanishes
exactly at the pole site `s = 1` (`pole_booked`), and the alternating conduction
cancels exactly per adjacent pair (`conduction_window` — the principal fiber's
window-zero).

Proven in this file: the packaging instance and the uniqueness application,
unconditionally; all analytic content is consumed from
`SpectralFiberIsLFunction.lean`, cited not re-proved.  The completed-`Λ`-level
functional-equation intertwining is the main paper's compiled content.
-/

open Complex Filter Topology

namespace CriticalLinePhasor.FiberEquivalence

open CriticalLinePhasor.SpectralFiber
open CriticalLinePhasor.CarrierTargetIdentification

/-- The eta fiber's partial readout: the first `N` spectral-fiber readout terms. -/
noncomputable def etaPartialReadout (s : ℂ) (N : ℕ) : ℂ :=
  ∑ n ∈ Finset.range N, readout etaW s n

/-- **At most one entire reading of the eta fiber exists** — the identity-theorem
core on the punctured strip. -/
theorem eta_entire_reading_unique {G G' : ℂ → ℂ}
    (hG : Differentiable ℂ G) (hG' : Differentiable ℂ G')
    (hreadG : ∀ s : ℂ, 0 < s.re → s ≠ 1 →
      Tendsto (etaPartialReadout s) atTop (𝓝 (G s)))
    (hreadG' : ∀ s : ℂ, 0 < s.re → s ≠ 1 →
      Tendsto (etaPartialReadout s) atTop (𝓝 (G' s))) :
    G = G' := by
  have hU : IsOpen ({z : ℂ | 0 < z.re} \ {1}) :=
    (isOpen_lt continuous_const continuous_re).sdiff isClosed_singleton
  have h2 : (2 : ℂ) ∈ ({z : ℂ | 0 < z.re} \ {1}) := by
    constructor
    · norm_num
    · norm_num
  refine entire_eq_of_eqOn_isOpen hG hG' hU h2 ?_
  intro s hsU
  exact tendsto_nhds_unique (hreadG s hsU.1 (by simpa using hsU.2))
    (hreadG' s hsU.1 (by simpa using hsU.2))

/-- **Relational equality, principal character** — the packaged structure: exact
per-cell alternating conduction, punctured-strip readout of the pole-free product,
recovery of ζ itself from the rescaled fiber readout, uniqueness of the entire
reading, identification of ζ with the principal L-function, and the pole booked as
the conduction factor's zero. -/
structure PrincipalFiberEquivalence : Prop where
  conduction_window : ∀ n : ℕ, etaW n + etaW (n + 1) = 0
  readout_eq : ∀ s : ℂ, 0 < s.re → s ≠ 1 →
    Tendsto (etaPartialReadout s) atTop
      (𝓝 ((1 - (2 : ℂ) ^ (1 - s)) * riemannZeta s))
  zeta_recovered : ∀ s : ℂ, 0 < s.re → s ≠ 1 →
    (1 : ℂ) - 2 ^ (1 - s) ≠ 0 →
    Tendsto (fun N => ((1 - (2 : ℂ) ^ (1 - s))⁻¹) * etaPartialReadout s N) atTop
      (𝓝 (riemannZeta s))
  reading_unique : ∀ G G' : ℂ → ℂ, Differentiable ℂ G → Differentiable ℂ G' →
    (∀ s : ℂ, 0 < s.re → s ≠ 1 →
      Tendsto (etaPartialReadout s) atTop (𝓝 (G s))) →
    (∀ s : ℂ, 0 < s.re → s ≠ 1 →
      Tendsto (etaPartialReadout s) atTop (𝓝 (G' s))) → G = G'
  principal_is_zeta : ∀ χ : DirichletCharacter ℂ 1,
    riemannZeta = DirichletCharacter.LFunction χ
  pole_booked : (1 : ℂ) - 2 ^ ((1 : ℂ) - 1) = 0

/-- **The principal instance, unconditional** — every field consumed from the
compiled corpus. -/
theorem principalFiberEquivalence : PrincipalFiberEquivalence where
  conduction_window := by
    intro n
    show (-1 : ℂ) ^ (n + 1) + (-1 : ℂ) ^ (n + 1 + 1) = 0
    rw [pow_succ (-1 : ℂ) (n + 1)]
    ring
  readout_eq := fun _ hs hs1 => etaSpectralFiber_readout_tendsto_zeta hs hs1
  zeta_recovered := fun _ hs hs1 hfac =>
    etaSpectralFiber_readout_recovers_zeta hs hs1 hfac
  reading_unique := fun _ _ hG hG' hr hr' =>
    eta_entire_reading_unique hG hG' hr hr'
  principal_is_zeta := riemannZeta_eq_principal_LFunction
  pole_booked := by norm_num

end CriticalLinePhasor.FiberEquivalence

#print axioms CriticalLinePhasor.FiberEquivalence.eta_entire_reading_unique
#print axioms CriticalLinePhasor.FiberEquivalence.principalFiberEquivalence
