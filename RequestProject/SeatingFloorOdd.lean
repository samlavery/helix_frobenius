import RequestProject.SeatingHighSign

/-!
# The floor's odd symmetry: the factorization normal form

The valley floor `F(s) = Re[ξ′/ξ(s)]` is exactly odd under `s ↦ 1−s`:
compiled from the plain functional equation `ξ(1−s) = ξ(s)`
(`ZD.ZeroCount.riemannXi_one_sub`, in-tree) by the chain rule.  This is the
normal form behind the measured mass factorization `F = (σ−½)·M` with `M`
even (measured: M = Poisson-smoothed zero density, tmp/att547): the floor
vanishes identically on the line, and the seat door's content is the SIGN
of the even factor alone.

No `sorry`, no `axiom`.
-/

open Complex ComplexConjugate Filter Topology

noncomputable section

namespace CriticalLinePhasor.SeatingLedger

/-- The ξ derivative is exactly odd about the center. -/
theorem xi_deriv_one_sub (s : ℂ) :
    deriv ZD.riemannXi (1 - s) = -deriv ZD.riemannXi s := by
  have h1 : HasDerivAt (fun w : ℂ => 1 - w) (-1) s :=
    (hasDerivAt_id s).const_sub 1
  have h2 : HasDerivAt ZD.riemannXi (deriv ZD.riemannXi (1 - s)) (1 - s) :=
    (ZD.riemannXi_differentiable (1 - s)).hasDerivAt
  have h3 : HasDerivAt (fun w : ℂ => ZD.riemannXi (1 - w))
      (deriv ZD.riemannXi (1 - s) * (-1)) s := h2.comp s h1
  have h4 : (fun w : ℂ => ZD.riemannXi (1 - w)) = ZD.riemannXi :=
    funext fun w => ZD.ZeroCount.riemannXi_one_sub w
  rw [h4] at h3
  have h5 := h3.deriv
  linear_combination h5

/-- **The log-derivative is exactly odd about the center** — the functional
equation read at the level of the seat field. -/
theorem xiLogDeriv_odd (s : ℂ) :
    logDeriv ZD.riemannXi (1 - s) = -logDeriv ZD.riemannXi s := by
  rw [logDeriv_apply, logDeriv_apply, xi_deriv_one_sub,
    ZD.ZeroCount.riemannXi_one_sub]
  ring

/-- **The valley floor is exactly odd about the center** (real register):
`F(1−s) = −F(s)`.  Corollary: `F` vanishes identically at the fixed line of
`s ↦ 1−s̄`; the seat door's content is the sign of the even factor `M` in
`F = (σ−½)·M` alone. -/
theorem floor_odd (s : ℂ) :
    (logDeriv ZD.riemannXi (1 - s)).re = -(logDeriv ZD.riemannXi s).re := by
  rw [xiLogDeriv_odd]
  simp

/-- The ξ derivative is conjugation-equivariant (antiholomorphic transfer,
`HasDerivAt.conj_conj`). -/
theorem xi_deriv_conj (s : ℂ) :
    deriv ZD.riemannXi (conj s) = conj (deriv ZD.riemannXi s) := by
  have h2 : HasDerivAt ZD.riemannXi (deriv ZD.riemannXi s) s :=
    (ZD.riemannXi_differentiable s).hasDerivAt
  have h3 := h2.conj_conj
  have h4 : (⇑(starRingEnd ℂ) ∘ ZD.riemannXi ∘ ⇑(starRingEnd ℂ))
      = ZD.riemannXi := by
    funext w
    simp only [Function.comp_apply]
    rw [ContourArgument.riemannXi_conj, Complex.conj_conj]
  rw [h4] at h3
  exact h3.deriv

/-- The log-derivative is conjugation-equivariant. -/
theorem xiLogDeriv_conj (s : ℂ) :
    logDeriv ZD.riemannXi (conj s) = conj (logDeriv ZD.riemannXi s) := by
  rw [logDeriv_apply, logDeriv_apply, xi_deriv_conj,
    ContourArgument.riemannXi_conj, ← map_div₀]

/-- **The σ-mirror at fixed height** — the mass normal form: for
`s = σ + it`, the point `1 − s̄ = (1−σ) + it` carries the opposite floor,
`F(1−σ, t) = −F(σ, t)`.  Hence `F` vanishes identically at `σ = ½` and
factors through the odd part of `σ − ½`; the seat door is the sign of the
even factor `M` alone (measured: `M` = Poisson-smoothed zero density,
`tmp/att547_mass_probe.py`). -/
theorem floor_mirror (s : ℂ) :
    (logDeriv ZD.riemannXi (1 - conj s)).re
      = -(logDeriv ZD.riemannXi s).re := by
  rw [xiLogDeriv_odd, xiLogDeriv_conj]
  simp

end CriticalLinePhasor.SeatingLedger

#print axioms CriticalLinePhasor.SeatingLedger.xiLogDeriv_odd
#print axioms CriticalLinePhasor.SeatingLedger.floor_odd
#print axioms CriticalLinePhasor.SeatingLedger.floor_mirror
