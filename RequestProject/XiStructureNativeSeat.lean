import RequestProject.XiStructureHBSeat

/-!
# The native-domain form: the leaf on `Re s > 0`

The helix geometry's domain is `Re s > 0` (`native_domain_iff`; the entry
wall is `Re s = 0`; the ordered readout is compiled there).  The strict
right-half seat is chart-shaped — it privileges one bank of the carrier's
projection.  Native form: the cross term `Re(ξ·conj ξ′)` is exactly ODD
under the mirror `s ↦ 1−s̄` (compiled below), so the single statement over
the whole native domain is the signed/even form

  `0 < (σ−½)·Re(ξ(s)·conj(ξ′(s)))`   for `0 < σ`, `σ ≠ ½`,

equivalent to `IsHB xiStructure`, hence to every other face, hence closing
Mathlib's `RiemannHypothesis`.  This is the leaf stated where the warp's
instruments live.

No `sorry`, no `axiom`.
-/

open Complex ComplexConjugate Filter Topology

noncomputable section

namespace CriticalLinePhasor.XiStructure

open CriticalLinePhasor.DeBranges CriticalLinePhasor.SeatingLedger

/-- **The cross term is exactly odd under the FE mirror** at fixed height. -/
theorem cross_mirror (s : ℂ) :
    (ZD.riemannXi (1 - conj s) * conj (deriv ZD.riemannXi (1 - conj s))).re
      = -(ZD.riemannXi s * conj (deriv ZD.riemannXi s)).re := by
  have h2 : deriv ZD.riemannXi (1 - conj s)
      = -conj (deriv ZD.riemannXi s) := by
    rw [xi_deriv_one_sub (conj s), xi_deriv_conj]
  rw [ContourArgument.riemannXi_one_sub_conj, h2, map_neg, Complex.conj_conj,
    mul_neg, Complex.neg_re]
  have hswap : conj (ZD.riemannXi s) * deriv ZD.riemannXi s
      = conj (ZD.riemannXi s * conj (deriv ZD.riemannXi s)) := by
    rw [map_mul, Complex.conj_conj]
  rw [hswap, Complex.conj_re]

/-- **The native-domain seat**: `IsHB xiStructure` is the signed cross-term
positivity over the whole helix domain `Re s > 0`, off the carrier
projection. -/
theorem xiStructure_isHB_iff_native_seat :
    IsHB xiStructure ↔
      ∀ s : ℂ, 0 < s.re → s.re ≠ 1/2 →
        0 < (s.re - 1/2)
          * (ZD.riemannXi s * conj (deriv ZD.riemannXi s)).re := by
  rw [xiStructure_isHB_iff_strict_seat]
  constructor
  · intro hR s hs0 hsne
    rcases lt_or_gt_of_ne hsne with hlt | hgt
    · have hmre : (1/2 : ℝ) < (1 - conj s).re := by
        simp only [Complex.sub_re, Complex.one_re, Complex.conj_re]
        linarith
      have hmir := hR (1 - conj s) hmre
      rw [cross_mirror] at hmir
      exact mul_pos_of_neg_of_neg (by linarith) (by linarith)
    · exact mul_pos (by linarith) (hR s hgt)
  · intro hN s hs
    have h := hN s (by linarith) (by linarith)
    nlinarith

/-- **Mathlib RH from the native seat** — the leaf in its helix-native
form: signed cross-term positivity on `Re s > 0` closes everything. -/
theorem riemannHypothesis_of_native_seat
    (h : ∀ s : ℂ, 0 < s.re → s.re ≠ 1/2 →
      0 < (s.re - 1/2)
        * (ZD.riemannXi s * conj (deriv ZD.riemannXi s)).re) :
    RiemannHypothesis :=
  RHBridge.no_offline_zeros_implies_rh
    (rh_of_xiStructure_isHB (xiStructure_isHB_iff_native_seat.mpr h))

end CriticalLinePhasor.XiStructure

#print axioms CriticalLinePhasor.XiStructure.cross_mirror
#print axioms CriticalLinePhasor.XiStructure.xiStructure_isHB_iff_native_seat
#print axioms CriticalLinePhasor.XiStructure.riemannHypothesis_of_native_seat
