import RequestProject.XiStructureFunction
import RequestProject.SeatingFloorOdd
import RequestProject.RiemannHypothesisBridge

/-!
# The warp door IS the seat door: HB ⟺ strict seat, compiled

The identity chase from the warp's compiled components.  With
`s = ½ − iz` and the week's FE bricks (`riemannXi_one_sub`,
`xi_deriv_one_sub`, `xi_deriv_conj`):

  `Estar xiStructure z = ξ(s) − ξ′(s)`   (exactly),

so by polarization (`‖a−b‖ < ‖a+b‖ ⟺ 0 < Re(a·conj b)`),

  `IsHB xiStructure  ⟺  ∀ s, Re s > ½ → 0 < Re(ξ(s)·conj(ξ′(s)))`

— the STRICT SEAT on the right half.  The Hermite–Biehler property of the
warped structure function and the seat's sign condition are one compiled
proposition; "the warp eliminates all residue at cancellation" has exactly
this Lean form.  Composed with the compiled doors, either face forces
Mathlib's `RiemannHypothesis`.

No `sorry`, no `axiom`.
-/

open Complex ComplexConjugate Filter Topology

noncomputable section

namespace CriticalLinePhasor.XiStructure

open CriticalLinePhasor.DeBranges CriticalLinePhasor.SeatingLedger

/-- **The star of the structure function, in closed form**: the warp's
conjugate reading is exactly `ξ − ξ′` on the chart. -/
theorem estar_xiStructure (z : ℂ) :
    Estar xiStructure z
      = ZD.riemannXi (1/2 - Complex.I * z)
        - deriv ZD.riemannXi (1/2 - Complex.I * z) := by
  unfold Estar xiStructure
  rw [map_add]
  have harg : (1/2 : ℂ) - Complex.I * (starRingEnd ℂ) z
      = (starRingEnd ℂ) (1/2 + Complex.I * z) := by
    apply Complex.ext <;>
      simp [Complex.mul_re, Complex.mul_im] <;> ring
  rw [harg, ContourArgument.riemannXi_conj, xi_deriv_conj,
    Complex.conj_conj, Complex.conj_conj]
  rw [show (1/2 : ℂ) + Complex.I * z = 1 - (1/2 - Complex.I * z) by ring,
    ZD.ZeroCount.riemannXi_one_sub, xi_deriv_one_sub]
  ring

/-- Polarization: the HB inequality is the positivity of the cross term. -/
theorem norm_sub_lt_norm_add_iff (a b : ℂ) :
    ‖a - b‖ < ‖a + b‖ ↔ 0 < (a * conj b).re := by
  constructor
  · intro h
    have h2 : ‖a - b‖^2 < ‖a + b‖^2 := by
      nlinarith [norm_nonneg (a - b), norm_nonneg (a + b)]
    rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq,
      Complex.normSq_sub, Complex.normSq_add] at h2
    linarith
  · intro h
    have h2 : ‖a - b‖^2 < ‖a + b‖^2 := by
      rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq,
        Complex.normSq_sub, Complex.normSq_add]
      linarith
    nlinarith [norm_nonneg (a - b), norm_nonneg (a + b)]

/-- **The warp door is the seat door**: `IsHB xiStructure` is exactly the
strict seat sign condition right of the line. -/
theorem xiStructure_isHB_iff_strict_seat :
    IsHB xiStructure ↔
      ∀ s : ℂ, 1/2 < s.re →
        0 < (ZD.riemannXi s * conj (deriv ZD.riemannXi s)).re := by
  constructor
  · intro hHB s hs
    have him : 0 < (Complex.I * (s - 1/2)).im := by
      simp only [Complex.mul_im, Complex.I_re, Complex.I_im,
        Complex.sub_re, Complex.sub_im]
      simpa using (by linarith : (0:ℝ) < s.re - 1/2)
    have hz := hHB (Complex.I * (s - 1/2)) him
    have harg : (1/2 : ℂ) - Complex.I * (Complex.I * (s - 1/2)) = s := by
      rw [show Complex.I * (Complex.I * (s - 1/2))
          = (Complex.I * Complex.I) * (s - 1/2) by ring, Complex.I_mul_I]
      ring
    rw [estar_xiStructure, harg] at hz
    unfold xiStructure at hz
    rw [harg] at hz
    exact (norm_sub_lt_norm_add_iff _ _).mp hz
  · intro hseat z hz
    rw [estar_xiStructure]
    unfold xiStructure
    apply (norm_sub_lt_norm_add_iff _ _).mpr
    apply hseat
    simp only [Complex.sub_re, Complex.mul_re, Complex.I_re, Complex.I_im]
    simp
    linarith

/-- **Mathlib RH from the strict seat** — the warp's claim, as the one
remaining Lean form: strict positivity of `Re(ξ·conj ξ′)` right of the
line closes everything through the compiled HB door and bridge. -/
theorem riemannHypothesis_of_strict_seat
    (hseat : ∀ s : ℂ, 1/2 < s.re →
      0 < (ZD.riemannXi s * conj (deriv ZD.riemannXi s)).re) :
    RiemannHypothesis :=
  RHBridge.no_offline_zeros_implies_rh
    (rh_of_xiStructure_isHB (xiStructure_isHB_iff_strict_seat.mpr hseat))

end CriticalLinePhasor.XiStructure

#print axioms CriticalLinePhasor.XiStructure.estar_xiStructure
#print axioms CriticalLinePhasor.XiStructure.xiStructure_isHB_iff_strict_seat
#print axioms CriticalLinePhasor.XiStructure.riemannHypothesis_of_strict_seat
