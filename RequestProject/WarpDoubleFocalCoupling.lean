import RequestProject.TwoEndedGrownState
import RequestProject.CarrierBank
import RequestProject.ThreeDFocalEvent

/-!
# Same-height warp and the double focal event: the coupling test (ledger 912)

At carrier height `y` (the ordinate of the helix height), the dynamic warp is the heat semigroup
`e^{−sH}` at `s = carrierPoint y` (`CarrierReadout.heat`), and the four physical banks are the
positive/negative channels of the grown fiber at the physical head (`TwoEndedGrownState`) together
with their J-images.  No functional equation, no census, no free abscissa.

* A (one height, three constructions): the END+ channels are head-window sums of the warp's own
  diagonal matrix elements (`positiveChannel_eq_warp`, `negativeChannel_eq_warp`); END− is their
  conjugate (`Pminus`, `Mminus`).
* E/F (phase and radius provenance): the warp's matrix element on site `n` is the unitary height flow
  `e^{−iy·logWeight n}` times a radial weight whose length is `(n+1)^{−carrierAbscissa}` at every height
  (`warpElement_flow`, `warpElement_norm`).
* C/I: `DoubleFocal y ↔ Rplus y = 0` (`doubleFocal_iff`) — the second end adds no equation.
* H: the J-odd combination of the two ends vanishes identically (`paired_odd`); the J-even one is
  twice a single residual (`paired_even_iff`); the sum/difference of the ends are the real and imaginary
  parts of one residual (`ends_add`, `ends_sub`).
* G: the height-derivatives of the two ends are conjugate (`hasDerivAt_ends`).

No `sorry`, no `axiom`.
-/

noncomputable section
open Complex Finset

namespace CriticalLinePhasor.WarpDoubleFocal

open CarrierReadout CriticalLinePhasor.ThreeDFocal CriticalLinePhasor.TwoEndedGrownState
  CriticalLinePhasor.GrownFiberEvolution CriticalLinePhasor.CarrierHeadFiniteFiber

/-! ## A. One height, three constructions -/

/-- The dynamic warp at height `y`: the heat semigroup at the carrier point of `y`. -/
def warp (y : ℝ) := heat (carrierPoint y)

/-- The warp's diagonal matrix element on the `n`-th site phasor. -/
def warpElement (y : ℝ) (n : ℕ) : ℂ :=
  inner ℂ (phasor n) (warp y ⟨phasor n, phasor_mem_cweightDomain _ n⟩ : L2)

/-- The matrix element, computed from the operator. -/
theorem warpElement_eq (y : ℝ) (n : ℕ) :
    warpElement y n = ((n : ℂ) + 1) ^ (-carrierPoint y) :=
  inner_phasor_heat _ n

/-- **END+ positive bank = window-weighted warp elements on the odd sites.** -/
theorem positiveChannel_eq_warp (y : ℝ) (N : ℕ) :
    positiveChannel (physicalHead y) (carrierPoint y) N =
      ∑ j ∈ range N, ((headWindow (physicalHead y) (2 * j) : ℝ) : ℂ) * warpElement y (2 * j) := by
  unfold positiveChannel
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [warpElement_eq]

/-- **END+ negative bank = window-weighted warp elements on the even sites.** -/
theorem negativeChannel_eq_warp (y : ℝ) (N : ℕ) :
    negativeChannel (physicalHead y) (carrierPoint y) N =
      ∑ j ∈ range N, ((headWindow (physicalHead y) (2 * j + 1) : ℝ) : ℂ) *
        warpElement y (2 * j + 1) := by
  unfold negativeChannel
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [warpElement_eq]

/-- The END− banks: the physical J-images (conjugates) of the END+ banks, same head and window. -/
def Pminus (y : ℝ) (N : ℕ) : ℂ := (starRingEnd ℂ) (positiveChannel (physicalHead y) (carrierPoint y) N)

def Mminus (y : ℝ) (N : ℕ) : ℂ := (starRingEnd ℂ) (negativeChannel (physicalHead y) (carrierPoint y) N)

/-! ## E/F. Phase and radius of the warp element -/

/-- **Phase provenance**: the warp element is the unitary height flow `e^{−iy·logWeight n}` of the
carrier Hamiltonian applied to the warp element at height `0`. -/
theorem warpElement_flow (y : ℝ) (n : ℕ) :
    warpElement y n = Complex.exp (-(Complex.I * y) * (logWeight n : ℂ)) * warpElement 0 n := by
  rw [warpElement_eq, warpElement_eq, ← heat_eigenvalue_eq_exp]
  have hsplit : carrierPoint y = carrierPoint 0 + Complex.I * (y : ℂ) := by
    simp [carrierPoint]
  rw [hsplit]
  exact CarrierReadout.bank_flow (carrierPoint 0) (Complex.I * (y : ℂ)) n

/-- **Radius**: the length of the warp element is `(n+1)^{−carrierAbscissa}` at every height. -/
theorem warpElement_norm (y : ℝ) (n : ℕ) :
    ‖warpElement y n‖ = ((n : ℝ) + 1) ^ (-carrierAbscissa) := by
  rw [warpElement_eq]
  have hc : ((n : ℂ) + 1) = (((n : ℝ) + 1 : ℝ) : ℂ) := by push_cast; rfl
  rw [hc, Complex.norm_cpow_eq_rpow_re_of_pos (by positivity)]
  simp [carrierPoint]

/-- The flow factor has length one: the whole radial content sits in the height-`0` element. -/
theorem norm_flow (y : ℝ) (n : ℕ) :
    ‖Complex.exp (-(Complex.I * y) * (logWeight n : ℂ))‖ = 1 := by
  rw [Complex.norm_exp]
  simp [Complex.mul_re]

/-! ## C/I. The double focal event -/

/-- The END+ residual at height `y`: the grown fiber at the physical head and the carrier point. -/
def Rplus (y : ℝ) : ℂ := finiteFiber (physicalHead y) (carrierPoint y)

/-- The END− residual: the physical J-image of the END+ residual. -/
def Rminus (y : ℝ) : ℂ := (starRingEnd ℂ) (Rplus y)

/-- The residual of each end is its own P/M closure. -/
theorem Rplus_eq_P_sub_M (y : ℝ) {N : ℕ} (hN : ⌈physicalHead y⌉₊ ≤ 2 * N) :
    Rplus y = positiveChannel (physicalHead y) (carrierPoint y) N -
      negativeChannel (physicalHead y) (carrierPoint y) N := by
  have hZ : 0 < physicalHead y := lt_of_lt_of_le (by positivity) (physicalHead_lower y)
  exact finiteFiber_eq_P_sub_M hZ _ hN

theorem Rminus_eq_P_sub_M (y : ℝ) {N : ℕ} (hN : ⌈physicalHead y⌉₊ ≤ 2 * N) :
    Rminus y = Pminus y N - Mminus y N := by
  rw [Rminus, Rplus_eq_P_sub_M y hN, map_sub]
  rfl

/-- The physical double focal event: both ends close on their own P/M lanes. -/
def DoubleFocal (y : ℝ) : Prop := Rminus y = 0 ∧ Rplus y = 0

/-- **The second end adds no equation**: the double event is the single END+ closure. -/
theorem doubleFocal_iff (y : ℝ) : DoubleFocal y ↔ Rplus y = 0 := by
  unfold DoubleFocal Rminus
  constructor
  · rintro ⟨_, h⟩
    exact h
  · intro h
    exact ⟨by rw [h, map_zero], h⟩

/-! ## H. Two-end combinations -/

/-- The J-odd combination of the two ends vanishes identically. -/
theorem paired_odd (y : ℝ) : Rminus y - (starRingEnd ℂ) (Rplus y) = 0 := sub_self _

/-- The J-even combination is twice one residual: it vanishes exactly at a single-end closure. -/
theorem paired_even_iff (y : ℝ) : Rminus y + (starRingEnd ℂ) (Rplus y) = 0 ↔ Rplus y = 0 := by
  unfold Rminus
  rw [← two_mul, mul_eq_zero, map_eq_zero]
  simp

/-- The sum of the two ends is twice the real part of one residual. -/
theorem ends_add (y : ℝ) : Rplus y + Rminus y = ((2 * (Rplus y).re : ℝ) : ℂ) := by
  unfold Rminus
  rw [Complex.add_conj]

/-- The difference of the two ends is `2i` times the imaginary part of one residual. -/
theorem ends_sub (y : ℝ) : Rplus y - Rminus y = 2 * Complex.I * ((Rplus y).im : ℂ) := by
  unfold Rminus
  rw [Complex.sub_conj]
  push_cast
  ring

/-! ## G. Height derivatives of the two ends -/

/-- The END+ residual is the compiled carrier state at the carrier abscissa. -/
theorem Rplus_eq_carrierState (y : ℝ) : Rplus y = carrierState carrierAbscissa y := rfl

/-- **The two ends have conjugate height-derivatives** (the END+ derivative is the explicit
supply + rotation expression of `hasDerivAt_carrierState`). -/
theorem hasDerivAt_ends (y : ℝ) :
    ∃ D : ℂ, HasDerivAt Rplus D y ∧ HasDerivAt Rminus ((starRingEnd ℂ) D) y := by
  obtain ⟨D, hD⟩ : ∃ D, HasDerivAt (fun y : ℝ => carrierState carrierAbscissa y) D y :=
    ⟨_, hasDerivAt_carrierState carrierAbscissa y⟩
  exact ⟨D, hD, hD.star⟩

end CriticalLinePhasor.WarpDoubleFocal

#print axioms CriticalLinePhasor.WarpDoubleFocal.warpElement_eq
#print axioms CriticalLinePhasor.WarpDoubleFocal.positiveChannel_eq_warp
#print axioms CriticalLinePhasor.WarpDoubleFocal.negativeChannel_eq_warp
#print axioms CriticalLinePhasor.WarpDoubleFocal.warpElement_flow
#print axioms CriticalLinePhasor.WarpDoubleFocal.warpElement_norm
#print axioms CriticalLinePhasor.WarpDoubleFocal.norm_flow
#print axioms CriticalLinePhasor.WarpDoubleFocal.Rplus_eq_P_sub_M
#print axioms CriticalLinePhasor.WarpDoubleFocal.Rminus_eq_P_sub_M
#print axioms CriticalLinePhasor.WarpDoubleFocal.doubleFocal_iff
#print axioms CriticalLinePhasor.WarpDoubleFocal.paired_odd
#print axioms CriticalLinePhasor.WarpDoubleFocal.paired_even_iff
#print axioms CriticalLinePhasor.WarpDoubleFocal.ends_add
#print axioms CriticalLinePhasor.WarpDoubleFocal.ends_sub
#print axioms CriticalLinePhasor.WarpDoubleFocal.hasDerivAt_ends
