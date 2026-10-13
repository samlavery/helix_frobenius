import RequestProject.HelixWindowCompletion

/-!
# The window completion on the helix (ledger 1258)

Ledger 1257 built the head fiber's tail from scalar banks. Here every bank is a readout of points on the 3D
helix, and the reflection is the global helix involution.

**Heights.**
* `Z`: the event's physical height. Its chart readout is `log Z`, its exponent `s = σ + i·log Z`.
* `N`: the head, i.e. how many sites the fiber has grown. At the event `N = physicalHead (log Z) ≈ 9Z²`.
* `x`: the height along the helix at which a bank's sites are read (site `n` at `n²x`); the strands integrate it.
* `c`: the cut, a bank height. The anti-helix cut is `1/c`; in helix height `log c ↔ -log c`, the
  reflection about the origin.
`Z` enters twice: through the head `N`, and through the spin. The Mellin weight `x^{s/2}` turns by `(log Z)/2`
per unit of helix height.
The closure at the event's height is `helix_closure_at_height`.

* `headFiber N n x`: site `n ∈ ℤ` of the event's head as a helix point
  `(‖aₙ‖, arg aₙ, log(Hₙx))`, with `aₙ = (-1)^{|n|} φ(|n|/N)` (`φ = smoothEntry`, so `a₀ = 1`) and the house's
  Gaussian source heights `Hₙ = n²` (`H₀ = 1`, the zero mode as its own channel; `gaussianLatticeHeight`).
  `headBank3D N x`: the readout `Σₙ fiberPhasor · kernel(multiplicativeHeight)`. This is the construction of
  `gaussianLattice3DBankReadout`, with the head's coefficients in place of `1`.
* `antiFiber N n x`: the same site after `globalHelixInvolution` `(r, θ, h) ↦ (r, -θ, -h)` and the exact
  height shear (`indexedReciprocalCoefficientFiber`, conjugated data). `headAntiBank3D N x` is its readout.
* Projections: `headBank3D_eq : headBank3D N x = windowBank N x`, and
  `headAntiBank3D_eq : headAntiBank3D N x = windowBank N (1/x)`. The anti-helix carries the head's sites at
  reflected height.
* `helixTail N c s`: the tail, now from four helix banks: the head bank and the η bank above the cut, and the
  reflected head bank and the η anti-helix bank (`etaHelixBank`, `etaAntiHelixBank`, ledger 1255) above the
  reflected cut.
* `helix_completion`: for `Re s > 0`, `s ≠ 1`, every head `N > 0` and every cut `c > 0`,
  `finiteFiber N s + helixTail N c s = (1 - 2^{1-s})·ζ(s)`. `helixTail_eq_windowTail` identifies it with 1257.
* In helix height `h = log x` (`upper3D_height`, `lower3D_height`): the helix correction integrates heights above
  `log c`; the anti-helix correction integrates heights above `-log c`, the cut reflected about the origin `h = 0`.
* `headSum_helix_completion`, `head_helix_closure_iff`: the arrows into `FocalEvent`'s channel `headSum`, as in
  1257, now with the helix tail.
-/

open Complex Set MeasureTheory Filter Topology
open scoped ComplexConjugate

noncomputable section

namespace CriticalLinePhasor.HelixWindowCompletion3D

open CriticalLinePhasor CriticalLinePhasor.CarrierHeadFiniteFiber CriticalLinePhasor.HelixTwoEndedEta
  CriticalLinePhasor.GlobalHelix CriticalLinePhasor.HelixWindowCompletion ConeProjection

/-! ## The head's sites on the helix -/

/-- The head's coefficient at site `n ∈ ℤ`: `(-1)^{|n|} φ(|n|/Z)`. -/
def headCoeffInt (N : ℝ) (n : ℤ) : ℂ :=
  (-1 : ℂ) ^ n.natAbs * (smoothEntry ((n.natAbs : ℝ) / N) : ℂ)

theorem smoothEntry_zero' : smoothEntry 0 = 1 := by
  unfold smoothEntry
  norm_num

theorem smoothEntry_ge_one {u : ℝ} (hu : 1 ≤ u) : smoothEntry u = 0 := by
  unfold smoothEntry
  simp only [not_lt.mpr hu, ↓reduceIte]

theorem headCoeffInt_zero (N : ℝ) : headCoeffInt N 0 = 1 := by
  simp [headCoeffInt, smoothEntry_zero']

theorem headCoeffInt_succ (N : ℝ) (k : ℕ) : headCoeffInt N ((k + 1 : ℕ) : ℤ) = -headCoeff N k := by
  unfold headCoeffInt headCoeff
  rw [Int.natAbs_natCast, pow_succ]
  ring

theorem headCoeffInt_neg_succ (N : ℝ) (k : ℕ) : headCoeffInt N (-((k : ℤ) + 1)) = -headCoeff N k := by
  have h : (-((k : ℤ) + 1)).natAbs = k + 1 := by omega
  unfold headCoeffInt headCoeff
  rw [h, pow_succ]
  push_cast
  ring

/-- Site `n` of the head as a point on the helix. -/
def headFiber (N : ℝ) (n : ℤ) (x : ℝ) : Fiber :=
  indexedCoefficientFiber (headCoeffInt N) gaussianLatticeHeight n x

/-- **The head bank on the helix**: the readout of the head's helix points. -/
def headBank3D (N x : ℝ) : ℂ :=
  ∑' n : ℤ, fiberPhasor (headFiber N n x) *
    gaussianLatticeKernelTerm n (multiplicativeHeight (headFiber N n x))

/-- Site `n` of the head after the global helix involution and the exact height shear. -/
def antiFiber (N : ℝ) (n : ℤ) (x : ℝ) : Fiber :=
  indexedReciprocalCoefficientFiber (fun j => conj (headCoeffInt N j)) gaussianLatticeHeight n x

/-- **The anti-helix bank of the head**: the readout of the involuted helix points. -/
def headAntiBank3D (N x : ℝ) : ℂ :=
  ∑' n : ℤ, fiberPhasor (antiFiber N n x) *
    gaussianLatticeKernelTerm n (multiplicativeHeight (antiFiber N n x))

/-- The common scalar term: site `n` read at external height `t`. -/
def bankTerm (N : ℝ) (n : ℤ) (t : ℝ) : ℂ :=
  headCoeffInt N n * gaussianLatticeKernelTerm n (gaussianLatticeHeight n * t)

theorem headBank3D_term {N x : ℝ} (hx : 0 < x) (n : ℤ) :
    fiberPhasor (headFiber N n x) * gaussianLatticeKernelTerm n (multiplicativeHeight (headFiber N n x)) =
      bankTerm N n x := by
  unfold headFiber bankTerm
  rw [fiberPhasor_indexedCoefficientFiber,
    multiplicativeHeight_indexedCoefficientFiber _ _ gaussianLatticeHeight_pos n hx]

theorem headAntiBank3D_term {N x : ℝ} (hx : 0 < x) (n : ℤ) :
    fiberPhasor (antiFiber N n x) * gaussianLatticeKernelTerm n (multiplicativeHeight (antiFiber N n x)) =
      bankTerm N n (1 / x) := by
  unfold antiFiber bankTerm
  rw [fiberPhasor_indexedReciprocalCoefficientFiber_conj,
    multiplicativeHeight_indexedReciprocalCoefficientFiber _ _ gaussianLatticeHeight_pos n hx]
  congr 2
  ring

/-- The kernel of a nonzero site is the Gaussian at the site's height rate. -/
theorem bankTerm_succ (N : ℝ) (k : ℕ) (t : ℝ) :
    bankTerm N ((k + 1 : ℕ) : ℤ) t = -(headCoeff N k * ((Real.exp (-siteRate k * t) : ℝ) : ℂ)) := by
  have hne : ((k + 1 : ℕ) : ℤ) ≠ 0 := by omega
  unfold bankTerm gaussianLatticeKernelTerm gaussianLatticeHeight
  simp only [hne, ↓reduceIte]
  rw [headCoeffInt_succ, siteRate]
  push_cast
  ring_nf

theorem bankTerm_neg_succ (N : ℝ) (k : ℕ) (t : ℝ) :
    bankTerm N (-((k : ℤ) + 1)) t = -(headCoeff N k * ((Real.exp (-siteRate k * t) : ℝ) : ℂ)) := by
  have hne : (-((k : ℤ) + 1)) ≠ 0 := by omega
  unfold bankTerm gaussianLatticeKernelTerm gaussianLatticeHeight
  simp only [hne, ↓reduceIte]
  rw [headCoeffInt_neg_succ, siteRate]
  push_cast
  ring_nf

theorem headCoeff_eq_zero {N : ℝ} (hN : 0 < N) {k : ℕ} (hk : ⌈N⌉₊ ≤ k) : headCoeff N k = 0 := by
  have h1 : N ≤ ((k + 1 : ℕ) : ℝ) := by
    have := Nat.le_ceil N
    have h2 : (⌈N⌉₊ : ℝ) ≤ k := by exact_mod_cast hk
    push_cast
    linarith
  unfold headCoeff
  rw [smoothEntry_ge_one ((one_le_div hN).mpr h1)]
  simp

/-- **The head bank's sites sum to the scalar bank**, at every height. -/
theorem hasSum_bankTerm {N : ℝ} (hN : 0 < N) (t : ℝ) : HasSum (fun n : ℤ => bankTerm N n t) (windowBank N t) := by
  have hpos0 : HasSum (fun n : ℕ => bankTerm N (n : ℤ) t)
      (∑ n ∈ Finset.range (⌈N⌉₊ + 1), bankTerm N (n : ℤ) t) := by
    apply hasSum_sum_of_ne_finset_zero
    intro n hn
    rw [Finset.mem_range, not_lt] at hn
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    rw [bankTerm_succ, headCoeff_eq_zero hN (by omega), zero_mul, neg_zero]
  have hneg0 : HasSum (fun n : ℕ => bankTerm N (-((n : ℤ) + 1)) t)
      (∑ n ∈ Finset.range ⌈N⌉₊, bankTerm N (-((n : ℤ) + 1)) t) := by
    apply hasSum_sum_of_ne_finset_zero
    intro n hn
    rw [Finset.mem_range, not_lt] at hn
    rw [bankTerm_neg_succ, headCoeff_eq_zero hN hn, zero_mul, neg_zero]
  have h0 : bankTerm N ((0 : ℕ) : ℤ) t = 1 := by
    unfold bankTerm gaussianLatticeKernelTerm
    simp [headCoeffInt_zero]
  have hval : windowBank N t = (∑ n ∈ Finset.range (⌈N⌉₊ + 1), bankTerm N (n : ℤ) t)
      + ∑ n ∈ Finset.range ⌈N⌉₊, bankTerm N (-((n : ℤ) + 1)) t := by
    rw [Finset.sum_range_succ', h0, Finset.sum_congr rfl fun k _ => bankTerm_succ N k t,
      Finset.sum_congr rfl fun k _ => bankTerm_neg_succ N k t, Finset.sum_neg_distrib]
    unfold windowBank
    ring
  rw [hval]
  exact HasSum.of_nat_of_neg_add_one (f := fun n : ℤ => bankTerm N n t) hpos0 hneg0

theorem headBank3D_eq {N x : ℝ} (hN : 0 < N) (hx : 0 < x) : headBank3D N x = windowBank N x := by
  unfold headBank3D
  simp_rw [headBank3D_term hx]
  exact (hasSum_bankTerm hN x).tsum_eq

theorem headAntiBank3D_eq {N x : ℝ} (hN : 0 < N) (hx : 0 < x) : headAntiBank3D N x = windowBank N (1 / x) := by
  unfold headAntiBank3D
  simp_rw [headAntiBank3D_term hx]
  exact (hasSum_bankTerm hN (1 / x)).tsum_eq

/-- The reflected head bank of 1257 is the anti-helix readout. -/
theorem windowAntiBank_eq_helix {N u : ℝ} (hN : 0 < N) (hu : 0 < u) :
    windowAntiBank N u = ((u ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * headAntiBank3D N u := by
  rw [windowAntiBank, headAntiBank3D_eq hN hu, one_div u]

/-! ## The tail from helix banks, and the completion -/

/-- The helix correction above the cut: the head's helix bank minus the η helix bank. -/
def upper3D (N c : ℝ) (w : ℂ) : ℂ :=
  ∫ x in Ioi c, (x : ℂ) ^ (w - 1) * (headBank3D N x - etaHelixBank x)

/-- The anti-helix correction above the reflected cut: the head's anti-helix bank minus the η anti-helix bank. -/
def lower3D (N c : ℝ) (w : ℂ) : ℂ :=
  ∫ u in Ioi c⁻¹, (u : ℂ) ^ (1 / 2 - w - 1) *
    (((u ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * headAntiBank3D N u - etaAntiHelixBank u)

/-- **The tail of the head fiber, built from helix banks.** -/
def helixTail (N c : ℝ) (s : ℂ) : ℂ :=
  (Real.pi : ℂ) ^ (s / 2) / (2 * Gamma (s / 2)) * (upper3D N c (s / 2) + lower3D N c (s / 2))

theorem helixTail_eq_windowTail {N c : ℝ} (hN : 0 < N) (hc : 0 < c) (s : ℂ) :
    helixTail N c s = windowTail N c s := by
  have hU : upper3D N c (s / 2) = upperCorrection N c (s / 2) := by
    unfold upper3D upperCorrection
    refine setIntegral_congr_fun measurableSet_Ioi fun x (hx : c < x) => ?_
    rw [headBank3D_eq hN (hc.trans hx)]
  have hL : lower3D N c (s / 2) = lowerCorrection N c (s / 2) := by
    unfold lower3D lowerCorrection
    refine setIntegral_congr_fun measurableSet_Ioi fun u (hu : c⁻¹ < u) => ?_
    rw [windowAntiBank_eq_helix hN ((inv_pos.mpr hc).trans hu)]
  unfold helixTail windowTail
  rw [hU, hL]

/-- **The window completion on the helix.** For `Re s > 0`, `s ≠ 1`, every head `N > 0` and every cut `c > 0`. -/
theorem helix_completion {N c : ℝ} (hN : 0 < N) (hc : 0 < c) {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) :
    finiteFiber N s + helixTail N c s = (1 - (2 : ℂ) ^ (1 - s)) * riemannZeta s := by
  rw [helixTail_eq_windowTail hN hc]
  exact window_completion hc hs hs1

/-! ## In helix height: the cut at `log c`, the reflected cut at `-log c` -/

theorem exp_smul_cpow (h : ℝ) (w : ℂ) :
    (Real.exp h : ℂ) * ((Real.exp h : ℝ) : ℂ) ^ (w - 1) = Complex.exp (w * h) := by
  rw [cpow_def_of_ne_zero (ofReal_ne_zero.mpr (Real.exp_pos h).ne'), ← ofReal_log (Real.exp_pos h).le,
    Real.log_exp, ofReal_exp, ← Complex.exp_add]
  congr 1
  ring

/-- The helix correction is an integral over helix heights above the cut `log c`. -/
theorem upper3D_height {N c : ℝ} (hc : 0 < c) (w : ℂ) :
    upper3D N c w = ∫ h in Ioi (Real.log c),
      Complex.exp (w * h) * (headBank3D N (Real.exp h) - etaHelixBank (Real.exp h)) := by
  unfold upper3D
  rw [← Real.exp_log hc, ← integral_comp_exp_Ioi, Real.exp_log hc]
  refine setIntegral_congr_fun measurableSet_Ioi fun h _ => ?_
  rw [real_smul, ← mul_assoc, exp_smul_cpow]

/-- The anti-helix correction is an integral over helix heights above `-log c`: the cut reflected about the
origin. -/
theorem lower3D_height {N c : ℝ} (hc : 0 < c) (w : ℂ) :
    lower3D N c w = ∫ h in Ioi (-Real.log c),
      Complex.exp ((1 / 2 - w) * h) * (((Real.exp h ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * headAntiBank3D N (Real.exp h)
        - etaAntiHelixBank (Real.exp h)) := by
  unfold lower3D
  have hci : c⁻¹ = Real.exp (-Real.log c) := by rw [Real.exp_neg, Real.exp_log hc]
  rw [hci, ← integral_comp_exp_Ioi]
  refine setIntegral_congr_fun measurableSet_Ioi fun h _ => ?_
  rw [real_smul, ← mul_assoc, exp_smul_cpow]

/-! ## Arrows into `FocalEvent`'s channel -/

open CriticalLinePhasor.FocalEventProjection CriticalLinePhasor.EisensteinWheelBank

theorem physicalHead_pos (y : ℝ) : 0 < physicalHead y :=
  lt_of_lt_of_le (by positivity) (physicalHead_lower y)

/-- **The event's head sum, completed by the helix tail.** -/
theorem headSum_helix_completion {σ : ℝ} (hσ : 0 < σ) (y : ℝ) {c : ℝ} (hc : 0 < c)
    (hs1 : (σ : ℂ) + (y : ℂ) * I ≠ 1) :
    headSum Routing.eta.coeff (fun k => ((k : ℝ) + 1) ^ (-σ)) y +
        helixTail (physicalHead y) c ((σ : ℂ) + (y : ℂ) * I) =
      (1 - (2 : ℂ) ^ (1 - ((σ : ℂ) + (y : ℂ) * I))) * riemannZeta ((σ : ℂ) + (y : ℂ) * I) := by
  rw [helixTail_eq_windowTail (physicalHead_pos y) hc]
  exact headSum_window_completion hσ y hc hs1

/-- **The two-ended closure of the event's head, on the helix**, at the native exponent. -/
theorem head_helix_closure_iff (y : ℝ) {c : ℝ} (hc : 0 < c) :
    headSum Routing.eta.coeff (fun k => ((k : ℝ) + 1) ^ (-(1 / 2 : ℝ))) y +
        helixTail (physicalHead y) c (((1 / 2 : ℝ) : ℂ) + (y : ℂ) * I) = 0 ↔
      riemannZeta (((1 / 2 : ℝ) : ℂ) + (y : ℂ) * I) = 0 := by
  rw [helixTail_eq_windowTail (physicalHead_pos y) hc]
  exact head_two_ended_closure_iff y hc

/-! ## At the event's physical height `Z` -/

/-- **The completion at physical height `Z`**: the event's head (`N = physicalHead (log Z)`) at exponent
`σ + i·log Z`, plus the helix tail. -/
theorem helix_completion_at_height {σ : ℝ} (hσ : 0 < σ) (Z : ℝ) {c : ℝ} (hc : 0 < c)
    (hs1 : (σ : ℂ) + (Real.log Z : ℂ) * I ≠ 1) :
    headSum Routing.eta.coeff (fun k => ((k : ℝ) + 1) ^ (-σ)) (Real.log Z) +
        helixTail (physicalHead (Real.log Z)) c ((σ : ℂ) + (Real.log Z : ℂ) * I) =
      (1 - (2 : ℂ) ^ (1 - ((σ : ℂ) + (Real.log Z : ℂ) * I))) *
        riemannZeta ((σ : ℂ) + (Real.log Z : ℂ) * I) :=
  headSum_helix_completion hσ (Real.log Z) hc hs1

/-- **The two-ended closure at the event's physical height `Z`**: the head's sum plus the helix tail vanishes
exactly when `ζ(½ + i·log Z) = 0`. -/
theorem helix_closure_at_height (Z : ℝ) {c : ℝ} (hc : 0 < c) :
    headSum Routing.eta.coeff (fun k => ((k : ℝ) + 1) ^ (-(1 / 2 : ℝ))) (Real.log Z) +
        helixTail (physicalHead (Real.log Z)) c (((1 / 2 : ℝ) : ℂ) + (Real.log Z : ℂ) * I) = 0 ↔
      riemannZeta (((1 / 2 : ℝ) : ℂ) + (Real.log Z : ℂ) * I) = 0 :=
  head_helix_closure_iff (Real.log Z) hc

/-- A focal event's physical height is `Z = e^y`; its chart readout is `y = log Z`. -/
theorem FocalEvent.log_height (e : FocalEvent) : Real.log e.height = e.y := by
  rw [e.height_eq, TwoEndedJState.eventHeight, Real.log_exp]

end CriticalLinePhasor.HelixWindowCompletion3D

end

#print axioms CriticalLinePhasor.HelixWindowCompletion3D.headBank3D_eq
#print axioms CriticalLinePhasor.HelixWindowCompletion3D.headAntiBank3D_eq
#print axioms CriticalLinePhasor.HelixWindowCompletion3D.helix_completion
#print axioms CriticalLinePhasor.HelixWindowCompletion3D.upper3D_height
#print axioms CriticalLinePhasor.HelixWindowCompletion3D.lower3D_height
#print axioms CriticalLinePhasor.HelixWindowCompletion3D.headSum_helix_completion
#print axioms CriticalLinePhasor.HelixWindowCompletion3D.head_helix_closure_iff
#print axioms CriticalLinePhasor.HelixWindowCompletion3D.helix_completion_at_height
#print axioms CriticalLinePhasor.HelixWindowCompletion3D.helix_closure_at_height
#print axioms CriticalLinePhasor.HelixWindowCompletion3D.FocalEvent.log_height
