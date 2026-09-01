import RequestProject.BankLimitBridge

/-!
# The bank door's object in closed form: the Herglotz-kernel lattice sum

The bank door (`riemannHypothesis_of_bank_convergence`) asks for convergence
of `logDeriv` of finite unimodular clock banks to `logDeriv ξ` on the
high-left channel.  This file computes that object EXACTLY — DC first, no
estimate:

* `symClock_logDeriv_closed` — the clock's log-derivative in closed form:
  `logDeriv (symClock α ℓ) z = −(ℓ/2)·i·(1+w)/(1−w)` with
  `w = conj α · e^{iℓz}`, `|w| < 1` on the upper half-plane — **the Herglotz
  kernel of the disk**, per clock.  (The geometric series of
  `symClock_logDeriv_expansion`, collapsed; previously an internal `have`
  of `symClock_logDeriv_im_nonpos`, now exported.)
* `bank_readout_logDeriv_closed` — **the door's object**: at every point
  left of the line, the bank readout's log-derivative is the finite
  Herglotz-kernel lattice sum `−Σᵢ (ℓᵢ/2)·(1+wᵢ)/(1−wᵢ)`.  The compiled
  anti-Herglotz property (`finiteBank_seatMass_nonneg`) made literal: the
  bank IS a positive combination of disk Herglotz kernels.
* `riemannHypothesis_of_herglotz_sum_convergence` — the door restated on
  the closed form: RH from convergence of the EXPLICIT lattice sums to
  `logDeriv ξ` at channel points.  Positivity, transfer, and the mass door
  are already spent; the hypothesis is one convergence statement about
  elementary functions — the register the Carlson mean-value machinery
  (`CarrierTransientRigidity`) speaks.

No `sorry`, no `axiom`.
-/

open Complex Filter Topology

noncomputable section

namespace CriticalLinePhasor.BankLimit

open CriticalLinePhasor.ChiralityHB CriticalLinePhasor.SeatingLedger

/-- **The clock's log-derivative in closed form — the Herglotz kernel.**
On the open upper/lower half-plane, `logDeriv (symClock α ℓ) z
= −(ℓ/2)·i·(1+w)/(1−w)` with `w = conj α · e^{iℓz}`: the geometric series
of `symClock_logDeriv_expansion` collapsed to the Cayley/Herglotz kernel
of the disk. -/
theorem symClock_logDeriv_closed {α : ℂ} (hα : ‖α‖ = 1) {ℓ : ℝ}
    (hℓ : 0 < ℓ) {z : ℂ} (hz : z.im ≠ 0) :
    logDeriv (symClock α ℓ) z
      = -(((ℓ / 2 : ℝ) : ℂ) * Complex.I
          * ((1 + (starRingEnd ℂ) α * Complex.exp (Complex.I * ℓ * z))
             / (1 - (starRingEnd ℂ) α * Complex.exp (Complex.I * ℓ * z)))) := by
  set A : ℂ := Complex.exp (Complex.I * z * ℓ / 2) with hA
  set G : ℂ := α * Complex.exp (-(Complex.I * z * ℓ / 2)) with hG
  set w : ℂ := (starRingEnd ℂ) α * Complex.exp (Complex.I * ℓ * z) with hw
  have hQeq : symClock α ℓ z = A - G := rfl
  have hAGne : A - G ≠ 0 := by
    rw [← hQeq]
    exact symClock_ne_zero_off_axis hα hℓ hz
  have hD := symClock_hasDerivAt α ℓ z
  have hlog : logDeriv (symClock α ℓ) z
      = ((ℓ / 2 : ℝ) : ℂ) * (Complex.I * ((A + G) / (A - G))) := by
    rw [logDeriv_apply, hD.deriv, hQeq, ← hA, ← hG]
    push_cast
    ring
  have hα0 : α ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hα
    norm_num at hα
  have hinv : (starRingEnd ℂ) α * α = 1 := by
    rw [← Complex.inv_eq_conj hα, inv_mul_cancel₀ hα0]
  have hGne : G ≠ 0 := by
    rw [hG]
    exact mul_ne_zero hα0 (Complex.exp_ne_zero _)
  have hAwG : A = w * G := by
    rw [hA, hw, hG,
      show (starRingEnd ℂ) α * Complex.exp (Complex.I * ℓ * z)
          * (α * Complex.exp (-(Complex.I * z * ℓ / 2)))
        = ((starRingEnd ℂ) α * α)
          * (Complex.exp (Complex.I * ℓ * z)
              * Complex.exp (-(Complex.I * z * ℓ / 2))) by ring,
      hinv, one_mul, ← Complex.exp_add]
    congr 1
    ring
  have hwne : w - 1 ≠ 0 := by
    intro h0
    rw [sub_eq_zero] at h0
    apply hAGne
    rw [hAwG, h0, one_mul, sub_self]
  have h1w : (1 : ℂ) - w ≠ 0 := by
    intro h0
    apply hwne
    rw [sub_eq_zero] at h0 ⊢
    exact h0.symm
  have hratio : (A + G) / (A - G) = (w + 1) / (w - 1) := by
    rw [hAwG, show w * G + G = (w + 1) * G by ring,
      show w * G - G = (w - 1) * G by ring,
      mul_div_mul_right _ _ hGne]
  rw [hlog, hratio]
  field_simp
  ring

/-- **The door's object, computed exactly.**  At every point strictly left
of the critical line, the bank readout's log-derivative is a finite
Herglotz-kernel lattice sum: the compiled anti-Herglotz positivity made
literal — the bank is a positive-length combination of disk Herglotz
kernels evaluated at `wᵢ = conj αᵢ · e^{iℓᵢ·spectralCoord s}`. -/
theorem bank_readout_logDeriv_closed {ι : Type*} (t : Finset ι)
    (α : ι → ℂ) (ℓ : ι → ℝ)
    (hα : ∀ i ∈ t, ‖α i‖ = 1) (hℓ : ∀ i ∈ t, 0 < ℓ i)
    {s : ℂ} (hs : s.re < 1 / 2) :
    logDeriv (fun w => ∏ i ∈ t,
        symClock (α i) (ℓ i) (CriticalLinePhasor.HilbertPolya.spectralCoord w)) s
      = -∑ i ∈ t, ((ℓ i / 2 : ℝ) : ℂ) *
          ((1 + (starRingEnd ℂ) (α i)
              * Complex.exp (Complex.I * (ℓ i)
                  * CriticalLinePhasor.HilbertPolya.spectralCoord s))
           / (1 - (starRingEnd ℂ) (α i)
              * Complex.exp (Complex.I * (ℓ i)
                  * CriticalLinePhasor.HilbertPolya.spectralCoord s))) := by
  have hy : 0 < (CriticalLinePhasor.HilbertPolya.spectralCoord s).im := by
    rw [spectralCoord_im]
    linarith
  have hzne : (CriticalLinePhasor.HilbertPolya.spectralCoord s).im ≠ 0 :=
    ne_of_gt hy
  have hstep : logDeriv (fun w => ∏ i ∈ t,
      symClock (α i) (ℓ i) (CriticalLinePhasor.HilbertPolya.spectralCoord w)) s
      = ∑ i ∈ t, logDeriv (fun w =>
          symClock (α i) (ℓ i)
            (CriticalLinePhasor.HilbertPolya.spectralCoord w)) s := by
    exact logDeriv_prod
      (fun i hi => symClock_ne_zero_off_axis (hα i hi) (hℓ i hi) hzne)
      (fun i hi => (symClock_differentiableAt (α i) (ℓ i) _).comp s
        (spectralCoord_hasDerivAt s).differentiableAt)
  rw [hstep, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl (fun i hi => ?_)
  have hcomp : logDeriv (fun w =>
      symClock (α i) (ℓ i)
        (CriticalLinePhasor.HilbertPolya.spectralCoord w)) s
      = logDeriv (symClock (α i) (ℓ i))
          (CriticalLinePhasor.HilbertPolya.spectralCoord s)
        * deriv CriticalLinePhasor.HilbertPolya.spectralCoord s :=
    logDeriv_comp (symClock_differentiableAt (α i) (ℓ i) _)
      (spectralCoord_hasDerivAt s).differentiableAt
  rw [hcomp, (spectralCoord_hasDerivAt s).deriv,
    symClock_logDeriv_closed (hα i hi) (hℓ i hi) hzne]
  linear_combination (((ℓ i / 2 : ℝ) : ℂ) *
    ((1 + (starRingEnd ℂ) (α i)
        * Complex.exp (Complex.I * (ℓ i)
            * CriticalLinePhasor.HilbertPolya.spectralCoord s))
     / (1 - (starRingEnd ℂ) (α i)
        * Complex.exp (Complex.I * (ℓ i)
            * CriticalLinePhasor.HilbertPolya.spectralCoord s))))
    * Complex.I_mul_I

/-- **The bank door on the closed form**: the Riemann Hypothesis from
convergence of the EXPLICIT Herglotz-kernel lattice sums to `logDeriv ξ`
at the channel points.  Positivity is spent by identity at every finite
rank, the transfer lemma carries it, the mass door closes — the entire
remaining field is this one convergence statement about elementary
functions, the register the Carlson mean-value machinery speaks. -/
theorem riemannHypothesis_of_herglotz_sum_convergence
    {ι : Type*} (T : ℕ → Finset ι) (α : ι → ℂ) (ℓ : ι → ℝ)
    (hα : ∀ i, ‖α i‖ = 1) (hℓ : ∀ i, 0 < ℓ i) :
    ∃ A : ℝ, 0 < A ∧
      ((∀ s : ℂ, 1269 / 2 < |s.im| →
          A / (Real.log |s.im|) ^ 9 < s.re → s.re < 1 / 2 →
          Tendsto (fun n => -∑ i ∈ T n,
              ((ℓ i / 2 : ℝ) : ℂ) *
                ((1 + (starRingEnd ℂ) (α i)
                    * Complex.exp (Complex.I * (ℓ i)
                        * CriticalLinePhasor.HilbertPolya.spectralCoord s))
                 / (1 - (starRingEnd ℂ) (α i)
                    * Complex.exp (Complex.I * (ℓ i)
                        * CriticalLinePhasor.HilbertPolya.spectralCoord s))))
            atTop (nhds (logDeriv ZD.riemannXi s))) →
        RiemannHypothesis) := by
  obtain ⟨A, hA0, hdoor⟩ := riemannHypothesis_of_bank_convergence T α ℓ hα hℓ
  refine ⟨A, hA0, fun hconv => hdoor ?_⟩
  intro s him hlow hhigh
  refine Filter.Tendsto.congr (fun n => ?_) (hconv s him hlow hhigh)
  exact (bank_readout_logDeriv_closed (T n) α ℓ
    (fun i _ => hα i) (fun i _ => hℓ i) hhigh).symm

/-- The closed-form bank door with convergence required only off zeros of
`riemannXi`; the zero case is discharged by the totalized seat mass. -/
theorem riemannHypothesis_of_herglotz_sum_convergence_off_zeros
    {ι : Type*} (T : ℕ → Finset ι) (α : ι → ℂ) (ℓ : ι → ℝ)
    (hα : ∀ i, ‖α i‖ = 1) (hℓ : ∀ i, 0 < ℓ i) :
    ∃ A : ℝ, 0 < A ∧
      ((∀ s : ℂ, 1269 / 2 < |s.im| →
          A / (Real.log |s.im|) ^ 9 < s.re → s.re < 1 / 2 →
          ZD.riemannXi s ≠ 0 →
          Tendsto (fun n => -∑ i ∈ T n,
              ((ℓ i / 2 : ℝ) : ℂ) *
                ((1 + (starRingEnd ℂ) (α i)
                    * Complex.exp (Complex.I * (ℓ i)
                        * CriticalLinePhasor.HilbertPolya.spectralCoord s))
                 / (1 - (starRingEnd ℂ) (α i)
                    * Complex.exp (Complex.I * (ℓ i)
                        * CriticalLinePhasor.HilbertPolya.spectralCoord s))))
            atTop (nhds (logDeriv ZD.riemannXi s))) →
        RiemannHypothesis) := by
  obtain ⟨A, hA0, hdoor⟩ :=
    riemannHypothesis_of_bank_convergence_off_zeros T α ℓ hα hℓ
  refine ⟨A, hA0, fun hconv => hdoor ?_⟩
  intro s him hlow hhigh hxi
  refine Filter.Tendsto.congr (fun n => ?_)
    (hconv s him hlow hhigh hxi)
  exact (bank_readout_logDeriv_closed (T n) α ℓ
    (fun i _ => hα i) (fun i _ => hℓ i) hhigh).symm

end CriticalLinePhasor.BankLimit

#print axioms CriticalLinePhasor.BankLimit.symClock_logDeriv_closed
#print axioms CriticalLinePhasor.BankLimit.bank_readout_logDeriv_closed
#print axioms CriticalLinePhasor.BankLimit.riemannHypothesis_of_herglotz_sum_convergence
#print axioms CriticalLinePhasor.BankLimit.riemannHypothesis_of_herglotz_sum_convergence_off_zeros
