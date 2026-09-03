import RequestProject.BankHerglotzReduction

/-!
# The clock door's admissible class: the Poisson floor and summable windings

`riemannHypothesis_of_bank_convergence` (BankLimitBridge) takes a sequence of finite
unimodular clock banks `∏ symClock (α i) (ℓ i)` and asks that their log-derivatives
converge to `logDeriv ξ` at channel points left of the line.  This file computes, DC first
and exactly, what that hypothesis forces on the banks themselves.

* `herglotzKernel_re` — the real part of the disk Herglotz kernel is the Poisson kernel:
  `Re((1+w)/(1−w)) = (1 − ‖w‖²)/‖1−w‖²`.
* `herglotzKernel_re_ge` — the Poisson floor `(1−‖w‖)/(1+‖w‖)` for `‖w‖ < 1`.
* `clockFloor` / `bank_logDeriv_re_le` — in the seat chart at abscissa `σ < ½` every clock
  of winding `ℓ` contributes real part at most `−(ℓ/2)·(1−r)/(1+r)`, `r = e^{−ℓ(½−σ)}`
  (that is `−(ℓ/2)·tanh(ℓ(½−σ)/2)`); the bank's real part is at most minus the sum of the
  floors.  Face-independent: the face `α` enters only through `arg w`.
* `bank_convergence_bounds_floor_sum` — **the door-class law**: if the bank log-derivatives
  converge, to anything at all, at one point left of the line, the floor sums are bounded
  uniformly in the stage.
* `bank_convergence_bounds_large_clocks` / `bank_convergence_card_bounded_of_winding_ge` —
  hence each stage carries boundedly many clocks of winding `≥ ℓ₀`, and a bank all of whose
  windings are `≥ ℓ₀` (every prime-indexed bank, `ℓ = log p ≥ log 2`) has bounded stage
  cardinality.  The compiled prime instance is `no_positive_primeToothNoTransient`
  (BankNoTransient); this is the general law behind it.

Reading.  The door's admissible banks have windings tending to `0` apart from boundedly
many clocks; a clock of winding `ℓ → 0` is a single pole `1/(s − ρ₀)` plus its DC `−ℓ/2`.
So the door is fed by pole swarms, whose zeros sit in the faces.  No fiber warp
(`DualWarp`: face twists) and no carrier scale (`Admissible.scale`: lattice relabeling)
touches the floor, because the floor does not depend on the face.

No `sorry`, no `axiom`.
-/

open Complex Filter Topology

noncomputable section

namespace CriticalLinePhasor.BankLimit

open CriticalLinePhasor.ChiralityHB

/-- **Real part of the disk Herglotz kernel = the Poisson kernel.**  No hypothesis is
needed: at `w = 1` both sides are Lean's `0`. -/
theorem herglotzKernel_re (w : ℂ) :
    ((1 + w) / (1 - w)).re = (1 - ‖w‖ ^ 2) / ‖1 - w‖ ^ 2 := by
  rw [Complex.div_re, Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply,
    Complex.normSq_apply]
  simp only [Complex.add_re, Complex.sub_re, Complex.one_re, Complex.add_im,
    Complex.sub_im, Complex.one_im]
  ring

/-- **The Poisson floor**: inside the disk the kernel's real part is at least
`(1−‖w‖)/(1+‖w‖)`, its value at the antipode `w = −‖w‖`. -/
theorem herglotzKernel_re_ge {w : ℂ} (hw : ‖w‖ < 1) :
    (1 - ‖w‖) / (1 + ‖w‖) ≤ ((1 + w) / (1 - w)).re := by
  rw [herglotzKernel_re]
  have h0 : 0 ≤ ‖w‖ := norm_nonneg w
  have hne : (1 : ℂ) - w ≠ 0 := by
    intro h
    have hw1 : w = 1 := by linear_combination -h
    rw [hw1, norm_one] at hw
    exact lt_irrefl _ hw
  have hpos : 0 < ‖(1 : ℂ) - w‖ := norm_pos_iff.mpr hne
  have h1 : ‖(1 : ℂ) - w‖ ≤ 1 + ‖w‖ := by
    calc ‖(1 : ℂ) - w‖ ≤ ‖(1 : ℂ)‖ + ‖w‖ := norm_sub_le _ _
      _ = 1 + ‖w‖ := by rw [norm_one]
  have h3 : ‖(1 : ℂ) - w‖ ^ 2 ≤ (1 + ‖w‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
  rw [div_le_div_iff₀ (by linarith) (pow_pos hpos 2)]
  calc (1 - ‖w‖) * ‖(1 : ℂ) - w‖ ^ 2 ≤ (1 - ‖w‖) * (1 + ‖w‖) ^ 2 :=
        mul_le_mul_of_nonneg_left h3 (by linarith)
    _ = (1 - ‖w‖ ^ 2) * (1 + ‖w‖) := by ring

/-- The clock's disk point in the seat chart has modulus `e^{−ℓ(½−σ)}`: the face drops out. -/
theorem clockDiskPoint_norm {α : ℂ} (hα : ‖α‖ = 1) (ℓ : ℝ) (s : ℂ) :
    ‖(starRingEnd ℂ) α * Complex.exp (Complex.I * ℓ * HilbertPolya.spectralCoord s)‖
      = Real.exp (-(ℓ * (1 / 2 - s.re))) := by
  rw [norm_mul, RCLike.norm_conj, hα, one_mul, Complex.norm_exp]
  congr 1
  have hre : (Complex.I * (ℓ : ℂ) * HilbertPolya.spectralCoord s).re
      = -(ℓ * (HilbertPolya.spectralCoord s).im) := by
    simp [Complex.mul_re, Complex.mul_im]
  rw [hre, spectralCoord_im]

/-- The **clock floor** at abscissa `σ`: `(ℓ/2)·(1−r)/(1+r)` with `r = e^{−ℓ(½−σ)}`, that is
`(ℓ/2)·tanh(ℓ(½−σ)/2)` — the least value of `(ℓ/2)·P_r` over the clock's period. -/
def clockFloor (ℓ σ : ℝ) : ℝ :=
  (ℓ / 2) * ((1 - Real.exp (-(ℓ * (1 / 2 - σ)))) / (1 + Real.exp (-(ℓ * (1 / 2 - σ)))))

theorem clockFloor_pos {ℓ σ : ℝ} (hℓ : 0 < ℓ) (hσ : σ < 1 / 2) : 0 < clockFloor ℓ σ := by
  unfold clockFloor
  have hu : 0 < ℓ * (1 / 2 - σ) := mul_pos hℓ (by linarith)
  have hr : Real.exp (-(ℓ * (1 / 2 - σ))) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hr0 : 0 < Real.exp (-(ℓ * (1 / 2 - σ))) := Real.exp_pos _
  exact mul_pos (by linarith) (div_pos (by linarith) (by linarith))

/-- The floor grows with the winding: a longer clock has a deeper floor. -/
theorem clockFloor_mono {ℓ₀ ℓ σ : ℝ} (hℓ₀ : 0 < ℓ₀) (hle : ℓ₀ ≤ ℓ) (hσ : σ < 1 / 2) :
    clockFloor ℓ₀ σ ≤ clockFloor ℓ σ := by
  unfold clockFloor
  have hu : 0 < 1 / 2 - σ := by linarith
  have hr₀0 : 0 < Real.exp (-(ℓ₀ * (1 / 2 - σ))) := Real.exp_pos _
  have hr0 : 0 < Real.exp (-(ℓ * (1 / 2 - σ))) := Real.exp_pos _
  have hr₀1 : Real.exp (-(ℓ₀ * (1 / 2 - σ))) < 1 :=
    Real.exp_lt_one_iff.mpr (by nlinarith [mul_pos hℓ₀ hu])
  have hrr₀ : Real.exp (-(ℓ * (1 / 2 - σ))) ≤ Real.exp (-(ℓ₀ * (1 / 2 - σ))) :=
    Real.exp_le_exp.mpr (by nlinarith [mul_nonneg (sub_nonneg.mpr hle) hu.le])
  set r₀ := Real.exp (-(ℓ₀ * (1 / 2 - σ))) with hr₀
  set r := Real.exp (-(ℓ * (1 / 2 - σ))) with hr
  have hg : (1 - r₀) / (1 + r₀) ≤ (1 - r) / (1 + r) := by
    rw [div_le_div_iff₀ (by linarith) (by linarith)]
    nlinarith
  have hg0 : 0 ≤ (1 - r₀) / (1 + r₀) := div_nonneg (by linarith) (by linarith)
  exact mul_le_mul (by linarith) hg hg0 (by linarith)

/-- **Every clock lies below its floor, face-independently; the bank lies below the sum.**
In the seat chart at `σ < ½` the bank readout's real part is at most
`−Σᵢ clockFloor (ℓ i) σ`. -/
theorem bank_logDeriv_re_le {ι : Type*} (t : Finset ι) (α : ι → ℂ) (ℓ : ι → ℝ)
    (hα : ∀ i ∈ t, ‖α i‖ = 1) (hℓ : ∀ i ∈ t, 0 < ℓ i) {s : ℂ} (hs : s.re < 1 / 2) :
    (logDeriv (fun w => ∏ i ∈ t,
        symClock (α i) (ℓ i) (HilbertPolya.spectralCoord w)) s).re
      ≤ -∑ i ∈ t, clockFloor (ℓ i) s.re := by
  rw [bank_readout_logDeriv_closed t α ℓ hα hℓ hs, Complex.neg_re, Complex.re_sum,
    neg_le_neg_iff]
  apply Finset.sum_le_sum
  intro i hi
  rw [Complex.re_ofReal_mul]
  unfold clockFloor
  have hu : 0 < ℓ i * (1 / 2 - s.re) := mul_pos (hℓ i hi) (by linarith)
  have hw : ‖(starRingEnd ℂ) (α i)
      * Complex.exp (Complex.I * (ℓ i) * HilbertPolya.spectralCoord s)‖ < 1 := by
    rw [clockDiskPoint_norm (hα i hi)]
    exact Real.exp_lt_one_iff.mpr (by linarith)
  have hfloor := herglotzKernel_re_ge hw
  rw [clockDiskPoint_norm (hα i hi)] at hfloor
  exact mul_le_mul_of_nonneg_left hfloor (by linarith [hℓ i hi])

/-- **The door-class law.**  If the bank log-derivatives converge, to anything at all, at
ONE point left of the line, then the clock-floor sums are bounded uniformly in the stage. -/
theorem bank_convergence_bounds_floor_sum {ι : Type*} (T : ℕ → Finset ι) (α : ι → ℂ)
    (ℓ : ι → ℝ) (hα : ∀ i, ‖α i‖ = 1) (hℓ : ∀ i, 0 < ℓ i) {s : ℂ} (hs : s.re < 1 / 2)
    {L : ℂ}
    (hconv : Tendsto (fun n => logDeriv (fun w => ∏ i ∈ T n,
        symClock (α i) (ℓ i) (HilbertPolya.spectralCoord w)) s) atTop (nhds L)) :
    ∃ C : ℝ, ∀ n, ∑ i ∈ T n, clockFloor (ℓ i) s.re ≤ C := by
  have hre : Tendsto (fun n => (logDeriv (fun w => ∏ i ∈ T n,
      symClock (α i) (ℓ i) (HilbertPolya.spectralCoord w)) s).re) atTop (nhds L.re) :=
    (Complex.continuous_re.tendsto L).comp hconv
  obtain ⟨C, hC⟩ := hre.bddBelow_range
  refine ⟨-C, fun n => ?_⟩
  have h1 := bank_logDeriv_re_le (T n) α ℓ (fun i _ => hα i) (fun i _ => hℓ i) hs
  have h2 : C ≤ (logDeriv (fun w => ∏ i ∈ T n,
      symClock (α i) (ℓ i) (HilbertPolya.spectralCoord w)) s).re :=
    hC (Set.mem_range_self n)
  linarith

/-- **Boundedly many long clocks per stage.**  Under convergence, the number of clocks of
winding `≥ ℓ₀` in stage `n` is at most `C / clockFloor ℓ₀ σ`, uniformly in `n`. -/
theorem bank_convergence_bounds_large_clocks {ι : Type*} (T : ℕ → Finset ι) (α : ι → ℂ)
    (ℓ : ι → ℝ) (hα : ∀ i, ‖α i‖ = 1) (hℓ : ∀ i, 0 < ℓ i) {s : ℂ} (hs : s.re < 1 / 2)
    {L : ℂ}
    (hconv : Tendsto (fun n => logDeriv (fun w => ∏ i ∈ T n,
        symClock (α i) (ℓ i) (HilbertPolya.spectralCoord w)) s) atTop (nhds L))
    {ℓ₀ : ℝ} (hℓ₀ : 0 < ℓ₀) :
    ∃ C : ℝ, ∀ n,
      (((T n).filter (fun i => ℓ₀ ≤ ℓ i)).card : ℝ) ≤ C / clockFloor ℓ₀ s.re := by
  obtain ⟨C, hC⟩ := bank_convergence_bounds_floor_sum T α ℓ hα hℓ hs hconv
  refine ⟨C, fun n => ?_⟩
  rw [le_div_iff₀ (clockFloor_pos hℓ₀ hs)]
  calc (((T n).filter (fun i => ℓ₀ ≤ ℓ i)).card : ℝ) * clockFloor ℓ₀ s.re
      ≤ ∑ i ∈ (T n).filter (fun i => ℓ₀ ≤ ℓ i), clockFloor (ℓ i) s.re := by
        have h := Finset.card_nsmul_le_sum ((T n).filter (fun i => ℓ₀ ≤ ℓ i))
          (fun i => clockFloor (ℓ i) s.re) (clockFloor ℓ₀ s.re)
          (fun i hi => clockFloor_mono hℓ₀ (Finset.mem_filter.mp hi).2 hs)
        simpa [nsmul_eq_mul] using h
    _ ≤ ∑ i ∈ T n, clockFloor (ℓ i) s.re :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun i _ _ => (clockFloor_pos (hℓ i) hs).le)
    _ ≤ C := hC n

/-- **Prime-shaped banks have bounded stages.**  A bank all of whose windings are `≥ ℓ₀`
(every prime-indexed bank: `ℓ = log p ≥ log 2`) has bounded stage cardinality under
convergence at any point left of the line — so an exhaustion of the primes cannot feed the
door, for any faces.  Compiled prime instance: `no_positive_primeToothNoTransient`. -/
theorem bank_convergence_card_bounded_of_winding_ge {ι : Type*} (T : ℕ → Finset ι)
    (α : ι → ℂ) (ℓ : ι → ℝ) (hα : ∀ i, ‖α i‖ = 1) (hℓ : ∀ i, 0 < ℓ i) {s : ℂ}
    (hs : s.re < 1 / 2) {L : ℂ}
    (hconv : Tendsto (fun n => logDeriv (fun w => ∏ i ∈ T n,
        symClock (α i) (ℓ i) (HilbertPolya.spectralCoord w)) s) atTop (nhds L))
    {ℓ₀ : ℝ} (hℓ₀ : 0 < ℓ₀) (hge : ∀ i, ℓ₀ ≤ ℓ i) :
    ∃ C : ℝ, ∀ n, ((T n).card : ℝ) ≤ C := by
  obtain ⟨C, hC⟩ := bank_convergence_bounds_large_clocks T α ℓ hα hℓ hs hconv hℓ₀
  refine ⟨C / clockFloor ℓ₀ s.re, fun n => ?_⟩
  have hfilt : (T n).filter (fun i => ℓ₀ ≤ ℓ i) = T n :=
    Finset.filter_true_of_mem (fun i _ => hge i)
  have h := hC n
  rw [hfilt] at h
  exact h

end CriticalLinePhasor.BankLimit

#print axioms CriticalLinePhasor.BankLimit.herglotzKernel_re
#print axioms CriticalLinePhasor.BankLimit.herglotzKernel_re_ge
#print axioms CriticalLinePhasor.BankLimit.bank_logDeriv_re_le
#print axioms CriticalLinePhasor.BankLimit.bank_convergence_bounds_floor_sum
#print axioms CriticalLinePhasor.BankLimit.bank_convergence_bounds_large_clocks
#print axioms CriticalLinePhasor.BankLimit.bank_convergence_card_bounded_of_winding_ge
