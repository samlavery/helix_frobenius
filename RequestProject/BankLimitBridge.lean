import RequestProject.FiniteBankMass
import RequestProject.SeatingMassRH

/-!
# The bridge: finite-bank positivity transported to the readout

Arrow [A3] of the kill tree, compiled.  Two statements:

* `mass_nonneg_of_logDeriv_tendsto` — the transfer lemma, unconditional and
  reusable: pointwise convergence of log-derivatives carries seat-mass
  nonnegativity to the limit.  Nonnegativity is closed; that is the whole
  content, and it needs no holomorphy, no uniformity, no zero-set control.
* `riemannHypothesis_of_bank_convergence` — the bridge itself: if the
  log-derivatives of finite unimodular clock banks converge to `ξ`'s at
  every point of the compiled high-left channel, then Mathlib's
  `RiemannHypothesis` holds.

The positivity side is `finiteBank_seatMass_nonneg` — arbitrary unimodular
faces, arbitrary positive lengths, whole half-plane `σ < ½`,
unconditional.  So the bridge's hypothesis is purely a CONVERGENCE
statement about explicit functions: no positivity is assumed anywhere
downstream of the banks.

No `sorry`, no `axiom`.
-/

open Complex Filter Topology

noncomputable section

namespace CriticalLinePhasor.BankLimit

open CriticalLinePhasor.ChiralityHB CriticalLinePhasor.SeatingLedger

/-- **The transfer lemma**: seat-mass nonnegativity survives pointwise
convergence of log-derivatives. -/
theorem mass_nonneg_of_logDeriv_tendsto {F : ℕ → ℂ → ℂ} {G : ℂ → ℂ} {s : ℂ}
    (hconv : Tendsto (fun n => logDeriv (F n) s) atTop
      (nhds (logDeriv G s)))
    (hpos : ∀ n, 0 ≤ (logDeriv (F n) s).re / (s.re - 1/2)) :
    0 ≤ (logDeriv G s).re / (s.re - 1/2) := by
  have hdiv : Tendsto (fun n => (logDeriv (F n) s).re / (s.re - 1/2)) atTop
      (nhds ((logDeriv G s).re / (s.re - 1/2))) := by
    have hcont : Continuous (fun z : ℂ => z.re / (s.re - 1/2)) :=
      Complex.continuous_re.div_const _
    exact (hcont.tendsto _).comp hconv
  exact ge_of_tendsto hdiv (Filter.Eventually.of_forall hpos)

/-- **The bridge**: convergence of finite unimodular clock banks' log
derivatives to `ξ`'s, at the points of the compiled high-left channel,
forces the exact Mathlib `RiemannHypothesis`.  Positivity is never
hypothesized — it is supplied at every finite rank by
`finiteBank_seatMass_nonneg` and carried across by the transfer lemma. -/
theorem riemannHypothesis_of_bank_convergence
    {ι : Type*} (T : ℕ → Finset ι) (α : ι → ℂ) (ℓ : ι → ℝ)
    (hα : ∀ i, ‖α i‖ = 1) (hℓ : ∀ i, 0 < ℓ i) :
    ∃ A : ℝ, 0 < A ∧
      ((∀ s : ℂ, 1269/2 < |s.im| →
          A / (Real.log |s.im|)^9 < s.re → s.re < 1/2 →
          Tendsto (fun n => logDeriv (fun w => ∏ i ∈ T n,
              symClock (α i) (ℓ i)
                (CriticalLinePhasor.HilbertPolya.spectralCoord w)) s)
            atTop (nhds (logDeriv ZD.riemannXi s))) →
        RiemannHypothesis) := by
  obtain ⟨A, hA0, hdoor⟩ := riemannHypothesis_of_channel_mass
  refine ⟨A, hA0, fun hconv => hdoor ?_⟩
  intro s him hlow hhigh
  unfold seatMass
  refine mass_nonneg_of_logDeriv_tendsto (hconv s him hlow hhigh) ?_
  intro n
  exact finiteBank_seatMass_nonneg (T n) α ℓ
    (fun i _ => hα i) (fun i _ => hℓ i) hhigh

/-- The same bank bridge only asks for convergence away from zeros of `ξ`.
At a zero, Lean's totalized logarithmic derivative makes `seatMass` vanish,
so no convergence input is used there. -/
theorem riemannHypothesis_of_bank_convergence_off_zeros
    {ι : Type*} (T : ℕ → Finset ι) (α : ι → ℂ) (ℓ : ι → ℝ)
    (hα : ∀ i, ‖α i‖ = 1) (hℓ : ∀ i, 0 < ℓ i) :
    ∃ A : ℝ, 0 < A ∧
      ((∀ s : ℂ, 1269 / 2 < |s.im| →
          A / (Real.log |s.im|) ^ 9 < s.re → s.re < 1 / 2 →
          ZD.riemannXi s ≠ 0 →
          Tendsto (fun n => logDeriv (fun w => ∏ i ∈ T n,
              symClock (α i) (ℓ i)
                (CriticalLinePhasor.HilbertPolya.spectralCoord w)) s)
            atTop (nhds (logDeriv ZD.riemannXi s))) →
        RiemannHypothesis) := by
  obtain ⟨A, hA0, hdoor⟩ := riemannHypothesis_of_channel_mass
  refine ⟨A, hA0, fun hconv => hdoor ?_⟩
  intro s him hlow hhigh
  by_cases hz : ZD.riemannXi s = 0
  · unfold seatMass
    rw [logDeriv_apply, hz, div_zero, Complex.zero_re, zero_div]
  · unfold seatMass
    refine mass_nonneg_of_logDeriv_tendsto
      (hconv s him hlow hhigh hz) ?_
    intro n
    exact finiteBank_seatMass_nonneg (T n) α ℓ
      (fun i _ => hα i) (fun i _ => hℓ i) hhigh

end CriticalLinePhasor.BankLimit

#print axioms CriticalLinePhasor.BankLimit.mass_nonneg_of_logDeriv_tendsto
#print axioms CriticalLinePhasor.BankLimit.riemannHypothesis_of_bank_convergence
#print axioms CriticalLinePhasor.BankLimit.riemannHypothesis_of_bank_convergence_off_zeros
