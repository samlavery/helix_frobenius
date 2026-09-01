import RequestProject.DVPCarrierContinuation

/-!
# The channel readout bridge: `ζ′/ζ` on the ordered carrier series

The arithmetic-entry brick of the mass program.  The compiled ordered
readout (`etaLim`, holomorphic on `Re s > 0`, with
`etaLim = (1 − 2^{1−s})·ζ` there) carries the logarithmic derivative of `ζ`
into the channel through convergent bank data:

* `etaFactor_ne_zero` — the η-factor `1 − 2^{1−s}` NEVER vanishes left of
  `σ = 1` (its modulus is `2^{1−σ} > 1`): the ordered chart is
  singularity-free over the whole strip interior and channel;
* `zeta_logDeriv_eq_etaLim` — at every strip point off the zeros,
  `ζ′/ζ = (etaLim)′/etaLim − (η-factor)′/(η-factor)`, both terms computed
  from the carrier side.  Unconditional.

In HP terms this is the trace-formula face of the mass hypothesis: the
resolvent's boundary values on the channel evaluated from the ordered
arithmetic readout — the explicit formula the lens/receiver doors demand
of the exhibit.

No `sorry`, no `axiom`.
-/

open Complex Filter

noncomputable section

namespace CriticalLinePhasor.CarrierChannelReadout

open CriticalLinePhasor.DVP

/-- **The η-factor is invertible left of `σ = 1`**: `|2^{1−s}| = 2^{1−σ} > 1`,
so `1 − 2^{1−s} ≠ 0`.  The ordered chart has no spurious singularities in
the strip interior or the channel. -/
theorem etaFactor_ne_zero {s : ℂ} (hs : s.re < 1) :
    (1:ℂ) - (2:ℂ)^((1:ℂ)-s) ≠ 0 := by
  intro h
  have heq : (2:ℂ)^((1:ℂ)-s) = 1 := (sub_eq_zero.mp h).symm
  have hnorm : ‖(2:ℂ)^((1:ℂ)-s)‖ = (2:ℝ)^(((1:ℂ)-s).re) := by
    rw [show (2:ℂ) = ((2:ℝ):ℂ) by norm_num]
    exact Complex.norm_cpow_eq_rpow_re_of_pos two_pos _
  rw [heq] at hnorm
  have hre : ((1:ℂ)-s).re = 1 - s.re := by
    simp [Complex.sub_re]
  rw [hre, norm_one] at hnorm
  have hgt : (1:ℝ) < (2:ℝ)^(1 - s.re) :=
    (Real.one_lt_rpow_iff_of_pos two_pos).mpr
      (Or.inl ⟨one_lt_two, by linarith⟩)
  rw [← hnorm] at hgt
  exact lt_irrefl 1 hgt

/-- **The channel readout bridge**: at every strip-interior point off the
zeros, the logarithmic derivative of `ζ` is the ordered readout's
logarithmic derivative minus the explicit η-factor term.  Unconditional —
the identity that moves the seat's prime side onto the convergent carrier
series. -/
theorem zeta_logDeriv_eq_etaLim {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1)
    (hz : riemannZeta s ≠ 0) :
    logDeriv riemannZeta s
      = logDeriv etaLim s
        - logDeriv (fun w => (1:ℂ) - (2:ℂ)^((1:ℂ)-w)) s := by
  have hsne1 : s ≠ 1 := by
    intro h
    rw [h] at hs1
    simp at hs1
  have hfne : (1:ℂ) - (2:ℂ)^((1:ℂ)-s) ≠ 0 := etaFactor_ne_zero hs1
  have hg : DifferentiableAt ℂ (fun w : ℂ => (2:ℂ)^((1:ℂ)-w)) s :=
    ((differentiableAt_const _).sub differentiableAt_id).const_cpow
      (Or.inl two_ne_zero)
  have hfd : DifferentiableAt ℂ (fun w : ℂ => (1:ℂ) - (2:ℂ)^((1:ℂ)-w)) s :=
    (differentiableAt_const 1).sub hg
  have hzd : DifferentiableAt ℂ riemannZeta s :=
    differentiableAt_riemannZeta hsne1
  have hopen : IsOpen {w : ℂ | 0 < w.re ∧ w ≠ 1} := by
    have h1 : IsOpen {w : ℂ | 0 < w.re} :=
      isOpen_lt continuous_const Complex.continuous_re
    have h2 : IsOpen {w : ℂ | w ≠ 1} := isOpen_ne
    exact h1.inter h2
  have hev : etaLim
      =ᶠ[nhds s] fun w => ((1:ℂ) - (2:ℂ)^((1:ℂ)-w)) * riemannZeta w := by
    filter_upwards [hopen.mem_nhds ⟨hs0, hsne1⟩] with w hw
    exact etaLim_eq_zeta hw.1 hw.2
  have hld : logDeriv etaLim s
      = logDeriv (fun w => ((1:ℂ) - (2:ℂ)^((1:ℂ)-w)) * riemannZeta w) s := by
    rw [logDeriv_apply, logDeriv_apply, hev.deriv_eq, hev.eq_of_nhds]
  rw [hld, logDeriv_mul s hfne hz hfd hzd]
  ring

end CriticalLinePhasor.CarrierChannelReadout

#print axioms CriticalLinePhasor.CarrierChannelReadout.etaFactor_ne_zero
#print axioms CriticalLinePhasor.CarrierChannelReadout.zeta_logDeriv_eq_etaLim
