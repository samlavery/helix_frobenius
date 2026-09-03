import RequestProject.SeatingMassRH
import RequestProject.CarrierChannelReadout

/-!
# The seat mass in ordered carrier data (Track A3 of `HP_SKELETON.md`)

The mass door `riemannHypothesis_of_channel_mass` asks for `seatMass s ≥ 0` on the high
left channel, where `seatMass s = Re[ξ′/ξ(s)] / (σ − ½)`.  This file splices the classical
product form of `ξ` onto the compiled η-bridge, so the hypothesis reads entirely in the
ordered carrier readout plus explicit trivial terms.

* `logDeriv_Gammaℝ_eq` — `Γℝ′/Γℝ(s) = −½ log π + ½ Γ′/Γ(s/2)` on `Re s > 0`.
* `logDeriv_riemannXi_splice` — on the strip off the zeros of `ζ`,
  `ξ′/ξ(s) = 1/s + 1/(s−1) − ½ log π + ½ Γ′/Γ(s/2) + ζ′/ζ(s)`.
* `seatMass_eta_form` — with the η-bridge `zeta_logDeriv_eq_etaLim`,
  `seatMass s = Re[ η′/η(s) − (1 − 2^{1−s})′/(1 − 2^{1−s}) + 1/s + 1/(s−1) − ½ log π
                     + ½ Γ′/Γ(s/2) ] / (σ − ½)`,
  where `η = etaLim` is the ordered carrier series, convergent on the whole channel.
  Three fields: the two ENDS `1/s + 1/(s−1)`, the Archimedean clock `−½ log π + ½ ψ(s/2)`,
  and the WINDING through the ordered readout.
* `riemannHypothesis_of_eta_mass` — the mass door restated: nonnegativity of that
  explicit expression on the channel, off the zeros of `ζ`, forces Mathlib's
  `RiemannHypothesis`.  At a zero the totalized `seatMass` vanishes, so no input is used.

No `sorry`, no `axiom`.
-/

open Complex Filter Topology

noncomputable section

namespace CriticalLinePhasor.SeatingLedger

open CriticalLinePhasor.DVP CriticalLinePhasor.CarrierChannelReadout

/-- The classical product form of `ξ` on `Re s > 0`, `s ≠ 1` (pointwise). -/
theorem riemannXi_eq_poly_mul_Gammaℝ_mul_zeta {s : ℂ} (hs0 : 0 < s.re) (hs1 : s ≠ 1) :
    ZD.riemannXi s = (s * (s - 1) / 2) * (Gammaℝ s * riemannZeta s) := by
  have hs0' : s ≠ 0 := by
    intro h
    rw [h, Complex.zero_re] at hs0
    exact lt_irrefl 0 hs0
  have hΓ : Gammaℝ s ≠ 0 := Gammaℝ_ne_zero_of_re_pos hs0
  rw [ZD.riemannXi_eq_classical_of_ne_zero_of_ne_one s hs0' hs1,
    riemannZeta_def_of_ne_zero hs0', mul_comm (Gammaℝ s), div_mul_cancel₀ _ hΓ]

/-- The same, as an eventual equality at `s`: the set `{Re > 0} ∖ {1}` is open. -/
theorem riemannXi_eventuallyEq_poly_mul_Gammaℝ_mul_zeta {s : ℂ} (hs0 : 0 < s.re) (hs1 : s ≠ 1) :
    ZD.riemannXi =ᶠ[nhds s] fun w => (w * (w - 1) / 2) * (Gammaℝ w * riemannZeta w) := by
  have hopen : IsOpen {w : ℂ | 0 < w.re ∧ w ≠ 1} :=
    (isOpen_lt continuous_const Complex.continuous_re).inter isOpen_ne
  filter_upwards [hopen.mem_nhds ⟨hs0, hs1⟩] with w hw
  exact riemannXi_eq_poly_mul_Gammaℝ_mul_zeta hw.1 hw.2

/-- `s/2` avoids the poles of `Γ` when `Re s > 0`. -/
theorem half_ne_neg_nat {s : ℂ} (hs0 : 0 < s.re) (m : ℕ) : s / 2 ≠ -(m : ℂ) := by
  intro h
  have hre := congrArg Complex.re h
  rw [Complex.div_ofNat_re, Complex.neg_re, Complex.natCast_re] at hre
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  linarith

theorem half_re_pos {s : ℂ} (hs0 : 0 < s.re) : 0 < (s / 2).re := by
  rw [Complex.div_ofNat_re]
  linarith

/-- The Archimedean factor `π^{−w/2}` as a derivative. -/
theorem hasDerivAt_pi_cpow (s : ℂ) :
    HasDerivAt (fun w : ℂ => (Real.pi : ℂ) ^ (-w / 2))
      ((Real.pi : ℂ) ^ (-s / 2) * Complex.log (Real.pi : ℂ) * (-1 / 2)) s := by
  have h : HasDerivAt (fun w : ℂ => -w / 2) (-1 / 2) s := by
    simpa using ((hasDerivAt_id s).neg.div_const 2)
  exact h.const_cpow (Or.inl (by exact_mod_cast Real.pi_pos.ne'))

/-- `Γ(w/2)` as a derivative, for `Re s > 0`. -/
theorem hasDerivAt_Gamma_half {s : ℂ} (hs0 : 0 < s.re) :
    HasDerivAt (fun w : ℂ => Complex.Gamma (w / 2))
      (deriv Complex.Gamma (s / 2) * (1 / 2)) s := by
  have hG : HasDerivAt Complex.Gamma (deriv Complex.Gamma (s / 2)) (s / 2) :=
    (Complex.differentiableAt_Gamma (s / 2) (half_ne_neg_nat hs0)).hasDerivAt
  have hhalf : HasDerivAt (fun w : ℂ => w / 2) (1 / 2) s := by
    simpa using (hasDerivAt_id s).div_const 2
  exact hG.comp s hhalf

/-- `Γℝ` is differentiable on `Re s > 0`. -/
theorem Gammaℝ_differentiableAt_of_re_pos {s : ℂ} (hs0 : 0 < s.re) :
    DifferentiableAt ℂ Gammaℝ s := by
  have hfun : Gammaℝ = fun w : ℂ => (Real.pi : ℂ) ^ (-w / 2) * Complex.Gamma (w / 2) :=
    funext Gammaℝ_def
  rw [hfun]
  exact ((hasDerivAt_pi_cpow s).mul (hasDerivAt_Gamma_half hs0)).differentiableAt

/-- **The Archimedean clock**: `Γℝ′/Γℝ(s) = −½ log π + ½ Γ′/Γ(s/2)` on `Re s > 0`. -/
theorem logDeriv_Gammaℝ_eq {s : ℂ} (hs0 : 0 < s.re) :
    logDeriv Gammaℝ s
      = -((Real.log Real.pi : ℝ) : ℂ) / 2 + logDeriv Complex.Gamma (s / 2) / 2 := by
  have hfun : Gammaℝ = fun w : ℂ => (Real.pi : ℂ) ^ (-w / 2) * Complex.Gamma (w / 2) :=
    funext Gammaℝ_def
  have hA := hasDerivAt_pi_cpow s
  have hB := hasDerivAt_Gamma_half hs0
  have hπ0 : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_pos.ne'
  have hAne : (Real.pi : ℂ) ^ (-s / 2) ≠ 0 := cpow_ne_zero_iff.mpr (Or.inl hπ0)
  have hBne : Complex.Gamma (s / 2) ≠ 0 := Gamma_ne_zero_of_re_pos (half_re_pos hs0)
  rw [hfun, logDeriv_mul (f := fun w : ℂ => (Real.pi : ℂ) ^ (-w / 2))
      (g := fun w : ℂ => Complex.Gamma (w / 2)) s hAne hBne
      hA.differentiableAt hB.differentiableAt,
    logDeriv_apply, logDeriv_apply, hA.deriv, hB.deriv, logDeriv_apply,
    ← Complex.ofReal_log Real.pi_pos.le]
  field_simp

/-- The two ENDS: `(w(w−1)/2)′/(w(w−1)/2) = 1/s + 1/(s−1)` off `0, 1`. -/
theorem logDeriv_poly_eq {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    logDeriv (fun w : ℂ => w * (w - 1) / 2) s = 1 / s + 1 / (s - 1) := by
  have hP : HasDerivAt (fun w : ℂ => w * (w - 1) / 2) ((1 * (s - 1) + s * 1) / 2) s :=
    ((hasDerivAt_id' s).mul ((hasDerivAt_id' s).sub_const 1)).div_const 2
  have hs1' : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
  rw [logDeriv_apply, hP.deriv]
  field_simp

/-- **The splice**: on the strip off the zeros of `ζ`,
`ξ′/ξ(s) = 1/s + 1/(s−1) − ½ log π + ½ Γ′/Γ(s/2) + ζ′/ζ(s)`. -/
theorem logDeriv_riemannXi_splice {s : ℂ} (hs0 : 0 < s.re) (hs1 : s ≠ 1)
    (hz : riemannZeta s ≠ 0) :
    logDeriv ZD.riemannXi s
      = 1 / s + 1 / (s - 1) - ((Real.log Real.pi : ℝ) : ℂ) / 2
        + logDeriv Complex.Gamma (s / 2) / 2 + logDeriv riemannZeta s := by
  have hs0' : s ≠ 0 := by
    intro h
    rw [h, Complex.zero_re] at hs0
    exact lt_irrefl 0 hs0
  have hev := riemannXi_eventuallyEq_poly_mul_Gammaℝ_mul_zeta hs0 hs1
  have hΓ : Gammaℝ s ≠ 0 := Gammaℝ_ne_zero_of_re_pos hs0
  have hΓd : DifferentiableAt ℂ Gammaℝ s := Gammaℝ_differentiableAt_of_re_pos hs0
  have hζd : DifferentiableAt ℂ riemannZeta s := differentiableAt_riemannZeta hs1
  have hpoly_ne : s * (s - 1) / 2 ≠ 0 := by
    have : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
    exact div_ne_zero (mul_ne_zero hs0' this) two_ne_zero
  have hpoly_d : DifferentiableAt ℂ (fun w : ℂ => w * (w - 1) / 2) s :=
    (((hasDerivAt_id' s).mul ((hasDerivAt_id' s).sub_const 1)).div_const 2).differentiableAt
  have hld : logDeriv ZD.riemannXi s
      = logDeriv (fun w : ℂ => (w * (w - 1) / 2) * (Gammaℝ w * riemannZeta w)) s := by
    rw [logDeriv_apply, logDeriv_apply, hev.deriv_eq, hev.eq_of_nhds]
  rw [hld,
    logDeriv_mul (f := fun w : ℂ => w * (w - 1) / 2)
      (g := fun w : ℂ => Gammaℝ w * riemannZeta w) s hpoly_ne (mul_ne_zero hΓ hz)
      hpoly_d (hΓd.mul hζd),
    logDeriv_mul (f := Gammaℝ) (g := riemannZeta) s hΓ hz hΓd hζd,
    logDeriv_poly_eq hs0' hs1, logDeriv_Gammaℝ_eq hs0]
  ring

/-- **The seat mass in ordered carrier data.**  On the strip off the zeros of `ζ`, the
mass is the real part of: the ordered readout's log-derivative, minus the explicit
η-factor term, plus the two ends, plus the Archimedean clock — divided by `σ − ½`. -/
theorem seatMass_eta_form {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1) (hz : riemannZeta s ≠ 0) :
    seatMass s
      = (logDeriv etaLim s
          - logDeriv (fun w : ℂ => (1 : ℂ) - (2 : ℂ) ^ ((1 : ℂ) - w)) s
          + 1 / s + 1 / (s - 1) - ((Real.log Real.pi : ℝ) : ℂ) / 2
          + logDeriv Complex.Gamma (s / 2) / 2).re / (s.re - 1 / 2) := by
  have hs1' : s ≠ 1 := by
    intro h
    rw [h] at hs1
    simp at hs1
  unfold seatMass
  rw [logDeriv_riemannXi_splice hs0 hs1' hz, zeta_logDeriv_eq_etaLim hs0 hs1 hz]
  congr 2
  ring

/-- **The mass door in ordered carrier data.**  Nonnegativity of the explicit expression of
`seatMass_eta_form` on the high left channel, off the zeros of `ζ`, forces Mathlib's
`RiemannHypothesis`.  At a zero of `ζ` the totalized seat mass is `0`, so nothing is
required there. -/
theorem riemannHypothesis_of_eta_mass :
    ∃ A : ℝ, 0 < A ∧
      ((∀ s : ℂ, 1269 / 2 < |s.im| →
          A / (Real.log |s.im|) ^ 9 < s.re → s.re < 1 / 2 →
          riemannZeta s ≠ 0 →
          0 ≤ (logDeriv etaLim s
                - logDeriv (fun w : ℂ => (1 : ℂ) - (2 : ℂ) ^ ((1 : ℂ) - w)) s
                + 1 / s + 1 / (s - 1) - ((Real.log Real.pi : ℝ) : ℂ) / 2
                + logDeriv Complex.Gamma (s / 2) / 2).re / (s.re - 1 / 2)) →
        RiemannHypothesis) := by
  obtain ⟨A, hA0, hdoor⟩ := riemannHypothesis_of_channel_mass
  refine ⟨A, hA0, fun hmass => hdoor ?_⟩
  intro s him hlow hhigh
  have hlog : 0 < Real.log |s.im| := Real.log_pos (by linarith)
  have hs0 : 0 < s.re := lt_trans (div_pos hA0 (pow_pos hlog 9)) hlow
  have hs1 : s.re < 1 := by linarith
  by_cases hz : riemannZeta s = 0
  · have hs1' : s ≠ 1 := by
      intro h
      rw [h] at hs1
      simp at hs1
    have hxi : ZD.riemannXi s = 0 := by
      rw [riemannXi_eq_poly_mul_Gammaℝ_mul_zeta hs0 hs1', hz, mul_zero, mul_zero]
    unfold seatMass
    rw [logDeriv_apply, hxi, div_zero, Complex.zero_re, zero_div]
  · rw [seatMass_eta_form hs0 hs1 hz]
    exact hmass s him hlow hhigh hz

end CriticalLinePhasor.SeatingLedger

#print axioms CriticalLinePhasor.SeatingLedger.logDeriv_Gammaℝ_eq
#print axioms CriticalLinePhasor.SeatingLedger.logDeriv_riemannXi_splice
#print axioms CriticalLinePhasor.SeatingLedger.seatMass_eta_form
#print axioms CriticalLinePhasor.SeatingLedger.riemannHypothesis_of_eta_mass
