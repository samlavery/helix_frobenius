/-
Consumes results from https://github.com/anthropics/zeta-23-lean
at commit 3635e74826a4c1fcece7d1cd2b6fa75e43a00510 (Lean v4.33.0-rc2), registered as the
Lake path dependency `Zeta23` (see lakefile.toml).
Copyright the zeta-23-lean contributors, Anthropic PBC; Apache License 2.0
(http://www.apache.org/licenses/LICENSE-2.0).

Imported, not ported — nothing is copied into this file.  The two upstream results consumed are:

* `Zeta23.RvM.re_logDeriv_Gammaℝ_half`  (Zeta23/RvM/GammaSide.lean, line 107)
    `(logDeriv Complex.Gammaℝ (1/2 + t * I)).re = Real.pi * Zeta23.mu t`
  — the normalization identity, proved upstream from `Zeta23.RvM.logDeriv_Gammaℝ`
  (same file, line 65): `logDeriv Γℝ s = -(log π)/2 + ½·ψ(s/2)` on `Re s > 0`.

* `Zeta23.StirlingVert.mu_stirling`  (Zeta23/GammaFacts/StirlingVert.lean, line 616)
    `∃ C, ∀ τ, 1 ≤ |τ| → |Zeta23.mu τ - (1/(2π))·log(|τ|/(2π))| ≤ C/τ²`
  — Stirling for the digamma on vertical lines, proved upstream from the partial-fraction
  series (`Zeta23.GammaFacts.Series`), without Euler–Maclaurin.

`Zeta23.mu` is defined in Zeta23/Defs.lean, line 83.
-/
import Zeta23.RvM.GammaSide
import Zeta23.GammaFacts.StirlingVert
import RequestProject.CarrierJensen

/-!
# The Stirling brick: the clock rate is `½·log t + O(1)`

`CarrierJensen.lean` carries `carrierJensenBound_of_clockBound`, whose hypothesis `hclock`
— a chart bound on the Γ-clock's rate — was never discharged in this tree.  Our own
`StirlingBound.lean` controls the *modulus* of `Γ`, not its logarithmic derivative; that was
the gap.  This file closes it outright.

## The identity, and the bound

The carrier's clock rate is the Zeta23 density `μ` up to the single scalar `π`:

  `clockRate t = π · Zeta23.mu t`     (`clockRate_eq_pi_mul_mu`)

which is `Zeta23.RvM.re_logDeriv_Gammaℝ_half` (zeta-23-lean, `Zeta23/RvM/GammaSide.lean`,
line 107), in turn resting on `Zeta23.RvM.logDeriv_Gammaℝ` (same file, line 65),
`logDeriv Γℝ s = −(log π)/2 + ½·ψ(s/2)` on `Re s > 0`.  Our `line_def` is `rfl`-equal to their
`1/2 + t*I`, so the identity transfers as a bare term application — no derivative work is
hand-rolled here.  With `Zeta23.StirlingVert.mu_stirling` this yields

  `clockRate t ≤ A' + (1/2) · Real.log t`   for `t ≥ 2`   (`clockRate_log_bound_half`)

with the `log`-coefficient **exactly `1/2`** and only the additive constant existential.  See
the file header for the Apache-2.0 attribution and the full list of upstream results consumed.

## Scope: exactly what this discharges, and what it does not

**Discharged.**  `hclock`, unconditionally.  That is the whole of the Γ-side input to
`carrierJensenBound_of_clockBound`, and it had never been discharged anywhere in this tree.
What becomes unconditional is the *transport between the two registers*: the native register
now implies the chart register with no Γ-side hypothesis left standing
(`carrierJensenBound_of_clockBound_unconditional`).

**Not discharged — and this file must not be read as claiming otherwise.**
`CarrierJensenBound` is **not** proven here.  The residual input
`CarrierJensenClockBound A B` (`∀ t ≥ 2, |S t| ≤ A + B · clockRate t`) remains a hypothesis;
it is inhabited nowhere in this tree, and this file does not inhabit it.  Both named targets
are `|S t|` bounds, hence two-sided, and their two sides are of utterly different strength
(the register is stated exactly in `CarrierJensen.lean`):

* the **upper** side, `S t ≤ A + B·log t`, is classical strength — Backlund's argument-variation
  bound.  It is *not* derived here: this file supplies the Γ-clock's rate, not the census
  bookkeeping that would glue it.
* the **lower** side, `−S t ≤ A + B·log t`, is equivalent to `N_off(t) ≤ C·log t` — the off-line
  census bounded at log resolution — which is quantitative zero-set exhaustion, far beyond
  classical knowledge.  Nothing here touches it, and it remains open.

So: one named hypothesis closed, the register transport made unconditional, and both sides of
the Jensen target still standing.

## Harmonic content

The clock rate's own scale is `log t`, never unit `1`.  Its DC mode is computed exactly, not
estimated: `clockRate t = π·μ(t)` on the nose (an identity), and `μ`'s common mode is
`(1/2π)·log(t/2π)`.  So the DC term of the clock rate is exactly `½·log(t/(2π))` — the
coefficient `½` is the carrier's own, inherited from `Γℝ(s) = π^{−s/2}Γ(s/2)`, not a fitted
constant — and only the AC remainder, of size `O(t⁻²)`, is estimated.  The difficulty here was
never on the carrier: `Re Γℝ′/Γℝ(½+it)` is a smooth phase speed on the line.  It was the
chart's, in re-expressing that speed against `log t`.
-/

namespace CriticalLinePhasor.CarrierScale

/-- **The normalization identity.**  The carrier's clock rate is exactly `π` times the Zeta23
density `μ`: both name the same object, `Re (Γℝ′/Γℝ)(½+it) = ½·Re ψ(¼+it/2) − ½·log π`, in
charts differing by the factor `π`.  An identity, not an estimate — the DC mode evaluated
outright before any bound is taken. -/
theorem clockRate_eq_pi_mul_mu (t : ℝ) : clockRate t = Real.pi * Zeta23.mu t :=
  Zeta23.RvM.re_logDeriv_Gammaℝ_half t

/-- **The Stirling brick, sharp form.**  The clock rate is `½·log t + O(1)` with the leading
coefficient exactly `½` — the carrier's own DC coefficient, carried over from `Γℝ(s) = π^{−s/2}Γ(s/2)`
by the normalization identity.  Only the constant is existential. -/
theorem clockRate_log_bound_half :
    ∃ A' : ℝ, ∀ t : ℝ, 2 ≤ t → clockRate t ≤ A' + (1 / 2) * Real.log t := by
  obtain ⟨C, hC⟩ := Zeta23.StirlingVert.mu_stirling
  have hπ := Real.pi_pos
  -- the remainder constant is nonnegative: it dominates an absolute value at `τ = 1`
  have hC0 : 0 ≤ C := by
    have h := hC 1 (by norm_num)
    have h0 := abs_nonneg
      (Zeta23.mu 1 - (1 / (2 * Real.pi)) * Real.log (|(1 : ℝ)| / (2 * Real.pi)))
    simp only [one_pow, div_one] at h
    linarith
  refine ⟨-(1 / 2) * Real.log (2 * Real.pi) + Real.pi * C / 4, fun t ht => ?_⟩
  have ht0 : (0 : ℝ) < t := by linarith
  have habs : (1 : ℝ) ≤ |t| := by rw [abs_of_pos ht0]; linarith
  -- the AC remainder, evaluated on the window `t ≥ 2`
  have ht2 : (4 : ℝ) ≤ t ^ 2 := by nlinarith
  have hCt : C / t ^ 2 ≤ C / 4 := by gcongr
  -- the DC mode, in chart coordinates
  have hlog : Real.log (|t| / (2 * Real.pi)) = Real.log t - Real.log (2 * Real.pi) := by
    rw [abs_of_pos ht0, Real.log_div ht0.ne' (by positivity)]
  have hmu : Zeta23.mu t
      ≤ (1 / (2 * Real.pi)) * (Real.log t - Real.log (2 * Real.pi)) + C / 4 := by
    have h := (abs_le.mp (hC t habs)).2
    rw [hlog] at h
    linarith
  have hfin : Real.pi * ((1 / (2 * Real.pi)) * (Real.log t - Real.log (2 * Real.pi)) + C / 4)
      = (-(1 / 2) * Real.log (2 * Real.pi) + Real.pi * C / 4) + (1 / 2) * Real.log t := by
    field_simp
    ring
  calc clockRate t = Real.pi * Zeta23.mu t := clockRate_eq_pi_mul_mu t
    _ ≤ Real.pi * ((1 / (2 * Real.pi)) * (Real.log t - Real.log (2 * Real.pi)) + C / 4) := by
        exact mul_le_mul_of_nonneg_left hmu hπ.le
    _ = _ := hfin

/-- **The Stirling brick**, in exactly the shape `carrierJensenBound_of_clockBound` asks for:
the hypothesis `hclock` is discharged. -/
theorem clockRate_log_bound :
    ∃ A' B' : ℝ, ∀ t : ℝ, 2 ≤ t → clockRate t ≤ A' + B' * Real.log t := by
  obtain ⟨A', hA'⟩ := clockRate_log_bound_half
  exact ⟨A', 1 / 2, hA'⟩

/-- **`hclock` discharged.**  The native register now implies the chart register with no Γ-side
hypothesis left standing: `CarrierJensenClockBound` alone yields `CarrierJensenBound`.  The
chart's `log`-coefficient is halved, the carrier's own factor.

`CarrierJensenClockBound` is itself unproven — here and everywhere in this tree — so this does
**not** prove `CarrierJensenBound`; it removes the Γ-side input from the implication between
them.  See the scope note at the head of this file for the two sides and their strengths. -/
theorem carrierJensenBound_of_clockBound_unconditional {A B : ℝ} (hB : 0 ≤ B)
    (h : CarrierJensenClockBound A B) :
    ∃ A'' : ℝ, CarrierJensenBound A'' (B * (1 / 2)) := by
  obtain ⟨A', hA'⟩ := clockRate_log_bound_half
  exact ⟨A + B * A', carrierJensenBound_of_clockBound A B A' (1 / 2) hB hA' h⟩

end CriticalLinePhasor.CarrierScale

#print axioms CriticalLinePhasor.CarrierScale.clockRate_eq_pi_mul_mu
#print axioms CriticalLinePhasor.CarrierScale.clockRate_log_bound_half
#print axioms CriticalLinePhasor.CarrierScale.clockRate_log_bound
#print axioms CriticalLinePhasor.CarrierScale.carrierJensenBound_of_clockBound_unconditional
