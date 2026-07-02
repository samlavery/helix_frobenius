# Audit: conditional theorems vs. unconditional

Audit test used throughout (the project's own criterion): a hypothesis is a *valid target* to
discharge only if doing so **neither assumes RH/GRH nor is circular**.  A statement being true and
"RH-strength" is **not** by itself a reason to leave it conditional — but a statement whose
*conclusion is logically equivalent to RH/GRH* cannot be discharged unconditionally without proving
RH/GRH, and a series identity valid only where the series converges absolutely is genuinely
restricted.

## 1. Conditionals that WERE made unconditional / tightened

* **`σ > 1` ⇒ `σ > 0` (the strip extension).**  The "fiber accumulates to the L-function" partial-sum
  convergence results were restricted to `Re s > 1`; they hold on the whole strip `Re s > 0`
  (unconditionally, via `LFunctionPhasor.dirichlet_strip_tendsto_LFunction`).  Updated:
  * `Faithfulness.fiber_accumulates_to_L` — now `Re s > 0` (non-principal `χ`).
  * `Faithfulness.faithful_all_L` — first conjunct now `Re s > 0` (non-principal `χ`).
  * `Faithfulness.faithful_principal_L_eta_strip` — the **principal** character (`= ζ`) covered on
    `Re s > 0 \ {1}` via the eta-twisted readout.
  (The `PerHeightConvergence` line results already used the strip extension.)

* **Redundant hypothesis removed.**  `HarmonicCell.zero_source_admissibility` carried a redundant
  `hρ : LFunction χ ρ = 0` (already contained in `hnontriv : NontrivialZeroChi χ ρ`); removed.

* **`IsHB` conditionals for a concrete structure function.**  Already handled by the existing
  `ConditionalToUnconditional.lean`: every `IsHB E`-conditional de Branges theorem is discharged
  unconditionally for the concrete Paley–Wiener `E` via `paleyWiener_isHB` (yielding e.g. the
  classical `sin_ne_zero_of_im_ne_zero`, `sin_zeros_real`, `sin_zeros_discrete`).

* **Spectral cancellation, nontrivial range.**  `CancellationEquivalence.nontrivial_cancellation_sets_coincide`
  — the spectral/`L` cancellation coincidence on the open strip `0 < Re s < 1` (trivial zeros
  excluded), fully unconditional.

## 2. Conditionals that are GENUINELY conditional (cannot be made unconditional)

These are not thought-terminators: each has a *machine-checked* reason it is RH-strength or
domain-restricted.

* **Self-adjoint realization of an arbitrary nontrivial zero = GRH.**  Any statement of the form
  "a nontrivial cancellation of `Lχ` is realized as a kernel of a *self-adjoint* operator"
  (`vonNeumannOp γ` or the diagonal generator `Aχ`) forces `Re s = 1/2` (von Neumann reality), so
  quantified over all nontrivial zeros it is **logically equivalent to GRH for `χ`**.  This is proved
  unconditionally as `SpectralFiber.nontrivial_real_generator_iff_GRH`-style equivalences and isolated
  as hypotheses:
  * `SelfAdjointGenerator.GRH_from_nontrivial_Aχ_realization` (from an `Aχ`-kernel realization),
  * `SpectralFiber.GRH_from_spectral_exhaustion` (from `SpectralExhaustion`).
  The realization/exhaustion hypothesis is the genuine RH-strength input — neither assumed nor proved.
  What *is* unconditional: the on-line realizations
  (`SpectralFiber.nontrivial_spectral_cancellation_to_real_generator_of_re_half`,
  `SpectralFiber.real_generator_on_critical_line`, `SelfAdjointGenerator.Aχ_kernel_realized`) and the
  reverse direction (`realGeneratorCancellation_re_half`).

* **`IsHB E` for a `Λ`-built (arithmetic) structure function = RH/GRH.**  Documented in
  `DeBranges.lean` / `ConditionalToUnconditional.lean`: discharging `IsHB E` for an `E` built from a
  Dirichlet `L`-function is exactly "no off-line zeros".  Genuinely conditional.

* **`HarmonicCell.zero_source_admissibility` / `nontrivial_zero_represented` (`hcrit : ρ.re = 1/2`).**
  A real source-height's represented point always has `Re = 1/2`; dropping `hcrit` for all nontrivial
  zeros is GRH.  Genuinely conditional.  (The `ProjectionPrimacy`/`EveryZeroAdmissible` principles in
  `HarmonicPencilCell.lean` / `AdmissibleEigenheight.lean` isolate exactly this GRH content.)

* **Absolute-convergence / Euler / von Mangoldt identities (`σ > 1`).**  `ClosedForm`
  (`*_eq_tsum`, `phasor_summable`, `regCarrier_eq_LFunction`, `etaTwist_eq_tsum`, …),
  `PrimePowerProbe` (`vonMangoldtChannel_eq_neg_logDeriv`, `LFunction_ne_zero_of_one_lt_re`,
  `noDominance_no_offline_zero`), `HelixPolarization` (`theoremC`, `summable_channelTerm`,
  `traceWeighted_eq_tsum_primes`), `Faithfulness.explicit_formula_prime_field`.  These are series /
  Euler-product / nonvanishing facts that are **false or divergent** for `Re s ≤ 1`; the `σ > 1`
  restriction is intrinsic, not a thought-terminator.  (The conjugation-symmetry stepping stones
  `HelixCollapseReality.completedRiemannZeta_conj_strip` already have full-`ℂ` versions
  `completedRiemannZeta_conj` / `completedRiemannZeta₀_conj`.)

## Summary

Every conditional that is dischargeable without assuming RH/GRH (and without leaving the region of
convergence) has been made unconditional; the remaining conditionals are each provably RH/GRH-strength
or intrinsically tied to absolute convergence, with the RH-strength content isolated as explicit,
unproved hypotheses (never assumed globally, no `sorry`, no `axiom`).
