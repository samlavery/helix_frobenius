import RequestProject.HodgeSeedFork

/-!
# The fork closed: fully frozen contradicts the drift

The Hodge fork (`HodgeSeedFork`) pinned certified strands to the μ₆ boundary set;
the drift branch is the compiled Sato–Tate chain.  This file closes their
incompatibility with one exact common-mode identity — no moment matrix, no
compactness, no measure theory:

* `trace_mu6_identity` — **the μ₆ common mode of the trace ladder**: for any sixth
  root of unity, `2·S₂ - S₄ = 1` exactly, where `S_r` is the literal rank-`r`
  symmetric-power Satake trace (the relation `α⁴ = α⁻²` collapses the ladder);
* `frozen_average_relation` — a fully certified seed's prime averages therefore
  satisfy `2·avg₂(n) - avg₄(n) = 1` at every stage — the common mode is constant,
  computed exactly, before any limit;
* `frozen_violates_cancellation` — hence the per-rank cancellation fails: the
  ranks `2` and `4` cannot both average to zero;
* `frozen_not_equidistributed` — with the compiled biconditional, a fully frozen
  seed does **not** equidistribute against the carrier measure.

Together with `maass_satoTate_of_cancellation`, the fork is now two-sided at one
seed object: rational (certified) data freeze and provably do not drift; the drift
branch requires the generic (non-Galois-type) case — Sato–Tate's own hypothesis,
compiled.  No `axiom`, no `sorry`.
-/

open Filter Topology

namespace CriticalLinePhasor.FrozenDrift

open CriticalLinePhasor.GeneralSeed CriticalLinePhasor.MaassSatoTate
open CriticalLinePhasor.SatoTateCarrier3D CriticalLinePhasor.HodgeSeedFork

/-- **The μ₆ common mode of the trace ladder**: for a sixth root of unity the
rank-`2` and rank-`4` symmetric-power Satake traces satisfy `2·S₂ - S₄ = 1`
exactly — `α⁴ = α⁻²` collapses the ladder. -/
theorem trace_mu6_identity {α : ℂ} (h6 : α ^ 6 = 1) :
    2 * symmetricPowerSatakeTrace α 2 - symmetricPowerSatakeTrace α 4 = 1 := by
  have hα : α ≠ 0 := by
    intro h0
    rw [h0] at h6
    simp at h6
  unfold symmetricPowerSatakeTrace
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  field_simp
  linear_combination (1 - α ^ 2) * h6

/-- A fully certified seed's prime averages satisfy the constant relation
`2·avg₂ - avg₄ = 1` at every stage. -/
theorem frozen_average_relation (M : MaassEigenData) (hC : MaassTowerCeiling M)
    (certAll : ∀ p : Nat.Primes, LatticeCertificate M p) (n : ℕ) :
    2 * arithmeticSymmetricPowerPrimeAverage (maassSatoTateFamily M hC) 2 n
      - arithmeticSymmetricPowerPrimeAverage (maassSatoTateFamily M hC) 4 n = 1 := by
  unfold arithmeticSymmetricPowerPrimeAverage
  have hterm : ∀ i : Fin (n + 1),
      2 * (symmetricPowerSatakeTrace
            ((maassSatoTateFamily M hC).tower (nthPrime i)).value 2).re
        - (symmetricPowerSatakeTrace
            ((maassSatoTateFamily M hC).tower (nthPrime i)).value 4).re = 1 := by
    intro i
    have h6 : ((maassSatoTateFamily M hC).tower (nthPrime i)).value ^ 6 = 1 := by
      show (SatakeSeed.ofMaass M).satake (nthPrime i) ^ 6 = 1
      exact seed_freeze M hC _ (certAll _)
    have hid := trace_mu6_identity h6
    have hre := congrArg Complex.re hid
    simpa [Complex.sub_re, Complex.mul_re] using hre
  have hSums : (∑ i : Fin (n + 1),
        (2 * (symmetricPowerSatakeTrace
            ((maassSatoTateFamily M hC).tower (nthPrime i)).value 2).re
          - (symmetricPowerSatakeTrace
            ((maassSatoTateFamily M hC).tower (nthPrime i)).value 4).re))
      = ((n + 1 : ℕ) : ℝ) := by
    rw [Finset.sum_congr rfl fun i _ => hterm i]
    simp
  have hexpand : (∑ i : Fin (n + 1),
        (2 * (symmetricPowerSatakeTrace
            ((maassSatoTateFamily M hC).tower (nthPrime i)).value 2).re
          - (symmetricPowerSatakeTrace
            ((maassSatoTateFamily M hC).tower (nthPrime i)).value 4).re))
      = 2 * (∑ i : Fin (n + 1), (symmetricPowerSatakeTrace
            ((maassSatoTateFamily M hC).tower (nthPrime i)).value 2).re)
        - ∑ i : Fin (n + 1), (symmetricPowerSatakeTrace
            ((maassSatoTateFamily M hC).tower (nthPrime i)).value 4).re := by
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
  have h2 : 2 * (∑ i : Fin (n + 1), (symmetricPowerSatakeTrace
        ((maassSatoTateFamily M hC).tower (nthPrime i)).value 2).re)
      - ∑ i : Fin (n + 1), (symmetricPowerSatakeTrace
        ((maassSatoTateFamily M hC).tower (nthPrime i)).value 4).re
      = ((n + 1 : ℕ) : ℝ) := by
    rw [← hexpand]
    exact hSums
  have hcast : (((n + 1 : ℕ) : ℝ)) ≠ 0 := by
    exact_mod_cast Nat.succ_ne_zero n
  field_simp
  push_cast at h2 ⊢
  linarith [h2]

/-- **The frozen case fails the cancellation**: the ranks `2` and `4` cannot both
average to zero. -/
theorem frozen_violates_cancellation (M : MaassEigenData) (hC : MaassTowerCeiling M)
    (certAll : ∀ p : Nat.Primes, LatticeCertificate M p) :
    ¬(∀ r : ℕ, 1 ≤ r →
      Tendsto (fun n =>
        arithmeticSymmetricPowerPrimeAverage (maassSatoTateFamily M hC) r n)
        atTop (nhds 0)) := by
  intro h
  have h2 := h 2 (by norm_num)
  have h4 := h 4 (by norm_num)
  have hcomb : Tendsto (fun n =>
      2 * arithmeticSymmetricPowerPrimeAverage (maassSatoTateFamily M hC) 2 n
        - arithmeticSymmetricPowerPrimeAverage (maassSatoTateFamily M hC) 4 n)
      atTop (nhds 0) := by
    have := (h2.const_mul (2 : ℝ)).sub h4
    simpa using this
  have hconst : (fun n =>
      2 * arithmeticSymmetricPowerPrimeAverage (maassSatoTateFamily M hC) 2 n
        - arithmeticSymmetricPowerPrimeAverage (maassSatoTateFamily M hC) 4 n)
      = fun _ => (1 : ℝ) := funext fun n => frozen_average_relation M hC certAll n
  rw [hconst] at hcomb
  exact one_ne_zero (tendsto_nhds_unique tendsto_const_nhds hcomb)

/-- **The fork closed**: a fully frozen (everywhere-certified) seed does not
equidistribute against the carrier measure — rational data provably do not
drift. -/
theorem frozen_not_equidistributed (M : MaassEigenData) (hC : MaassTowerCeiling M)
    (certAll : ∀ p : Nat.Primes, LatticeCertificate M p) :
    ¬ Tendsto (empiricalPrimeCarrierMeasure (maassSatoTateFamily M hC).angle) atTop
      (nhds carrierProbability) :=
  fun h => frozen_violates_cancellation M hC certAll
    ((maass_satoTate_iff M hC).mpr h)

end CriticalLinePhasor.FrozenDrift

#print axioms CriticalLinePhasor.FrozenDrift.trace_mu6_identity
#print axioms CriticalLinePhasor.FrozenDrift.frozen_average_relation
#print axioms CriticalLinePhasor.FrozenDrift.frozen_violates_cancellation
#print axioms CriticalLinePhasor.FrozenDrift.frozen_not_equidistributed
