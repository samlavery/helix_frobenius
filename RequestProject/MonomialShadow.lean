import RequestProject.FrozenDrift

/-!
# The monomial shadow detector: finite order at any `N`, one moment, constant gap

`FrozenDrift` closed the fork at the `μ₆` certificate.  The shadow that matters is
not a specific order: any *finite-order* (monomial / CM-type / Galois-type) Satake
family is a shadow, whatever its order.  This file detects all of them at once,
with an exact common mode:

* `trace_root_of_unity_re` — **the general common mode**: for any `α` with
  `α^N = 1` the rank-`N` symmetric-power Satake trace is *exactly* `1`, or `N+1`
  in the degenerate case `α² = 1`.  The rank-`N` ladder collapses to a geometric
  sum in `α⁻²` whose period is `N`;
* `one_le_trace_re` — hence the rank-`N` trace has real part `≥ 1`: a constant gap,
  uniform in the datum;
* `MonomialShadow` — a family-level shadow certificate: one common order `N` with
  `α_p^N = 1` at every prime;
* `shadow_average_ge_one` / `shadow_violates_cancellation` /
  `shadow_not_equidistributed` — **the detector**: a shadow forces
  `avg_N(n) ≥ 1` at every stage, so the rank-`N` cancellation fails and the family
  provably does not equidistribute — a *single* bounded-rank moment separates,
  with gap `1`;
* `no_shadow_of_equidistributed` — the contrapositive: a drifting family has no
  finite-order shadow at **any** order;
* `mu6Shadow` — the `ℤ[ζ₆]` Hodge certificate is the `N = 6` instance, so
  `FrozenDrift`'s conclusion is a corollary of the general detector.

Scope.  These are *rigidity and detectability* statements about the trace family:
which analytic behaviour a finite-order shadow forbids, and which single moment
witnesses it.  They say nothing about computational cost, query complexity, or
*recovery* of an inducing datum — no algorithm and no complexity model appears
here.  No `axiom`, no `sorry`.
-/

open Filter Topology

namespace CriticalLinePhasor.ShadowDetector

open CriticalLinePhasor.GeneralSeed CriticalLinePhasor.MaassSatoTate
open CriticalLinePhasor.SatoTateCarrier3D CriticalLinePhasor.HodgeSeedFork
open CriticalLinePhasor.FrozenDrift

/-! ## The general common mode of the rank-`N` ladder -/

/-- The rank-`N` ladder of a root of unity collapses to a geometric sum in `α⁻²`. -/
theorem trace_eq_geom {α : ℂ} {N : ℕ} (hN : 1 ≤ N) (h : α ^ N = 1) :
    symmetricPowerSatakeTrace α N = ∑ j ∈ Finset.range (N + 1), ((α ^ 2)⁻¹) ^ j := by
  have hα : α ≠ 0 := by
    intro h0
    rw [h0, zero_pow (by omega : N ≠ 0)] at h
    exact zero_ne_one h
  unfold symmetricPowerSatakeTrace
  refine Finset.sum_congr rfl fun j hj => ?_
  have hjle : j ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  have hsplit : α ^ (N - j) * α ^ j = 1 := by
    rw [← pow_add]
    rw [show N - j + j = N from by omega]
    exact h
  have hinv : α ^ (N - j) = (α ^ j)⁻¹ := by
    field_simp
    linear_combination hsplit
  rw [hinv]
  rw [show ((α : ℂ) ^ 2)⁻¹ ^ j = ((α ^ j)⁻¹) ^ 2 from by
    rw [← inv_pow, ← inv_pow, ← pow_mul, ← pow_mul, mul_comm]]
  ring

/-- **The general common mode**: for `α^N = 1` the rank-`N` trace is exactly `1`,
or `N+1` in the degenerate case `α² = 1`. -/
theorem trace_root_of_unity_re {α : ℂ} {N : ℕ} (hN : 1 ≤ N) (h : α ^ N = 1) :
    symmetricPowerSatakeTrace α N = if (α ^ 2)⁻¹ = 1 then ((N : ℂ) + 1) else 1 := by
  rw [trace_eq_geom hN h]
  set β : ℂ := (α ^ 2)⁻¹ with hβ
  have hβN : β ^ N = 1 := by
    have hkey : ((α ^ 2)⁻¹) ^ N = ((α ^ N) ^ 2)⁻¹ := by
      rw [inv_pow, ← pow_mul, ← pow_mul, Nat.mul_comm]
    rw [hβ, hkey, h, one_pow, inv_one]
  by_cases hb : β = 1
  · rw [if_pos hb, hb]
    simp
  · rw [if_neg hb]
    rw [geom_sum_eq hb]
    rw [pow_succ, hβN, one_mul]
    exact div_self (sub_ne_zero_of_ne hb)

/-- **The constant gap**: the rank-`N` trace of a root of unity has real part
`≥ 1`, uniformly in the datum. -/
theorem one_le_trace_re {α : ℂ} {N : ℕ} (hN : 1 ≤ N) (h : α ^ N = 1) :
    1 ≤ (symmetricPowerSatakeTrace α N).re := by
  rw [trace_root_of_unity_re hN h]
  by_cases hb : (α ^ 2)⁻¹ = 1
  · rw [if_pos hb]
    simp only [Complex.add_re, Complex.natCast_re, Complex.one_re]
    have : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
    linarith
  · rw [if_neg hb]
    simp

/-! ## The shadow certificate and the detector -/

/-- **A monomial shadow**: one common finite order at every prime — the
Galois-type / CM-type rigidity, at any order. -/
structure MonomialShadow (F : ArithmeticSatakePrimeFamily) where
  N : ℕ
  N_pos : 1 ≤ N
  freeze : ∀ p : Nat.Primes, (F.tower p).value ^ N = 1

/-- **The detector's statistic**: a shadow forces the rank-`N` prime average
`≥ 1` at every stage — one bounded-rank moment, constant gap. -/
theorem shadow_average_ge_one (F : ArithmeticSatakePrimeFamily)
    (S : MonomialShadow F) (n : ℕ) :
    1 ≤ arithmeticSymmetricPowerPrimeAverage F S.N n := by
  unfold arithmeticSymmetricPowerPrimeAverage
  have hterm : ∀ i : Fin (n + 1),
      1 ≤ (symmetricPowerSatakeTrace ((F.tower (nthPrime i)).value) S.N).re :=
    fun i => one_le_trace_re S.N_pos (S.freeze _)
  have hpos : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  have hsum : ((n + 1 : ℕ) : ℝ) ≤
      ∑ i : Fin (n + 1),
        (symmetricPowerSatakeTrace ((F.tower (nthPrime i)).value) S.N).re := by
    calc ((n + 1 : ℕ) : ℝ) = ∑ _i : Fin (n + 1), (1 : ℝ) := by simp
      _ ≤ ∑ i : Fin (n + 1),
            (symmetricPowerSatakeTrace ((F.tower (nthPrime i)).value) S.N).re :=
          Finset.sum_le_sum fun i _ => hterm i
  rw [one_div, inv_mul_eq_div, le_div_iff₀ hpos, one_mul]
  exact hsum

/-- **The detector fires**: a shadow makes the rank-`N` cancellation fail. -/
theorem shadow_violates_cancellation (F : ArithmeticSatakePrimeFamily)
    (S : MonomialShadow F) :
    ¬(∀ r : ℕ, 1 ≤ r →
      Tendsto (fun n => arithmeticSymmetricPowerPrimeAverage F r n) atTop (nhds 0)) := by
  intro h
  have hlim := h S.N S.N_pos
  have hle : (1 : ℝ) ≤ 0 :=
    ge_of_tendsto hlim (Eventually.of_forall fun n => shadow_average_ge_one F S n)
  linarith

/-- **A shadow forbids the drift**: a finite-order family provably does not
equidistribute against the carrier measure. -/
theorem shadow_not_equidistributed (F : ArithmeticSatakePrimeFamily)
    (S : MonomialShadow F) :
    ¬ Tendsto (empiricalPrimeCarrierMeasure F.angle) atTop (nhds carrierProbability) :=
  fun h => shadow_violates_cancellation F S
    ((arithmeticSatakeCancellation_iff_carrierEquidistribution F).mpr h)

/-- **The contrapositive — the drift forbids every shadow**: an equidistributing
family has no finite-order shadow at any order. -/
theorem no_shadow_of_equidistributed (F : ArithmeticSatakePrimeFamily)
    (h : Tendsto (empiricalPrimeCarrierMeasure F.angle) atTop
      (nhds carrierProbability)) :
    ¬ Nonempty (MonomialShadow F) :=
  fun ⟨S⟩ => shadow_not_equidistributed F S h

/-! ## The `μ₆` Hodge certificate as the `N = 6` instance -/

/-- The `ℤ[ζ₆]` Hodge certificate at every prime is a monomial shadow of order
`6`, so the `FrozenDrift` conclusion is a corollary of the general detector. -/
noncomputable def mu6Shadow (M : MaassEigenData) (hC : MaassTowerCeiling M)
    (certAll : ∀ p : Nat.Primes, LatticeCertificate M p) :
    MonomialShadow (maassSatoTateFamily M hC) where
  N := 6
  N_pos := by norm_num
  freeze := fun p => seed_freeze M hC p (certAll p)

/-- The seed-level corollary, re-derived from the general detector. -/
theorem mu6_not_equidistributed (M : MaassEigenData) (hC : MaassTowerCeiling M)
    (certAll : ∀ p : Nat.Primes, LatticeCertificate M p) :
    ¬ Tendsto (empiricalPrimeCarrierMeasure (maassSatoTateFamily M hC).angle) atTop
      (nhds carrierProbability) :=
  shadow_not_equidistributed _ (mu6Shadow M hC certAll)

end CriticalLinePhasor.ShadowDetector

#print axioms CriticalLinePhasor.ShadowDetector.trace_root_of_unity_re
#print axioms CriticalLinePhasor.ShadowDetector.one_le_trace_re
#print axioms CriticalLinePhasor.ShadowDetector.shadow_average_ge_one
#print axioms CriticalLinePhasor.ShadowDetector.shadow_violates_cancellation
#print axioms CriticalLinePhasor.ShadowDetector.shadow_not_equidistributed
#print axioms CriticalLinePhasor.ShadowDetector.no_shadow_of_equidistributed
#print axioms CriticalLinePhasor.ShadowDetector.mu6_not_equidistributed
