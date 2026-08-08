import RequestProject.MaassSatoTateClosure

/-!
# Rankin–Selberg positivity, extracted at the seed surface

The two classical engines behind the Sato–Tate inputs — the Jacquet–Shalika
ceiling and the one-line nonvanishing — both run on Rankin–Selberg positivity.
This file extracts the compilable core at the house surface:

* `trace_conj_of_unit` / `trace_real_of_unit` — the symmetric-power Satake trace
  of a unit-modulus strand is real (the ladder is conjugation-symmetric), so its
  square is a genuine nonnegative real: the diagonal Rankin–Selberg local
  weights are nonnegative;
* `RSSquareSurface` — **the Rankin–Selberg square of a real self-dual surface**:
  coefficients `a(n)²`, again a surface (bound `2A`), with every coefficient a
  nonnegative real (`rsSquare_nonneg`, `rsSquare_im`);
* `rsSquare_dirichlet_nonneg` — its Dirichlet readout is nonnegative at every
  real point, junk-robustly — **the Landau-ready statement**: a nonnegative
  Dirichlet series, prepared for the Landau singularity lemma and the ceiling
  extraction;
* `hl_trace_positivity` — **the 3–4–1 inequality in trace coordinates**: for a
  unit strand, `2 + 2·(S₁).re + (S₂).re = (1 + 2·Re α)² ≥ 0` — the house form
  of the Hoffstein–Lockhart/de la Vallée-Poussin positivity that powers
  one-line nonvanishing, exact (a square, not an estimate).

Register.  The named next brick is the local Cauchy step: with
`G` the geometric column, the Rankin–Selberg local coefficient satisfies
`rs_k − rs_{k−2} = S_k(α)²` — the two-variable Cauchy identity in telescoped
form, whose proof route is the pair of three-term recursions (both sides solve
the `{α², 1, α⁻²}` recursion; three base cases close it).  That identity turns
the trace-square positivity above into per-coefficient positivity of the full
local Rankin–Selberg factor.  No `axiom`, no `sorry`.
-/

open Complex

namespace CriticalLinePhasor.RSPositivity

open CriticalLinePhasor.SatoTateCarrier3D CriticalLinePhasor.RamifiedMechanism
open CriticalLinePhasor.CarrierTheta

/-! ## The unit-strand trace is real -/

/-- The symmetric-power trace of a unit strand is conjugation-fixed: the ladder
`j ↔ r - j` is the conjugation symmetry. -/
theorem trace_conj_of_unit {α : ℂ} (hα : ‖α‖ = 1) (r : ℕ) :
    (starRingEnd ℂ) (symmetricPowerSatakeTrace α r) = symmetricPowerSatakeTrace α r := by
  have hinv : α⁻¹ = (starRingEnd ℂ) α := Complex.inv_eq_conj hα
  have hne : α ≠ 0 := by
    intro h0
    rw [h0] at hα
    simp at hα
  unfold symmetricPowerSatakeTrace
  rw [map_sum]
  rw [← Finset.sum_range_reflect]
  apply Finset.sum_congr rfl
  intro j hj
  have hjle : j ≤ r := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  rw [map_mul, map_pow, map_pow, ← hinv, map_inv₀, ← hinv, inv_inv]
  rw [show r + 1 - 1 - j = r - j from by omega]
  rw [show r - (r - j) = j from by omega]
  ring

/-- The unit-strand trace is real. -/
theorem trace_real_of_unit {α : ℂ} (hα : ‖α‖ = 1) (r : ℕ) :
    (symmetricPowerSatakeTrace α r).im = 0 := by
  have h := trace_conj_of_unit hα r
  have := congrArg Complex.im h
  simp only [Complex.conj_im] at this
  linarith

/-- The diagonal Rankin–Selberg local weight — the trace square — is a
nonnegative real. -/
theorem trace_sq_nonneg {α : ℂ} (hα : ‖α‖ = 1) (r : ℕ) :
    0 ≤ ((symmetricPowerSatakeTrace α r) ^ 2).re := by
  have him := trace_real_of_unit hα r
  rw [sq, Complex.mul_re, him]
  simp only [mul_zero, sub_zero]
  exact mul_self_nonneg _

/-! ## The Rankin–Selberg square surface -/

/-- **The Rankin–Selberg square of a real self-dual surface**: coefficients
`a(n)²`, again a polynomially-bounded surface. -/
noncomputable def RSSquareSurface (P : CoefficientSurface)
    (_hreal : ∀ n : ℕ, (starRingEnd ℂ) (P.a n) = P.a n) : CoefficientSurface where
  a := fun n => (P.a n) ^ 2
  adual := fun n => (P.a n) ^ 2
  A := 2 * P.A
  a_bound := fun n => by
    rw [sq, norm_mul, two_mul, pow_add]
    exact mul_le_mul (P.a_bound n) (P.a_bound n) (norm_nonneg _) (by positivity)
  adual_bound := fun n => by
    rw [sq, norm_mul, two_mul, pow_add]
    exact mul_le_mul (P.a_bound n) (P.a_bound n) (norm_nonneg _) (by positivity)

/-- Every Rankin–Selberg square coefficient is a nonnegative real. -/
theorem rsSquare_nonneg (P : CoefficientSurface)
    (hreal : ∀ n : ℕ, (starRingEnd ℂ) (P.a n) = P.a n) (n : ℕ) :
    0 ≤ ((RSSquareSurface P hreal).a n).re := by
  show 0 ≤ ((P.a n) ^ 2).re
  have him : (P.a n).im = 0 := by
    have := congrArg Complex.im (hreal n)
    simp only [Complex.conj_im] at this
    linarith
  rw [sq, Complex.mul_re, him]
  simp only [mul_zero, sub_zero]
  exact mul_self_nonneg _

theorem rsSquare_im (P : CoefficientSurface)
    (hreal : ∀ n : ℕ, (starRingEnd ℂ) (P.a n) = P.a n) (n : ℕ) :
    ((RSSquareSurface P hreal).a n).im = 0 := by
  show ((P.a n) ^ 2).im = 0
  have him : (P.a n).im = 0 := by
    have := congrArg Complex.im (hreal n)
    simp only [Complex.conj_im] at this
    linarith
  rw [sq, Complex.mul_im, him]
  simp

/-- **The Landau-ready statement**: the Rankin–Selberg square's Dirichlet readout
is nonnegative at every real point — junk-robustly (a divergent readout reads
`0`). -/
theorem rsSquare_dirichlet_nonneg (P : CoefficientSurface)
    (hreal : ∀ n : ℕ, (starRingEnd ℂ) (P.a n) = P.a n) (σ : ℝ) :
    0 ≤ (CriticalLinePhasor.CarrierTheta.dirichlet
      ((RSSquareSurface P hreal).a) ((σ : ℝ) : ℂ)).re := by
  unfold CriticalLinePhasor.CarrierTheta.dirichlet
  by_cases hsum : Summable (fun n : ℕ =>
      (RSSquareSurface P hreal).a n * ((n + 1 : ℕ) : ℂ) ^ (-((σ : ℝ) : ℂ)))
  · have hre : (∑' n : ℕ, (RSSquareSurface P hreal).a n *
        ((n + 1 : ℕ) : ℂ) ^ (-((σ : ℝ) : ℂ))).re
        = ∑' n : ℕ, ((RSSquareSurface P hreal).a n *
            ((n + 1 : ℕ) : ℂ) ^ (-((σ : ℝ) : ℂ))).re := by
      have h := Complex.reCLM.map_tsum hsum
      simpa using h
    rw [hre]
    apply tsum_nonneg
    intro n
    show 0 ≤ ((RSSquareSurface P hreal).a n * ((n + 1 : ℕ) : ℂ) ^ (-((σ : ℝ) : ℂ))).re
    have hpow : (((n + 1 : ℕ) : ℂ)) ^ (-((σ : ℝ) : ℂ))
        = ((((n + 1 : ℕ) : ℝ)) ^ (-σ : ℝ) : ℝ) := by
      rw [show (-((σ : ℝ) : ℂ)) = (((-σ : ℝ)) : ℂ) by push_cast; ring]
      rw [show (((n + 1 : ℕ) : ℂ)) = ((((n + 1 : ℕ) : ℝ)) : ℂ) by push_cast; ring]
      rw [← Complex.ofReal_cpow (by positivity)]
    rw [hpow, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
    rw [rsSquare_im P hreal n]
    have h1 := rsSquare_nonneg P hreal n
    have h2 : (0 : ℝ) ≤ (((n + 1 : ℕ) : ℝ)) ^ (-σ : ℝ) := by positivity
    simp only [mul_zero, sub_zero]
    exact mul_nonneg h1 h2
  · rw [tsum_eq_zero_of_not_summable hsum]
    simp

/-! ## The 3–4–1 positivity in trace coordinates -/

/-- **The house 3–4–1**: for a unit strand,
`2 + 2·(S₁).re + (S₂).re = (1 + 2·Re α)²` — the Hoffstein–Lockhart/de la
Vallée-Poussin positivity, exact. -/
theorem hl_trace_positivity {α : ℂ} (hα : ‖α‖ = 1) :
    0 ≤ 2 + 2 * (symmetricPowerSatakeTrace α 1).re
      + (symmetricPowerSatakeTrace α 2).re := by
  have hinv : α⁻¹ = (starRingEnd ℂ) α := Complex.inv_eq_conj hα
  have hns : Complex.normSq α = 1 := by
    rw [Complex.normSq_eq_norm_sq, hα]
    norm_num
  have hnorm : α.re ^ 2 + α.im ^ 2 = 1 := by
    have h2 := hns
    rw [Complex.normSq_apply] at h2
    nlinarith [h2]
  have hmul : α * (starRingEnd ℂ) α = 1 := by
    rw [Complex.mul_conj, hns]
    norm_num
  have hS1val : symmetricPowerSatakeTrace α 1 = α + (starRingEnd ℂ) α := by
    unfold symmetricPowerSatakeTrace
    rw [Finset.sum_range_succ, Finset.sum_range_one, hinv]
    norm_num
  have hS2val : symmetricPowerSatakeTrace α 2
      = α ^ 2 + 1 + ((starRingEnd ℂ) α) ^ 2 := by
    unfold symmetricPowerSatakeTrace
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one, hinv]
    norm_num
    exact hmul
  have hS1 : (symmetricPowerSatakeTrace α 1).re = 2 * α.re := by
    rw [hS1val]
    simp only [Complex.add_re, Complex.conj_re]
    ring
  have hS2 : (symmetricPowerSatakeTrace α 2).re = 4 * α.re ^ 2 - 1 := by
    rw [hS2val]
    simp only [Complex.add_re, Complex.one_re]
    rw [sq α, Complex.mul_re, sq ((starRingEnd ℂ) α), Complex.mul_re]
    simp only [Complex.conj_re, Complex.conj_im]
    nlinarith [hnorm]
  rw [hS1, hS2]
  nlinarith [sq_nonneg (1 + 2 * α.re)]

end CriticalLinePhasor.RSPositivity

#print axioms CriticalLinePhasor.RSPositivity.trace_real_of_unit
#print axioms CriticalLinePhasor.RSPositivity.trace_sq_nonneg
#print axioms CriticalLinePhasor.RSPositivity.rsSquare_nonneg
#print axioms CriticalLinePhasor.RSPositivity.rsSquare_dirichlet_nonneg
#print axioms CriticalLinePhasor.RSPositivity.hl_trace_positivity
