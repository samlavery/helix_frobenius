import RequestProject.SeatToeplitzRegister
import RequestProject.ClockPoissonBarycenter

/-!
# The reflection law of the Toeplitz functional, and the unitary clock as a cotangent (ledger 623)

* `toeplitzCoeff_reflect`: if a function's jets at `s` are `S′_m = (−1)^{m−1} S_m` — the jets of
  `f(1 − ·)` at `s` in terms of the jets of `f` at `1 − s` — then its Toeplitz coefficients at
  anchor `s` (with `d = 2σ − 1`) are minus those of `f` at `1 − s` (with `−d`). So the reflected
  Euler side enters the ordered face's constitution with a negative sign:
  `T^A(s) = U(s)·I + D(s) − T^{P_Q}(1 − s)` (checked numerically to 1e−14, att623).
* `symClock_logDeriv_eq_cot`: the symmetrized unitary clock's log-derivative is a cotangent,
  `logDeriv (symClock e^{iθ} ℓ) z = (ℓ/2)·cot((zℓ − θ)/2)`: the pure symmetric partial-fraction sum
  over its line zeros with no constant term (Mathlib `cot_series_rep`). This is the constitutional
  source of the positivity of the clock faces: a unitary clock's transported measure is a positive
  atomic measure on the circle; the Poisson barycenter (compiled,
  `unitaryClocks_poisson_barycenter_antiEulerFace`) averages such measures; the conduction clock on
  the channel is that average plus the uniform `log q/|d|`, since
  `logDeriv_s(1 − q^{1−s}) = logDeriv_s(symClock (1/r) ℓ) − ℓ/2`. Right of the line the same `ℓ/2`
  is subtracted from the Euler face, which is why Euler factors are not positive there (att623 C3).
-/

open Complex Finset
open CriticalLinePhasor.ChiralityHB

namespace CriticalLinePhasor.SeatingLedger

/-- **The reflection law of the Toeplitz functional.** -/
theorem toeplitzCoeff_reflect (d : ℂ) (S : ℕ → ℂ) (n : ℕ) :
    toeplitzCoeff d (fun m => (-1) ^ (m - 1) * S m) n = - toeplitzCoeff (-d) S n := by
  cases n with
  | zero =>
    simp only [toeplitzCoeff]
    have : ((-1 : ℂ) ^ (1 - 1) * S 1).re = (S 1).re := by simp
    rw [this, div_neg, neg_neg]
  | succ n =>
    simp only [toeplitzCoeff]
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl (fun i hi => ?_)
    rw [Finset.mem_range] at hi
    rw [show n + 2 - i - 1 = (n - i) + 1 by omega, pow_succ, neg_pow]
    ring

/-- **The unitary clock is a cotangent**: `logDeriv (symClock e^{iθ} ℓ) z = (ℓ/2) cot((zℓ − θ)/2)`. -/
theorem symClock_logDeriv_eq_cot (θ ℓ : ℝ) (z : ℂ)
    (hne : symClock (Complex.exp (I * θ)) ℓ z ≠ 0) :
    logDeriv (symClock (Complex.exp (I * θ)) ℓ) z
      = ((ℓ : ℂ) / 2) * Complex.cot ((z * ℓ - θ) / 2) := by
  set φ : ℂ := (z * ℓ - θ) / 2 with hφ
  have hA : Complex.exp (I * z * ℓ / 2) = Complex.exp (I * θ / 2) * Complex.exp (φ * I) := by
    rw [← Complex.exp_add]; congr 1; rw [hφ]; ring
  have hG : Complex.exp (I * θ) * Complex.exp (-(I * z * ℓ / 2))
      = Complex.exp (I * θ / 2) * Complex.exp (-φ * I) := by
    rw [← Complex.exp_add, ← Complex.exp_add]; congr 1; rw [hφ]; ring
  have hsym : symClock (Complex.exp (I * θ)) ℓ z
      = Complex.exp (I * θ / 2) * (Complex.exp (φ * I) - Complex.exp (-φ * I)) := by
    show Complex.exp (I * z * ℓ / 2) - Complex.exp (I * θ) * Complex.exp (-(I * z * ℓ / 2)) = _
    rw [hA, hG]; ring
  have hEE : Complex.exp (φ * I) - Complex.exp (-φ * I) ≠ 0 := by
    intro h0; apply hne; rw [hsym, h0, mul_zero]
  rw [symClock_logDeriv_eq, hA, hG, Complex.cot_eq_cos_div_sin]
  simp only [Complex.cos, Complex.sin]
  have hexp : Complex.exp (I * θ / 2) ≠ 0 := Complex.exp_ne_zero _
  have hI : (I : ℂ) ≠ 0 := I_ne_zero
  have hEE' : Complex.exp (-φ * I) - Complex.exp (φ * I) ≠ 0 := by
    intro h0; apply hEE; linear_combination -h0
  field_simp
  ring_nf
  simp only [Complex.I_sq]
  rw [show (-cexp (I * φ) + cexp (-(I * φ))) = -(cexp (I * φ) - cexp (-(I * φ))) by ring, inv_neg]
  ring

end CriticalLinePhasor.SeatingLedger
