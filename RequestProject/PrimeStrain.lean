import RequestProject.RegistrationStations

/-!
# The prime-forced strain (ledger 601)

The registry's strain is the finite prime-clock bank of the explicit formula for `S`, with the
χ = 1 transfer coefficient `1/π`:

  `Ŝ_X(t) = −(1/π) Σ_{n ≤ X} Λ(n) sin(t log n) / (√n log n)`.

This file defines it, proves it continuous and bounded by `B_X = (1/π) Σ_{n ≤ X} Λ(n)/(√n log n)`,
and instantiates the station theorems on it: `primeStations X n := station (primeStrain X) n`,
`primeStation_spec`, and the RH door `nontrivialZeros_online_of_primeResid`, whose hypotheses are

* a starting index `n₀` with `regClock (primeStrain X) 10 < n₀ − 3/2` (always available),
* the first station at or below `58` (a numeric fact about `ϑ` and the bank; not yet compiled),
* the residual law `|R(t_n) − R(t_{n₀})| < 1` at every station — the open node.
-/

open Complex Finset Filter Topology Set
open CriticalLinePhasor.CarrierScale (theta clockRate)

namespace CriticalLinePhasor.ContourArgument

/-- One clock of the bank: `Λ(n) sin(t log n) / (√n log n)`. -/
noncomputable def strainClock (n : ℕ) (t : ℝ) : ℝ :=
  (ArithmeticFunction.vonMangoldt n) * Real.sin (t * Real.log n) / (Real.sqrt n * Real.log n)

/-- The amplitude of one clock: `Λ(n)/(√n log n)`. -/
noncomputable def strainAmp (n : ℕ) : ℝ :=
  (ArithmeticFunction.vonMangoldt n) / (Real.sqrt n * Real.log n)

theorem strainClock_continuous (n : ℕ) : Continuous (strainClock n) := by
  unfold strainClock
  fun_prop

theorem abs_strainClock_le (n : ℕ) (t : ℝ) : |strainClock n t| ≤ |strainAmp n| := by
  unfold strainClock strainAmp
  have hsin : |Real.sin (t * Real.log n)| ≤ 1 := Real.abs_sin_le_one _
  calc |ArithmeticFunction.vonMangoldt n * Real.sin (t * Real.log n) / (Real.sqrt n * Real.log n)|
      = |ArithmeticFunction.vonMangoldt n / (Real.sqrt n * Real.log n)| * |Real.sin (t * Real.log n)| := by
        rw [← abs_mul]
        congr 1
        ring
    _ ≤ |ArithmeticFunction.vonMangoldt n / (Real.sqrt n * Real.log n)| * 1 :=
        mul_le_mul_of_nonneg_left hsin (abs_nonneg _)
    _ = |ArithmeticFunction.vonMangoldt n / (Real.sqrt n * Real.log n)| := mul_one _

/-- The prime-forced strain with cutoff `X`. -/
noncomputable def primeStrain (X : ℕ) (t : ℝ) : ℝ :=
  -(1 / Real.pi) * ∑ n ∈ range (X + 1), strainClock n t

/-- Its bound `B_X = (1/π) Σ |Λ(n)/(√n log n)|`. -/
noncomputable def primeStrainBound (X : ℕ) : ℝ :=
  (1 / Real.pi) * ∑ n ∈ range (X + 1), |strainAmp n|

theorem primeStrain_continuous (X : ℕ) : Continuous (primeStrain X) := by
  unfold primeStrain
  exact continuous_const.mul (continuous_finset_sum _ (fun n _ => strainClock_continuous n))

theorem abs_primeStrain_le (X : ℕ) (t : ℝ) : |primeStrain X t| ≤ primeStrainBound X := by
  unfold primeStrain primeStrainBound
  rw [abs_mul, abs_neg, abs_of_pos (by positivity : (0:ℝ) < 1 / Real.pi)]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact (Finset.abs_sum_le_sum_abs _ _).trans
    (Finset.sum_le_sum (fun n _ => abs_strainClock_le n t))

/-! ## The stations of the registry -/

/-- The registry's stations: `ϑ(t_n)/π + 3/2 + Ŝ_X(t_n) = n`, first crossing above `10`. -/
noncomputable def primeStation (X : ℕ) (n : ℕ) : ℝ := station (primeStrain X) n

theorem primeStation_spec (X : ℕ) {n : ℕ} (hn : regClock (primeStrain X) 10 < stationLevel n) :
    10 ≤ primeStation X n ∧
      theta (primeStation X n) / Real.pi + 3 / 2 + primeStrain X (primeStation X n) = n := by
  have h := station_spec (primeStrain_continuous X) (abs_primeStrain_le X) hn
  refine ⟨h.1, ?_⟩
  have h2 := h.2
  unfold regClock stationLevel at h2
  unfold primeStation
  linarith

/-- A starting index always exists: `n₀ = ⌈G(10)⌉₊ + 2`. -/
theorem primeStation_start (X : ℕ) :
    regClock (primeStrain X) 10 < stationLevel (⌈regClock (primeStrain X) 10⌉₊ + 2) := by
  unfold stationLevel
  push_cast
  linarith [Nat.le_ceil (regClock (primeStrain X) 10)]

/-- **The RH door on the registry's stations.** -/
theorem nontrivialZeros_online_of_primeResid (X : ℕ) {n₀ : ℕ}
    (hn₀ : regClock (primeStrain X) 10 < stationLevel n₀) (h58 : primeStation X n₀ ≤ 58)
    (hres : ∀ n, n₀ ≤ n →
      |resid (primeStrain X) (primeStation X n) - resid (primeStrain X) (primeStation X n₀)| < 1) :
    ∀ ρ ∈ ZD.NontrivialZeros, ρ.re = 1 / 2 :=
  nontrivialZeros_online_of_resid (primeStrain_continuous X) (abs_primeStrain_le X) hn₀ h58 hres

end CriticalLinePhasor.ContourArgument

#print axioms CriticalLinePhasor.ContourArgument.primeStation_spec
#print axioms CriticalLinePhasor.ContourArgument.nontrivialZeros_online_of_primeResid
