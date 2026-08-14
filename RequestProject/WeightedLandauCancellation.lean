import Mathlib.NumberTheory.Divisors
import Mathlib.Order.Interval.Finset.Floor
import Zeta23.Statement.SeamClosed

/-!
# The weighted Landau cancellation owed at its native scale

This file records the single finite weighted sum left by the discrete second-moment reduction.
Everything is unfolded into finite arithmetic over integers and the genuine nontrivial zeros of
Mathlib's `riemannZeta`.

For `x = T ^ θ`, the coefficient used below is

`a_x(n) = (1 - log n / log x) * Λ(n) / (π * √n)` for `0 < n ≤ x`, and `0` otherwise.

Thus

`w_x(k) = Σ_(mn=k) a_x(m) a_x(n)`

is a finite nonnegative divisor convolution when `1 < x`.  With `𝓁(T) = log(T / (2π))`,
`Z_T = {ρ : ζ(ρ)=0, 0<Re ρ<1, T<Im ρ<2T}`, and multiplicity `m_ρ`, put

`A_T(k) = N_T⁻¹ Σ_(ρ∈Z_T) m_ρ cos(Im(ρ) log k)`

and

`M_T(k) = N_T⁻¹ (-(T/(2π)) Λ(k)/√k)`.

The owed remainder at its own scale is exactly

`R(T,θ) = Σ_(T log T < k ≤ T^(2θ)) w_(T^θ)(k) * (A_T(k) - M_T(k))`.

`owedWeightedLandauBound θ` states that, for fixed `θ ∈ (1/2,1]`, this is eventually at
most `0.026 * θ² * 𝓁(T)² / (12π²)`.

Search audit run before construction:

* repository: `rg -n -i 'Landau|Gonek|vonMangoldt|zero.*sum|cos.*log|weighted.*sum'`
* Zeta23: `rg -n -i 'Landau|zeroCount|vonMangoldt|cos.*log|sum.*cos' ../zeta-23-lean`
* Mathlib: `rg -n 'divisorsAntidiagonal|factorPairs|factor_pairs|floor.*lt_iff|le_floor'`
* Mathlib reindexing/complex algebra:
  `rg -n 'sum_fiberwise|sum_bij|sum_product|sum_mul_sum|exp_mul_I|mul_re|re_sum'`
* semantic searches: `lean_leansearch` for finite product-map fibers and real parts of complex
  exponentials; `lean_loogle` for `Finset.sum_fiberwise_of_maps_to` and
  `Finset.sum_filter_add_sum_filter_not`

The exact DC split is `rawWeightedCosine_eq_main_add_remainder`: the raw zero average equals the
explicit Landau-main sum plus this one remainder.
-/

open scoped ArithmeticFunction BigOperators
open Set

namespace CriticalLinePhasor.WeightedLandauCancellation

noncomputable section

/-- The prime-polynomial length `x = T^θ`. -/
def xScale (T θ : ℝ) : ℝ := T ^ θ

/-- The triangular Selberg/von-Mangoldt coefficient, extended by zero off `0 < n ≤ x`. -/
def taperedCoefficient (x : ℝ) (n : ℕ) : ℝ :=
  if 0 < n ∧ (n : ℝ) ≤ x then
    (1 - Real.log n / Real.log x) * ArithmeticFunction.vonMangoldt n /
      (Real.pi * Real.sqrt n)
  else
    0

/-- The numerator of `a_x(n)`, including the finite support cutoff. -/
def taperedNumerator (x : ℝ) (n : ℕ) : ℝ :=
  if 0 < n ∧ (n : ℝ) ≤ x then
    (1 - Real.log n / Real.log x) * ArithmeticFunction.vonMangoldt n
  else
    0

/-- The divisor-convolution weight `w_x(k) = Σ_(mn=k) a_x(m)a_x(n)`. -/
def productWeight (x : ℝ) (k : ℕ) : ℝ :=
  ∑ p ∈ k.divisorsAntidiagonal, taperedCoefficient x p.1 * taperedCoefficient x p.2

/-- The displayed form
`(π²√k)⁻¹ Σ_(mn=k) taper_x(m)taper_x(n)Λ(m)Λ(n)`, with both cutoffs explicit. -/
def displayedProductWeight (x : ℝ) (k : ℕ) : ℝ :=
  1 / (Real.pi ^ 2 * Real.sqrt k) *
    ∑ p ∈ k.divisorsAntidiagonal, taperedNumerator x p.1 * taperedNumerator x p.2

/-- The genuine nontrivial zeta zeros in the strict ordinate window `T < γ < 2T`. -/
def openZeroWindow (Z : Zeta23.ZeroConfig) (T : ℝ) : Set ℂ :=
  Z.carrier ∩ {ρ | T < ρ.im ∧ ρ.im < 2 * T}

theorem openZeroWindow_finite (Z : Zeta23.ZeroConfig) (T : ℝ) :
    (openZeroWindow Z T).Finite := by
  refine (Z.finite_window T (2 * T)).subset ?_
  rintro ρ ⟨hρ, hlo, hhi⟩
  exact ⟨hρ, hlo, hhi.le⟩

/-- `N_T`, counting the strict dyadic zero window with analytic multiplicity. -/
def openZeroCount (Z : Zeta23.ZeroConfig) (T : ℝ) : ℕ :=
  ∑ᶠ ρ ∈ openZeroWindow Z T, Z.mult ρ

/-- The multiplicity-weighted cosine sum over the strict dyadic zero window. -/
def zeroCosineSum (Z : Zeta23.ZeroConfig) (T : ℝ) (k : ℕ) : ℝ :=
  ∑ᶠ ρ ∈ openZeroWindow Z T, (Z.mult ρ : ℝ) * Real.cos (ρ.im * Real.log k)

/-- The normalized zero-side cosine reading `N_T⁻¹ Σ_ρ m_ρ cos(γ log k)`. -/
def zeroCosineAverage (Z : Zeta23.ZeroConfig) (T : ℝ) (k : ℕ) : ℝ :=
  zeroCosineSum Z T k / openZeroCount Z T

/-- The normalized Landau main term `N_T⁻¹ (-(T/(2π)) Λ(k)/√k)`. -/
def landauMain (Z : Zeta23.ZeroConfig) (T : ℝ) (k : ℕ) : ℝ :=
  (-(T / (2 * Real.pi)) * ArithmeticFunction.vonMangoldt k / Real.sqrt k) /
    openZeroCount Z T

/-- The integer range `T log T < k ≤ T^(2θ)`, represented exactly by natural floors. -/
def owedRange (T θ : ℝ) : Finset ℕ :=
  Finset.Ioc ⌊T * Real.log T⌋₊ ⌊T ^ (2 * θ)⌋₊

/-- The raw weighted zero-side cosine sum on the unresolved integer range. -/
def rawWeightedCosine (Z : Zeta23.ZeroConfig) (T θ : ℝ) : ℝ :=
  ∑ k ∈ owedRange T θ, productWeight (xScale T θ) k * zeroCosineAverage Z T k

/-- The fully explicit weighted contribution of the Landau main terms. -/
def weightedLandauMain (Z : Zeta23.ZeroConfig) (T θ : ℝ) : ℝ :=
  ∑ k ∈ owedRange T θ, productWeight (xScale T θ) k * landauMain Z T k

/-- The sole cancellation remainder after subtracting the Landau main term at every integer. -/
def weightedLandauRemainder (Z : Zeta23.ZeroConfig) (T θ : ℝ) : ℝ :=
  ∑ k ∈ owedRange T θ,
    productWeight (xScale T θ) k * (zeroCosineAverage Z T k - landauMain Z T k)

/-- The requested explicit allowance, with decimal `0.026 = 13/500` interpreted exactly. -/
def owedAllowance (T θ : ℝ) : ℝ :=
  0.026 * θ ^ 2 * Zeta23.l T ^ 2 / (12 * Real.pi ^ 2)

/-- The one input, for a fixed exponent `θ ∈ (1/2,1]`, in eventual (`T → ∞`) form. -/
def owedWeightedLandauBound (θ : ℝ) : Prop :=
  1 / 2 < θ ∧ θ ≤ 1 ∧
    ∃ T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T → 2 ≤ T →
      weightedLandauRemainder Zeta23.zetaZeroConfig T θ ≤ owedAllowance T θ

@[simp] theorem taperedCoefficient_of_mem {x : ℝ} {n : ℕ} (hn : 0 < n)
    (hnx : (n : ℝ) ≤ x) :
    taperedCoefficient x n =
      (1 - Real.log n / Real.log x) * ArithmeticFunction.vonMangoldt n /
        (Real.pi * Real.sqrt n) := by
  simp [taperedCoefficient, hn, hnx]

theorem taperedCoefficient_eq_numerator_div (x : ℝ) (n : ℕ) :
    taperedCoefficient x n = taperedNumerator x n / (Real.pi * Real.sqrt n) := by
  by_cases hn : 0 < n ∧ (n : ℝ) ≤ x <;>
    simp [taperedCoefficient, taperedNumerator, hn]

/-- The convolution definition of `productWeight` is exactly the displayed `w(k)` formula. -/
theorem productWeight_eq_displayedProductWeight (x : ℝ) (k : ℕ) :
    productWeight x k = displayedProductWeight x k := by
  rw [productWeight, displayedProductWeight, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  rw [taperedCoefficient_eq_numerator_div, taperedCoefficient_eq_numerator_div]
  have hprod : p.1 * p.2 = k := (Nat.mem_divisorsAntidiagonal.mp hp).1
  have hsqrt : Real.sqrt p.1 * Real.sqrt p.2 = Real.sqrt k := by
    rw [← Real.sqrt_mul (Nat.cast_nonneg p.1), ← Nat.cast_mul, hprod]
  have hden :
      (Real.pi * Real.sqrt p.1) * (Real.pi * Real.sqrt p.2) =
        Real.pi ^ 2 * Real.sqrt k := by
    rw [← hsqrt]
    ring
  rw [div_mul_div_comm, hden]
  ring

theorem taperedCoefficient_nonneg {x : ℝ} (hx : 1 < x) (n : ℕ) :
    0 ≤ taperedCoefficient x n := by
  by_cases hn : 0 < n ∧ (n : ℝ) ≤ x
  · rw [taperedCoefficient, if_pos hn]
    have hlogx : 0 < Real.log x := Real.log_pos hx
    have hlogn : Real.log n ≤ Real.log x := Real.log_le_log (by exact_mod_cast hn.1) hn.2
    have htaper : 0 ≤ 1 - Real.log n / Real.log x := by
      rw [sub_nonneg, div_le_one hlogx]
      exact hlogn
    exact div_nonneg
      (mul_nonneg htaper ArithmeticFunction.vonMangoldt_nonneg)
      (mul_nonneg Real.pi_pos.le (Real.sqrt_nonneg n))
  · simp [taperedCoefficient, hn]

/-- The displayed divisor-convolution weights really are nonnegative. -/
theorem productWeight_nonneg {x : ℝ} (hx : 1 < x) (k : ℕ) :
    0 ≤ productWeight x k := by
  exact Finset.sum_nonneg fun p _ =>
    mul_nonneg (taperedCoefficient_nonneg hx p.1) (taperedCoefficient_nonneg hx p.2)

/-- Membership in `owedRange` is exactly the displayed real interval. -/
theorem mem_owedRange_iff {T θ : ℝ} {k : ℕ} (hlower : 0 ≤ T * Real.log T)
    (hupper : 0 ≤ T ^ (2 * θ)) :
    k ∈ owedRange T θ ↔ T * Real.log T < (k : ℝ) ∧ (k : ℝ) ≤ T ^ (2 * θ) := by
  rw [owedRange, ← Nat.cast_mem_Ioc_iff hlower hupper]
  rfl

/-- DC separation: explicit Landau mains plus exactly one cancellation remainder. -/
theorem rawWeightedCosine_eq_main_add_remainder (Z : Zeta23.ZeroConfig) (T θ : ℝ) :
    rawWeightedCosine Z T θ =
      weightedLandauMain Z T θ + weightedLandauRemainder Z T θ := by
  rw [rawWeightedCosine, weightedLandauMain, weightedLandauRemainder,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  ring

/-! ## Exact prime-polynomial square and quadrature normal form -/

/-- The actual finite support `0 < n ≤ ⌊x⌋₊` of the tapered prime polynomial. -/
def primeIndex (x : ℝ) : Finset ℕ :=
  Finset.Ioc 0 ⌊x⌋₊

/-- The exact nonzero product support `0 < k ≤ ⌊x⌋₊²`.  This is contained in `k ≤ x²`; all
coefficients in the remaining floor-padding are zero. -/
def productIndex (x : ℝ) : Finset ℕ :=
  Finset.Ioc 0 (⌊x⌋₊ ^ 2)

/-- The literal integer interpretation of `0 < k ≤ x²`. -/
def squaredProductIndex (x : ℝ) : Finset ℕ :=
  Finset.Ioc 0 ⌊x ^ 2⌋₊

/-- The phase `n^(it)`, written as an exponential to avoid any branch convention for powers. -/
def multiplicativePhase (t : ℝ) (n : ℕ) : ℂ :=
  Complex.exp (((t * Real.log n : ℝ) : ℂ) * Complex.I)

/-- The tapered prime polynomial `P_x(t)`. -/
def primePolynomial (x t : ℝ) : ℂ :=
  ∑ n ∈ primeIndex x, (taperedCoefficient x n : ℂ) * multiplicativePhase t n

/-- Its real (focal/slope) quadrature `A_x(t)`. -/
def realChannel (x t : ℝ) : ℝ :=
  (primePolynomial x t).re

/-- Its imaginary quadrature `B_x(t)`. -/
def quadratureChannel (x t : ℝ) : ℝ :=
  (primePolynomial x t).im

/-- The product polynomial with the divisor-convolution coefficients `w_x(k)`. -/
def productPolynomial (x t : ℝ) : ℂ :=
  ∑ k ∈ productIndex x, (productWeight x k : ℂ) * multiplicativePhase t k

/-- The full cosine channel of the product polynomial. -/
def productCosine (x t : ℝ) : ℝ :=
  ∑ k ∈ productIndex x, productWeight x k * Real.cos (t * Real.log k)

/-- The low-product part `k ≤ K`. -/
def lowProductCosine (x : ℝ) (K : ℕ) (t : ℝ) : ℝ :=
  ∑ k ∈ (productIndex x).filter (fun k => k ≤ K),
    productWeight x k * Real.cos (t * Real.log k)

/-- The super-band/high-product projection `K < k`. -/
def highProductCosine (x : ℝ) (K : ℕ) (t : ℝ) : ℝ :=
  ∑ k ∈ (productIndex x).filter (fun k => K < k),
    productWeight x k * Real.cos (t * Real.log k)

/-- Operator-level complex high-product projection `Π_{>K}(P_x²)`. -/
def highProductProjection (x : ℝ) (K : ℕ) (t : ℝ) : ℂ :=
  ∑ k ∈ (productIndex x).filter (fun k => K < k),
    (productWeight x k : ℂ) * multiplicativePhase t k

/-- The phase is multiplicative on positive natural inputs. -/
theorem multiplicativePhase_mul (t : ℝ) {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    multiplicativePhase t m * multiplicativePhase t n =
      multiplicativePhase t (m * n) := by
  rw [multiplicativePhase, multiplicativePhase, multiplicativePhase, ← Complex.exp_add]
  congr 2
  rw [Nat.cast_mul, Real.log_mul (by positivity) (by positivity)]
  push_cast
  ring

/-- Reindexing one product fiber gives exactly the existing divisor-convolution weight. -/
theorem boundedProductWeight_eq_productWeight {x : ℝ} (hx : 0 ≤ x)
    {k : ℕ} (hk : k ∈ productIndex x) :
    (∑ p ∈ (primeIndex x ×ˢ primeIndex x).filter (fun p => p.1 * p.2 = k),
      taperedCoefficient x p.1 * taperedCoefficient x p.2) = productWeight x k := by
  have hk0 : k ≠ 0 := by
    intro hkz
    subst k
    rw [productIndex, Finset.mem_Ioc] at hk
    omega
  rw [productWeight]
  apply Finset.sum_subset
  · intro p hp
    rw [Finset.mem_filter] at hp
    rw [Nat.mem_divisorsAntidiagonal]
    exact ⟨hp.2, hk0⟩
  · intro p hpdiv hpnot
    have hpdata := Nat.mem_divisorsAntidiagonal.mp hpdiv
    have hp1 : 0 < p.1 :=
      Nat.pos_of_ne_zero fun h => hk0 (by simpa [h] using hpdata.1.symm)
    have hp2 : 0 < p.2 :=
      Nat.pos_of_ne_zero fun h => hk0 (by simpa [h] using hpdata.1.symm)
    by_cases h1 : p.1 ∈ primeIndex x
    · have h2 : p.2 ∉ primeIndex x := by
        intro h2
        exact hpnot (Finset.mem_filter.mpr
          ⟨Finset.mem_product.mpr ⟨h1, h2⟩, hpdata.1⟩)
      rw [primeIndex, Finset.mem_Ioc] at h2
      have hxf : x < (p.2 : ℝ) :=
        (Nat.floor_lt hx).mp (lt_of_not_ge (fun hle => h2 ⟨hp2, hle⟩))
      have hzero : taperedCoefficient x p.2 = 0 := by
        simp [taperedCoefficient, hp2, not_le.mpr hxf]
      simp [hzero]
    · rw [primeIndex, Finset.mem_Ioc] at h1
      have hxf : x < (p.1 : ℝ) :=
        (Nat.floor_lt hx).mp (lt_of_not_ge (fun hle => h1 ⟨hp1, hle⟩))
      have hzero : taperedCoefficient x p.1 = 0 := by
        simp [taperedCoefficient, hp1, not_le.mpr hxf]
      simp [hzero]

/-- Every convolution coefficient above the actual support `⌊x⌋₊²` vanishes. -/
theorem productWeight_eq_zero_above_productIndex {x : ℝ} (hx : 0 ≤ x)
    {k : ℕ} (hk : 0 < k) (hlarge : ⌊x⌋₊ ^ 2 < k) :
    productWeight x k = 0 := by
  rw [productWeight]
  apply Finset.sum_eq_zero
  intro p hp
  have hpdata := Nat.mem_divisorsAntidiagonal.mp hp
  have hp1 : 0 < p.1 :=
    Nat.pos_of_ne_zero fun h => (Nat.ne_of_gt hk) (by simpa [h] using hpdata.1.symm)
  have hp2 : 0 < p.2 :=
    Nat.pos_of_ne_zero fun h => (Nat.ne_of_gt hk) (by simpa [h] using hpdata.1.symm)
  by_cases h1 : p.1 ≤ ⌊x⌋₊
  · have h2large : ⌊x⌋₊ < p.2 := by
      by_contra hnot
      have h2 : p.2 ≤ ⌊x⌋₊ := Nat.le_of_not_gt hnot
      rw [← hpdata.1] at hlarge
      nlinarith
    have hxf : x < (p.2 : ℝ) := (Nat.floor_lt hx).mp h2large
    have hzero : taperedCoefficient x p.2 = 0 := by
      simp [taperedCoefficient, hp2, not_le.mpr hxf]
    simp [hzero]
  · have h1large : ⌊x⌋₊ < p.1 := Nat.lt_of_not_ge h1
    have hxf : x < (p.1 : ℝ) := (Nat.floor_lt hx).mp h1large
    have hzero : taperedCoefficient x p.1 = 0 := by
      simp [taperedCoefficient, hp1, not_le.mpr hxf]
    simp [hzero]

/-- The nonzero support is contained in the literal range `k ≤ x²`. -/
theorem productIndex_subset_squaredProductIndex {x : ℝ} (hx : 0 ≤ x) :
    productIndex x ⊆ squaredProductIndex x := by
  intro k hk
  rw [productIndex, Finset.mem_Ioc] at hk
  rw [squaredProductIndex, Finset.mem_Ioc]
  refine ⟨hk.1, ?_⟩
  have hfloor : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le hx
  have hsquare : ((⌊x⌋₊ ^ 2 : ℕ) : ℝ) ≤ x ^ 2 := by
    push_cast
    nlinarith
  have hfloorSquare : ⌊x⌋₊ ^ 2 ≤ ⌊x ^ 2⌋₊ :=
    (Nat.le_floor_iff (sq_nonneg x)).mpr hsquare
  exact hk.2.trans hfloorSquare

/-- Exact Dirichlet-convolution identity: `P_x(t)² = Σ_k w_x(k) k^(it)`. -/
theorem primePolynomial_sq_eq_productPolynomial {x : ℝ} (hx : 0 ≤ x) (t : ℝ) :
    primePolynomial x t ^ 2 = productPolynomial x t := by
  rw [pow_two, primePolynomial, productPolynomial, Finset.sum_mul_sum]
  rw [← Finset.sum_product']
  let S := primeIndex x ×ˢ primeIndex x
  have hmap : ∀ p ∈ S, p.1 * p.2 ∈ productIndex x := by
    intro p hp
    simp only [S, Finset.mem_product, primeIndex, Finset.mem_Ioc] at hp
    rw [productIndex, Finset.mem_Ioc]
    exact ⟨Nat.mul_pos hp.1.1 hp.2.1, by nlinarith [hp.1.2, hp.2.2]⟩
  rw [← Finset.sum_fiberwise_of_maps_to hmap
    (fun p : ℕ × ℕ =>
      ((taperedCoefficient x p.1 : ℂ) * multiplicativePhase t p.1) *
        ((taperedCoefficient x p.2 : ℂ) * multiplicativePhase t p.2))]
  apply Finset.sum_congr rfl
  intro k hk
  rw [← boundedProductWeight_eq_productWeight hx hk]
  push_cast
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro p hp
  rw [Finset.mem_filter] at hp
  have hpmem := hp.1
  simp only [S, Finset.mem_product, primeIndex, Finset.mem_Ioc] at hpmem
  calc
    ((taperedCoefficient x p.1 : ℂ) * multiplicativePhase t p.1) *
        ((taperedCoefficient x p.2 : ℂ) * multiplicativePhase t p.2) =
      ((taperedCoefficient x p.1 : ℂ) * (taperedCoefficient x p.2 : ℂ)) *
        (multiplicativePhase t p.1 * multiplicativePhase t p.2) := by ring
    _ = ((taperedCoefficient x p.1 : ℂ) * (taperedCoefficient x p.2 : ℂ)) *
        multiplicativePhase t (p.1 * p.2) := by
      rw [multiplicativePhase_mul t hpmem.1.1 hpmem.2.1]
    _ = ((taperedCoefficient x p.1 : ℂ) * (taperedCoefficient x p.2 : ℂ)) *
        multiplicativePhase t k := by
      rw [hp.2]

/-- The same product polynomial padded to the literal range `0 < k ≤ x²`. -/
def squaredProductPolynomial (x t : ℝ) : ℂ :=
  ∑ k ∈ squaredProductIndex x, (productWeight x k : ℂ) * multiplicativePhase t k

/-- Padding from `⌊x⌋₊²` through `⌊x²⌋₊` contributes only zero coefficients. -/
theorem productPolynomial_eq_squaredProductPolynomial {x : ℝ} (hx : 0 ≤ x) (t : ℝ) :
    productPolynomial x t = squaredProductPolynomial x t := by
  rw [productPolynomial, squaredProductPolynomial]
  apply Finset.sum_subset (productIndex_subset_squaredProductIndex hx)
  intro k hkbig hksmall
  rw [squaredProductIndex, Finset.mem_Ioc] at hkbig
  have hlarge : ⌊x⌋₊ ^ 2 < k := by
    by_contra hnot
    exact hksmall (by
      rw [productIndex, Finset.mem_Ioc]
      exact ⟨hkbig.1, Nat.le_of_not_gt hnot⟩)
  rw [productWeight_eq_zero_above_productIndex hx hkbig.1 hlarge]
  simp

/-- Literal displayed form: `P_x(t)² = Σ_(0<k≤x²) w_x(k) k^(it)`. -/
theorem primePolynomial_sq_eq_squaredProductPolynomial {x : ℝ} (hx : 0 ≤ x) (t : ℝ) :
    primePolynomial x t ^ 2 = squaredProductPolynomial x t := by
  rw [primePolynomial_sq_eq_productPolynomial hx t,
    productPolynomial_eq_squaredProductPolynomial hx t]

/-- Taking the real part of the product polynomial produces its weighted cosine sum. -/
theorem productPolynomial_re_eq_productCosine (x t : ℝ) :
    (productPolynomial x t).re = productCosine x t := by
  rw [productPolynomial, productCosine, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [Complex.mul_re]
  simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  rw [show (multiplicativePhase t k).re = Real.cos (t * Real.log k) from
    Complex.exp_ofReal_mul_I_re _]

/-- The semiprime cosine wall is exactly the real/imaginary quadrature imbalance `A²-B²`. -/
theorem productCosine_eq_quadratureImbalance {x : ℝ} (hx : 0 ≤ x) (t : ℝ) :
    productCosine x t = realChannel x t ^ 2 - quadratureChannel x t ^ 2 := by
  have h := congrArg Complex.re (primePolynomial_sq_eq_productPolynomial hx t)
  rw [productPolynomial_re_eq_productCosine] at h
  simpa only [pow_two, Complex.mul_re, realChannel, quadratureChannel] using h.symm

/-- The full product cosine energy splits exactly into low and super-band pieces. -/
theorem productCosine_eq_low_add_high (x : ℝ) (K : ℕ) (t : ℝ) :
    productCosine x t = lowProductCosine x K t + highProductCosine x K t := by
  rw [productCosine, lowProductCosine, highProductCosine,
    ← Finset.sum_filter_add_sum_filter_not (s := productIndex x) (p := fun k => k ≤ K)]
  simp only [not_le]

/-- Closed form for the hard zone: `Z_{K,x}=A_x²-B_x²-L_{K,x}`. -/
theorem highProductCosine_eq_quadratureImbalance_sub_low {x : ℝ} (hx : 0 ≤ x)
    (K : ℕ) (t : ℝ) :
    highProductCosine x K t =
      realChannel x t ^ 2 - quadratureChannel x t ^ 2 - lowProductCosine x K t := by
  rw [← productCosine_eq_quadratureImbalance hx t,
    productCosine_eq_low_add_high x K t]
  ring

/-- Energy-transfer form solving the same identity for the required imaginary energy. -/
theorem quadratureChannel_sq_eq_real_sub_low_sub_high {x : ℝ} (hx : 0 ≤ x)
    (K : ℕ) (t : ℝ) :
    quadratureChannel x t ^ 2 =
      realChannel x t ^ 2 - lowProductCosine x K t - highProductCosine x K t := by
  have himbalance := productCosine_eq_quadratureImbalance hx t
  have hsplit := productCosine_eq_low_add_high x K t
  linarith

/-- The real readout of `Π_{>K}(P_x²)` is precisely the high-product cosine zone. -/
theorem highProductProjection_re_eq_highProductCosine (x : ℝ) (K : ℕ) (t : ℝ) :
    (highProductProjection x K t).re = highProductCosine x K t := by
  rw [highProductProjection, highProductCosine, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [Complex.mul_re]
  simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  rw [show (multiplicativePhase t k).re = Real.cos (t * Real.log k) from
    Complex.exp_ofReal_mul_I_re _]

/-- The requested hard zone with cutoff `K = ⌊T log T⌋₊`. -/
def zoneCosine (T θ t : ℝ) : ℝ :=
  highProductCosine (xScale T θ) ⌊T * Real.log T⌋₊ t

/-- The explicitly computable complementary low-product polynomial. -/
def zoneLowProductCosine (T θ t : ℝ) : ℝ :=
  lowProductCosine (xScale T θ) ⌊T * Real.log T⌋₊ t

/-- Operator-level form of the requested zone, `Π_{>T log T}(P_(T^θ)²)`. -/
def zoneProjection (T θ t : ℝ) : ℂ :=
  highProductProjection (xScale T θ) ⌊T * Real.log T⌋₊ t

/-- Final pointwise normal form
`Z_zone(t) = A_(T^θ)(t)² - B_(T^θ)(t)² - L_(T,θ)(t)`. -/
theorem zoneCosine_eq_quadratureImbalance_sub_low {T θ t : ℝ} (hT : 0 ≤ T) :
    zoneCosine T θ t =
      realChannel (xScale T θ) t ^ 2 - quadratureChannel (xScale T θ) t ^ 2 -
        zoneLowProductCosine T θ t := by
  exact highProductCosine_eq_quadratureImbalance_sub_low (Real.rpow_nonneg hT θ)
    ⌊T * Real.log T⌋₊ t

/-- The zone is exactly the real readout of its high-product projection. -/
theorem zoneProjection_re_eq_zoneCosine (T θ t : ℝ) :
    (zoneProjection T θ t).re = zoneCosine T θ t := by
  exact highProductProjection_re_eq_highProductCosine
    (xScale T θ) ⌊T * Real.log T⌋₊ t

end

end CriticalLinePhasor.WeightedLandauCancellation

#print axioms CriticalLinePhasor.WeightedLandauCancellation.openZeroWindow_finite
#print axioms CriticalLinePhasor.WeightedLandauCancellation.taperedCoefficient_nonneg
#print axioms CriticalLinePhasor.WeightedLandauCancellation.productWeight_eq_displayedProductWeight
#print axioms CriticalLinePhasor.WeightedLandauCancellation.productWeight_nonneg
#print axioms CriticalLinePhasor.WeightedLandauCancellation.mem_owedRange_iff
#print axioms CriticalLinePhasor.WeightedLandauCancellation.rawWeightedCosine_eq_main_add_remainder
#print axioms CriticalLinePhasor.WeightedLandauCancellation.multiplicativePhase_mul
#print axioms CriticalLinePhasor.WeightedLandauCancellation.boundedProductWeight_eq_productWeight
#print axioms CriticalLinePhasor.WeightedLandauCancellation.productWeight_eq_zero_above_productIndex
#print axioms CriticalLinePhasor.WeightedLandauCancellation.productIndex_subset_squaredProductIndex
#print axioms CriticalLinePhasor.WeightedLandauCancellation.primePolynomial_sq_eq_productPolynomial
#print axioms CriticalLinePhasor.WeightedLandauCancellation.productPolynomial_eq_squaredProductPolynomial
#print axioms CriticalLinePhasor.WeightedLandauCancellation.primePolynomial_sq_eq_squaredProductPolynomial
#print axioms CriticalLinePhasor.WeightedLandauCancellation.productCosine_eq_quadratureImbalance
#print axioms CriticalLinePhasor.WeightedLandauCancellation.productCosine_eq_low_add_high
#print axioms CriticalLinePhasor.WeightedLandauCancellation.highProductCosine_eq_quadratureImbalance_sub_low
#print axioms CriticalLinePhasor.WeightedLandauCancellation.quadratureChannel_sq_eq_real_sub_low_sub_high
#print axioms CriticalLinePhasor.WeightedLandauCancellation.highProductProjection_re_eq_highProductCosine
#print axioms CriticalLinePhasor.WeightedLandauCancellation.zoneCosine_eq_quadratureImbalance_sub_low
#print axioms CriticalLinePhasor.WeightedLandauCancellation.zoneProjection_re_eq_zoneCosine
