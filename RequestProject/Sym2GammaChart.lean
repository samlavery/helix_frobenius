import RequestProject.HeckeMultiplicativityWire

/-!
# The `Sym²` readout in the prescribed `Γℂ`-product chart

`Sym2Wire.sym2_readout` puts the peeled Rankin readout of the carrier profile in a
degree-four `Γℝ`-chart with shifts `[0, 1, k−1, k]`.  The prescribed completion consumed by
the coupling machinery (`cpsPolynomialFullPrimalCompletedReadout`) is a `Γℂ`-product,
`C^s · ∏_{μ ∈ μs} Γℂ(s+μ) · L(coeff, s)`.  Legendre duplication reconciles the two exactly:
`Γℝ(s)·Γℝ(s+1) = Γℂ(s)` (Mathlib `Gammaℝ_mul_Gammaℝ_add_one`), applied at `s` and at
`s + k − 1`, collapses the four real factors to two complex ones with shifts `[0, k−1]`.

* `gammaR_quadruple_eq_gammaC_pair` — the chart identity
  `Γℝ(s)Γℝ(s+1)Γℝ(s+k−1)Γℝ(s+k) = Γℂ(s)·Γℂ(s+k−1)`;
* `sym2_readout_gammaC` — the `Sym²` landing in the prescribed chart:
  `mellin (θ_μ(θ̄_f − ‖f‖²)) s = 2^{−k} · Γℂ(s) · Γℂ(s+k−1) · L(sym2Bank, s)` on `2 < Re s`.

Both are unconditional: `sym2_readout` carries no Hecke hypothesis, and duplication is a
Mathlib identity.  The Hecke input enters only where the bank's local factors are read as
the literal `Sym²`-Satake traces (`sym2Bank_prime_pow`), which is not used here.

No `axiom`, no `sorry`.
-/

open Complex UpperHalfPlane ArithmeticFunction LSeries
open scoped Real MatrixGroups LSeries.notation ArithmeticFunction.Moebius

namespace CriticalLinePhasor.Sym2Wire

variable {k : ℤ} {f : CuspForm 𝒮ℒ k}

/-- **Legendre duplication on the `Sym²` chart**: the degree-four `Γℝ`-product with shifts
`[0, 1, k−1, k]` is the degree-two `Γℂ`-product with shifts `[0, k−1]`.  Two applications of
`Γℝ(s)·Γℝ(s+1) = Γℂ(s)`, at `s` and at `s + k − 1`. -/
theorem gammaR_quadruple_eq_gammaC_pair (k : ℤ) (s : ℂ) :
    Gammaℝ s * Gammaℝ (s + 1) * Gammaℝ (s + (k : ℂ) - 1) * Gammaℝ (s + (k : ℂ))
      = Gammaℂ s * Gammaℂ (s + (k : ℂ) - 1) := by
  have h1 : Gammaℝ s * Gammaℝ (s + 1) = Gammaℂ s :=
    Gammaℝ_mul_Gammaℝ_add_one s
  have h2 : Gammaℝ (s + (k : ℂ) - 1) * Gammaℝ (s + (k : ℂ))
      = Gammaℂ (s + (k : ℂ) - 1) := by
    have := Gammaℝ_mul_Gammaℝ_add_one (s + (k : ℂ) - 1)
    rwa [show s + (k : ℂ) - 1 + 1 = s + (k : ℂ) by ring] at this
  calc Gammaℝ s * Gammaℝ (s + 1) * Gammaℝ (s + (k : ℂ) - 1) * Gammaℝ (s + (k : ℂ))
      = (Gammaℝ s * Gammaℝ (s + 1)) *
          (Gammaℝ (s + (k : ℂ) - 1) * Gammaℝ (s + (k : ℂ))) := by ring
    _ = Gammaℂ s * Gammaℂ (s + (k : ℂ) - 1) := by rw [h1, h2]

/-- **The `Sym²` landing in the prescribed `Γℂ`-product chart.**  On `2 < Re s`,
`mellin (θ_μ(θ̄_f − ‖f‖²)) s = 2^{−k} · Γℂ(s) · Γℂ(s+k−1) · L(sym2Bank, s)`.

This is `sym2_readout` with the four real Gamma factors collapsed by duplication.  The
right-hand side is now exactly the shape of `cpsPolynomialFullPrimalCompletedReadout` at
conductor `1` and shift list `[0, k−1]`, with the constant `2^{−k}` absorbable into the
coefficient bank.  Unconditional. -/
theorem sym2_readout_gammaC (hk : 0 ≤ k) {s : ℂ} (hs : 2 < s.re) :
    mellin (CriticalLinePhasor.Sym2Registration.peeledProfile k f) s =
      (2 : ℂ) ^ (-(k : ℂ)) * (Gammaℂ s * Gammaℂ (s + (k : ℂ) - 1)) *
        LSeries (⇑(sym2Bank f)) s := by
  rw [sym2_readout (f := f) hk hs, gammaR_quadruple_eq_gammaC_pair k s]

end CriticalLinePhasor.Sym2Wire

#print axioms CriticalLinePhasor.Sym2Wire.gammaR_quadruple_eq_gammaC_pair
#print axioms CriticalLinePhasor.Sym2Wire.sym2_readout_gammaC
