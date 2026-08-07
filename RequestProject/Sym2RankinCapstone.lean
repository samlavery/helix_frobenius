import RequestProject.Sym2RankinCoupling
import RequestProject.SymrBankAllRanks
import RequestProject.Sym2StandingWave

/-!
# The r = 2 rung, one theorem: coefficients, chart, functional equation, poles

The capstone of the `Sym²` benchmark: over the actual level-one eigen-datum — a cusp form
`f` of weight `k ≥ 2` with its typed Hecke package `H` — one quantified conclusion carries,
simultaneously:

1. **the coefficient passport** — the rank-uniform clock bank at `r = 2` is the
   independently-built `Sym²` convolution bank (`symrBank H 2 = sym2Bank f`), and both
   all-place coefficient banks of the rank-4 Rankin pair are the literal `L(f×f)` Euler
   datum `c = ζ ⋆ sym2Bank`;
2. **the Euler lines** — `ζ(s)·L(sym2Bank, s) = L(c, s)` and
   `ζ(2s)·L(μ⋆b, s) = L(sym2Bank, s)` on `2 < Re s`;
3. **the half-plane identification** — the completed transform of the coupled bank is
   `Γℂ(s)·Γℂ(s+k−1)·L(c, s)` on `2 < Re s`: the prescribed Deligne chart, the literal
   coefficients;
4. **the global functional equation** — `Λ(1−s) = Λ(s)` for every `s ∈ ℂ`;
5. **the polar structure** — residue `2^k·‖f‖²` at the edge `s = 1`, and the transform is
   entire away from its two booked poles;
6. **the peeled (`Sym²`) functional equation** — `Λζ(s)·Λ̄(1−s) = Λζ(1−s)·Λ̄(s)`, global
   and division-free, with edge regularity `ζ(s)⁻¹Λ̄(s) → ‖f‖²`.

The reflection input is the lattice theta transformation law carried through the Petersson
average — no automorphy of the target is consumed anywhere.  The hypotheses `0 ≤ k`,
`2 ≤ k` delimit the object class; `HeckeEigenData` is the typed classical seed package
that defines the eigenform.

No `axiom`, no `sorry`.
-/

open Finset ArithmeticFunction Complex UpperHalfPlane MeasureTheory
open scoped MatrixGroups Real LSeries.notation ArithmeticFunction.Moebius
  ArithmeticFunction.zeta

namespace CriticalLinePhasor.Sym2Rankin

open CriticalLinePhasor.GlobalHelix CriticalLinePhasor.Sym2Wire
open CriticalLinePhasor.SymrBank CriticalLinePhasor.Sym2Join
open CriticalLinePhasor.Unfolding CriticalLinePhasor.Sym2Registration

variable {k : ℤ} {f : CuspForm 𝒮ℒ k}

/-- The clean form of the half-plane identification: the `2^k·2^{−k}` gauge cancelled. -/
theorem sym2Rankin_lambda_eq' (H : HeckeEigenData f) (hk : 0 ≤ k) (hk2 : 2 ≤ k)
    {s : ℂ} (hs : 2 < s.re) :
    (sym2RankinPair H hk hk2).Λ s =
      Gammaℂ s * Gammaℂ (s + (k : ℂ) - 1) * LSeries (⇑(rankinBank f)) s := by
  rw [sym2Rankin_lambda_eq H hk hk2 hs, ← mul_assoc, ← mul_assoc,
    ← Complex.cpow_add _ _ two_ne_zero]
  simp

/-- **The r = 2 rung, one theorem.**  Over the actual eigen-datum, simultaneously: the
coefficient passport, the Euler lines, the prescribed-chart identification, the global
self-dual functional equation, the polar structure, and the peeled `Sym²` functional
equation with its edge regularity. -/
theorem sym2_rankin_rung (H : HeckeEigenData f) (hk : 0 ≤ k) (hk2 : 2 ≤ k) :
    -- 1. the coefficient passport
    (symrBank H 2 = sym2Bank f) ∧
    (∀ n : ℕ, cpsPolynomialPrimalCoeff (rankinSatakePair H) n = rankinBank f (n + 1)) ∧
    (∀ n : ℕ, cpsPolynomialDualCoeff (rankinSatakePair H) n = rankinBank f (n + 1)) ∧
    -- 2. the Euler lines
    (∀ s : ℂ, 2 < s.re →
      LSeries (⇑(rankinBank f)) s = riemannZeta s * LSeries (⇑(sym2Bank f)) s) ∧
    (∀ s : ℂ, 2 < s.re →
      riemannZeta (2 * s) *
          LSeries (⇑((μ : ArithmeticFunction ℂ) * rankinSquareNorm f)) s =
        LSeries (⇑(sym2Bank f)) s) ∧
    -- 3. the half-plane identification in the prescribed chart
    (∀ s : ℂ, 2 < s.re →
      (sym2RankinPair H hk hk2).Λ s =
        Gammaℂ s * Gammaℂ (s + (k : ℂ) - 1) * LSeries (⇑(rankinBank f)) s) ∧
    -- 4. the global functional equation
    (∀ s : ℂ, (sym2RankinPair H hk hk2).Λ (1 - s) = (sym2RankinPair H hk hk2).Λ s) ∧
    -- 5. the polar structure
    Filter.Tendsto (fun s : ℂ => (s - 1) * (sym2RankinPair H hk hk2).Λ s)
      (nhdsWithin 1 {(1 : ℂ)}ᶜ)
      (nhds ((2 : ℂ) ^ (k : ℂ) * ((peterssonMass k f : ℝ) : ℂ))) ∧
    Differentiable ℂ (sym2RankinPair H hk hk2).Λ₀ ∧
    -- 6. the peeled Sym² functional equation and its edge regularity
    (∀ s : ℂ, completedRiemannZeta s * (rsAveragedWeakFEPair f hk).Λ (1 - s) =
      completedRiemannZeta (1 - s) * (rsAveragedWeakFEPair f hk).Λ s) ∧
    Filter.Tendsto (fun s : ℂ => (riemannZeta s)⁻¹ * (rsAveragedWeakFEPair f hk).Λ s)
      (nhdsWithin 1 {(1 : ℂ)}ᶜ) (nhds ((peterssonMass k f : ℝ) : ℂ)) :=
  ⟨symrBank_two_eq_sym2Bank H,
   rankinPrimalCoeff_eq H,
   rankinDualCoeff_eq H,
   fun _ hs => LSeries_rankinBank f hk hs,
   fun _ hs => sym2_euler_identity hk hs,
   fun _ hs => sym2Rankin_lambda_eq' H hk hk2 hs,
   sym2Rankin_selfdual_FE H hk hk2,
   sym2Rankin_residue H hk hk2,
   sym2Rankin_entire H hk hk2,
   fun s => peeledFE f hk s,
   peeled_edge_regularity f hk⟩

end CriticalLinePhasor.Sym2Rankin

#print axioms CriticalLinePhasor.Sym2Rankin.sym2Rankin_lambda_eq'
#print axioms CriticalLinePhasor.Sym2Rankin.sym2_rankin_rung
