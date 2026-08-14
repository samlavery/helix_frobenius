import RequestProject.MaassSym2Local

/-!
# The Rankin--Selberg factorization for a Maass form

The classical shape, assembled from the wire:

  **`ζ(2s)·∑ₙ‖λₙ‖²n^{-s} = ζ(s)·L(Sym²u, s)`.**

Two convolution identities give it.  `maass_sym2_euler_identity` is `ζ(2s)·L(μ⋆b) = L(Sym²)`;
Möbius inversion is `ζ(s)·L(μ⋆b) = L(b)`, because `ζ ⋆ μ = 1`.  Multiplying the first by `ζ(s)`
and substituting the second removes `L(μ⋆b)` entirely.

This is the identity the edge argument reads: the left side has a **simple pole at `s = 1`** with
positive residue (`maass_rankinSeries_continuation` + `maassPetersson_pos`), and `ζ(s)` has a simple
pole there too, so `L(Sym²u, 1)` is a ratio of two nonzero residues — hence nonzero.

**Scope.**  `r = 2`.  Sato--Tate needs every rank; this is not a route to it.  The residue
comparison itself is not carried out here.
-/

open ArithmeticFunction LSeries Complex
open scoped Real LSeries.notation ArithmeticFunction.Moebius ArithmeticFunction.zeta

set_option maxHeartbeats 1000000

namespace CriticalLinePhasor.Unfolding

open CriticalLinePhasor.Sym2Wire CriticalLinePhasor.ThreeDConverse

/-- **Möbius inversion for the Maass square-norm series.** -/
theorem maass_zeta_mul_muRankin (M : GenuineMaassCuspForm3D) {s : ℂ}
    (hs : (2 * (M.eigenData.E₀ + 2) : ℝ) + 1 < s.re) :
    riemannZeta s * LSeries (⇑((μ : ArithmeticFunction ℂ) * maassRankinSquareNorm M)) s =
      LSeries (⇑(maassRankinSquareNorm M)) s := by
  have hE : (0:ℝ) ≤ 2 * (M.eigenData.E₀ + 2) := by positivity
  have hs1 : 1 < s.re := by linarith
  have hμs : LSeriesSummable (⇑(μ : ArithmeticFunction ℂ)) s := by
    have hcoe : (⇑(μ : ArithmeticFunction ℂ) : ℕ → ℂ) = ↗μ := by
      funext n; simp
    rw [hcoe]
    exact LSeriesSummable_moebius_iff.mpr hs1
  have hb : LSeriesSummable (⇑(maassRankinSquareNorm M)) s :=
    maassRankinSquareNorm_LSeriesSummable M hs
  have hμb : LSeriesSummable (⇑((μ : ArithmeticFunction ℂ) * maassRankinSquareNorm M)) s := by
    rw [← ArithmeticFunction.coe_mul]
    exact hμs.convolution hb
  have hζ : LSeriesSummable (⇑(ζ : ArithmeticFunction ℂ)) s := by
    have hcoe : (⇑(ζ : ArithmeticFunction ℂ) : ℕ → ℂ) = ↗(ζ : ArithmeticFunction ℂ) := rfl
    exact LSeriesSummable_zeta_iff.mpr hs1
  have hzeta : LSeries (⇑(ζ : ArithmeticFunction ℂ)) s = riemannZeta s := by
    rw [← LSeries_zeta_eq_riemannZeta hs1]
    congr 1
  calc riemannZeta s *
        LSeries (⇑((μ : ArithmeticFunction ℂ) * maassRankinSquareNorm M)) s
      = LSeries (⇑(ζ : ArithmeticFunction ℂ)) s *
          LSeries (⇑((μ : ArithmeticFunction ℂ) * maassRankinSquareNorm M)) s := by
        rw [hzeta]
    _ = LSeries ((⇑(ζ : ArithmeticFunction ℂ)) ⍟
          ⇑((μ : ArithmeticFunction ℂ) * maassRankinSquareNorm M)) s :=
        (LSeries_convolution' hζ hμb).symm
    _ = LSeries (⇑(maassRankinSquareNorm M)) s := by
        congr 1
        rw [show (⇑(ζ : ArithmeticFunction ℂ) ⍟
              ⇑((μ : ArithmeticFunction ℂ) * maassRankinSquareNorm M)) =
            ⇑((ζ : ArithmeticFunction ℂ) *
              ((μ : ArithmeticFunction ℂ) * maassRankinSquareNorm M)) from
          ArithmeticFunction.coe_mul _ _,
          ← mul_assoc, ArithmeticFunction.coe_zeta_mul_coe_moebius, one_mul]

/-- **The Rankin--Selberg factorization**: `ζ(2s)·L(‖λ‖², s) = ζ(s)·L(Sym², s)`. -/
theorem maass_rankinSelberg_factorization (M : GenuineMaassCuspForm3D) {s : ℂ}
    (hs : (2 * (M.eigenData.E₀ + 2) : ℝ) + 1 < s.re) (hs2 : 1 < (2 * s).re) :
    riemannZeta (2 * s) * LSeries (⇑(maassRankinSquareNorm M)) s =
      riemannZeta s * LSeries (⇑(maassSym2Bank M)) s := by
  rw [← maass_zeta_mul_muRankin M hs, ← maass_sym2_euler_identity M hs hs2]
  ring

end CriticalLinePhasor.Unfolding

#print axioms CriticalLinePhasor.Unfolding.maass_zeta_mul_muRankin
#print axioms CriticalLinePhasor.Unfolding.maass_rankinSelberg_factorization
