import RequestProject.ParsevalExact
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.LSeries.Convolution

/-!
# The Möbius transfer: peeling the zeta factor off the Rankin square

Brick (vi) of the `r = 2` chain, unconditional and definitional.  For any arithmetic function
`B` with L-series summable at `s`, `Re s > 1`, the zeta factor peels off exactly:

  `L(B, s) = ζ(s) · L(μ ⋆ B, s)`     (`moebius_zeta_transfer`),

because `ζ ⋆ μ = 1` in the Dirichlet ring — no arithmetic input at all.  Instantiated at the
Rankin square `B(n) = ‖a_n‖²` of a cusp form (`rankin_sym2_transfer`, convergence from the
compiled Hecke bound), this defines the Sym²-normalized coefficient sequence as `μ ⋆ ‖a‖²` and
factors the compiled Rankin–Selberg series as `ζ(s)` times its L-series on the convergence
half-plane.  Identifying `μ ⋆ ‖a‖²` with the classical Sym²-Satake coefficients is Hecke
multiplicativity — the named arithmetic input of the rung, *not* part of the transfer.
No RH/GRH.
-/

open ArithmeticFunction LSeries UpperHalfPlane Complex
open scoped LSeries.notation MatrixGroups Real ArithmeticFunction.Moebius
  ArithmeticFunction.zeta

namespace CriticalLinePhasor.HeckeSupBound

variable {k : ℤ}

/-- **The Möbius transfer**: for `Re s > 1` the zeta factor peels off any summable
L-series — `ζ ⋆ μ = 1` is the whole proof. -/
theorem moebius_zeta_transfer (B : ArithmeticFunction ℂ) {s : ℂ} (hs : 1 < s.re)
    (hb : LSeriesSummable (⇑B) s) :
    LSeries (⇑B) s =
      riemannZeta s * LSeries (⇑((μ : ArithmeticFunction ℂ) * B)) s := by
  have hμc : (⇑(μ : ArithmeticFunction ℂ) : ℕ → ℂ) = ↗μ := by
    funext n
    simp
  have hζc : (⇑(ζ : ArithmeticFunction ℂ) : ℕ → ℂ) = ↗ζ := by
    funext n
    simp
  have hμs : LSeriesSummable (⇑(μ : ArithmeticFunction ℂ)) s := by
    rw [hμc]
    exact LSeriesSummable_moebius_iff.mpr hs
  have hζs : LSeriesSummable (⇑(ζ : ArithmeticFunction ℂ)) s := by
    rw [hζc]
    exact LSeriesSummable_zeta_iff.mpr hs
  have hμB : LSeriesSummable (⇑((μ : ArithmeticFunction ℂ) * B)) s := by
    rw [← ArithmeticFunction.coe_mul]
    exact hμs.convolution hb
  have hid : (ζ : ArithmeticFunction ℂ) * ((μ : ArithmeticFunction ℂ) * B) = B := by
    rw [← mul_assoc, mul_comm (ζ : ArithmeticFunction ℂ) (μ : ArithmeticFunction ℂ),
      coe_moebius_mul_coe_zeta, one_mul]
  calc LSeries (⇑B) s
      = LSeries (⇑((ζ : ArithmeticFunction ℂ) * ((μ : ArithmeticFunction ℂ) * B))) s := by
        rw [hid]
    _ = LSeries ((⇑(ζ : ArithmeticFunction ℂ)) ⍟ ⇑((μ : ArithmeticFunction ℂ) * B)) s := by
        rw [← ArithmeticFunction.coe_mul]
    _ = LSeries (⇑(ζ : ArithmeticFunction ℂ)) s *
          LSeries (⇑((μ : ArithmeticFunction ℂ) * B)) s :=
        LSeries_convolution' hζs hμB
    _ = riemannZeta s * LSeries (⇑((μ : ArithmeticFunction ℂ) * B)) s := by
        rw [hζc, LSeries_zeta_eq_riemannZeta hs]

/-- The Rankin square of a cusp form, as an arithmetic function. -/
noncomputable def rankinSquare (f : CuspForm 𝒮ℒ k) : ArithmeticFunction ℂ :=
  toArithmeticFunction fun n => ((‖(qExpansion 1 f).coeff n‖ ^ 2 : ℝ) : ℂ)

/-- The Rankin square L-series converges on `Re s > k + 1`. -/
lemma rankinSquare_LSeriesSummable (f : CuspForm 𝒮ℒ k) {s : ℂ}
    (hs : (k : ℝ) + 1 < s.re) :
    LSeriesSummable (⇑(rankinSquare f)) s := by
  apply Summable.of_norm
  have hdir := (summable_rankin_dirichlet f hs).mul_left ((4 * π) ^ s.re)
  refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_) hdir
  rw [LSeries.norm_term_eq]
  rcases eq_or_ne n 0 with hn | hn
  · subst hn
    positivity
  · rw [if_neg hn]
    have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn
    have hnp : (0 : ℝ) < n := by exact_mod_cast hn1
    have hcoe : ‖(⇑(rankinSquare f) : ℕ → ℂ) n‖ = ‖(qExpansion 1 f).coeff n‖ ^ 2 := by
      rw [rankinSquare, toArithmeticFunction]
      simp only [ArithmeticFunction.coe_mk, if_neg hn]
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    rw [hcoe]
    rw [show (4 * π) ^ s.re * (‖(qExpansion 1 f).coeff n‖ ^ 2 / (4 * π * n) ^ s.re) =
      ‖(qExpansion 1 f).coeff n‖ ^ 2 *
        ((4 * π) ^ s.re / (4 * π * n) ^ s.re) by ring]
    rw [Real.mul_rpow (by positivity : (0:ℝ) ≤ 4 * π) hnp.le]
    have h4π : (0 : ℝ) < (4 * π) ^ s.re := Real.rpow_pos_of_pos (by positivity) _
    have hnσ : (0 : ℝ) < (n : ℝ) ^ s.re := Real.rpow_pos_of_pos hnp _
    rw [show (4 * π) ^ s.re / ((4 * π) ^ s.re * (n:ℝ) ^ s.re) = ((n:ℝ) ^ s.re)⁻¹ by
      field_simp]
    rw [div_eq_mul_inv]

/-- **The Sym² transfer for the cusp-form bank**: on the convergence half-plane,
`L(‖a‖², s) = ζ(s)·L(μ ⋆ ‖a‖², s)` — the definitional Möbius layer of the `r = 2` rung.
The sequence `μ ⋆ ‖a‖²` is the Sym²-normalized coefficient sequence by construction;
identifying it with the classical Sym²-Satake coefficients is Hecke multiplicativity, the
named arithmetic input, not part of this transfer. -/
theorem rankin_sym2_transfer (f : CuspForm 𝒮ℒ k) (hk : 0 ≤ k) {s : ℂ}
    (hs : (k : ℝ) + 1 < s.re) :
    LSeries (⇑(rankinSquare f)) s =
      riemannZeta s *
        LSeries (⇑((μ : ArithmeticFunction ℂ) * rankinSquare f)) s := by
  have hk' : (0 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  exact moebius_zeta_transfer (rankinSquare f) (by linarith)
    (rankinSquare_LSeriesSummable f hs)

end CriticalLinePhasor.HeckeSupBound

#print axioms CriticalLinePhasor.HeckeSupBound.moebius_zeta_transfer
#print axioms CriticalLinePhasor.HeckeSupBound.rankin_sym2_transfer
