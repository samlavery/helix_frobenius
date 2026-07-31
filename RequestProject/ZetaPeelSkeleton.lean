import RequestProject.CarrierThetaIdentification
import RequestProject.CarrierThetaDirichletInverse
import Mathlib.NumberTheory.LSeries.Dirichlet

/-!
# The zeta-peel skeleton: Möbius dilation at the Mellin layer

Dividing a `ζ`-factor out of a bank readout at the Mellin level is a **Möbius-weighted
dilation resummation of the profile** — a carrier-level operation: each carrier height
`n + 1` dilates the profile, the Möbius weights recombine the dilated copies, and the
readout of the recombined profile is the original readout with one `ζ`-factor removed.
This file lands that engine, reusing the compiled bank machinery throughout:

* `mellin_dilation` — the abstract Mellin-dilation identity: for a coefficient sequence
  `b` and profile `F`, under the two named hypotheses (Mellin convergence of `F` at `s`
  and absolute summability of the per-height Mellin norm integrals),
  `mellin (∑' n, b n • F((n+1)x)) s = (∑' n, b n / (n+1)^s) · mellin F s`.
  This is a readout wrapper over the compiled bank identification
  `CarrierTheta.theta_hasMellin`; the Fubini interchange inside is the house's
  `integral_tsum_of_summable_integral_norm` route, already discharged there.
* `moebiusSeq` / `theta_moebiusSeq_eq_dilationKernel` — the Möbius dilation weights on
  the zero-indexed carrier heights, identified with the compiled dilation-kernel bank
  `dilationKernel (μ : ArithmeticFunction ℂ)` of `CarrierThetaDirichletInverse`.
* `dirichlet_moebiusSeq_eq_zeta_inv` — the Möbius readout is `(riemannZeta s)⁻¹` on the
  half-plane `1 < re s` where the Möbius Dirichlet readout is absolutely summable
  (Mathlib's `ζ ⋆ μ = δ`; the half-plane is the identification chart of this readout,
  a hypothesis of the identification layer only).
* `zetaPeel_hasMellin` / `zetaPeel_mellin` — **the peel corollary**: for any profile `g`
  with `mellin g s` convergent and `1 < re s`,
  `mellin (θ_μ g) s = (riemannZeta s)⁻¹ · mellin g s`, where `θ_μ g` is the
  Möbius-dilated profile.  The summability side conditions are discharged automatically
  from `|μ| ≤ 1` via the compiled polynomial route
  (`theta_hasMellin_of_polynomial` at `C = 1`, `A = 0`).

This is the **skeleton** of the r = 2 zeta-peel: the dilation identity is the peel's
engine.  The r = 2-specific wiring — which `ζ`-factor at which shift, applied to the
averaged profile `θ̄_f` of `RSAveragedThetaProfile3D` to produce the `Sym²` bank readout,
and the coefficient identification with the literal twisted Satake bank — is the named
next step, **not done here**.  Everything proven here is unconditional.
-/

open Complex Set MeasureTheory ArithmeticFunction
open scoped LSeries.notation ArithmeticFunction.Moebius

namespace CriticalLinePhasor.ZetaPeel

open CriticalLinePhasor.CarrierTheta

/-! ## The abstract Mellin-dilation identity -/

/-- **The Mellin-dilation identity**, the peel's engine.  A coefficient-weighted dilation
resummation of a profile has Mellin transform equal to the coefficient Dirichlet readout
times the profile's Mellin transform.  The two hypotheses are named and explicit: Mellin
convergence of the profile at `s`, and absolute summability of the per-height Mellin norm
integrals (the dominated-convergence condition for the bank/integral interchange).
Convergence of the assembled dilation's Mellin integral is *constructed*, not assumed. -/
theorem mellin_dilation (b : ℕ → ℂ) (F : ℝ → ℂ) {s : ℂ}
    (hF : MellinConvergent F s)
    (hnorm : Summable fun n : ℕ =>
      ∫ x : ℝ in Ioi 0, ‖(x : ℂ) ^ (s - 1) * (b n * F ((n + 1 : ℕ) * x))‖) :
    mellin (fun x : ℝ => ∑' n : ℕ, b n * F ((n + 1 : ℕ) * x)) s
      = (∑' n : ℕ, b n / ((n + 1 : ℕ) : ℂ) ^ s) * mellin F s := by
  have hglobal : MellinConvergent (theta b F) s :=
    theta_mellinConvergent_of_summable_integral_norm b F hF hnorm
  have h := theta_hasMellin b F hF hglobal hnorm
  have hd : dirichlet b s = ∑' n : ℕ, b n / ((n + 1 : ℕ) : ℂ) ^ s := by
    refine tsum_congr fun n => ?_
    rw [cpow_neg, div_eq_mul_inv]
  calc
    mellin (fun x : ℝ => ∑' n : ℕ, b n * F ((n + 1 : ℕ) * x)) s
        = mellin (theta b F) s := rfl
    _ = dirichlet b s * mellin F s := h.2
    _ = (∑' n : ℕ, b n / ((n + 1 : ℕ) : ℂ) ^ s) * mellin F s := by rw [hd]

/-! ## The Möbius dilation weights -/

/-- The Möbius weights on the zero-indexed carrier heights: height `n` carries `μ(n+1)`. -/
noncomputable def moebiusSeq (n : ℕ) : ℂ := ((μ (n + 1) : ℤ) : ℂ)

/-- The Möbius weights are bounded by `1`: they take values in `{-1, 0, 1}`. -/
theorem moebiusSeq_norm_le_one (n : ℕ) : ‖moebiusSeq n‖ ≤ 1 := by
  unfold moebiusSeq
  rcases moebius_eq_or (n + 1) with h | h | h <;> simp [h]

/-- The Möbius weights, shifted to positive heights, are exactly the Möbius arithmetic
function — so the Möbius dilation plugs directly into the compiled Dirichlet-convolution
bank machinery. -/
theorem coefficientArithmetic_moebiusSeq :
    coefficientArithmetic moebiusSeq = ((μ : ArithmeticFunction ℤ) : ArithmeticFunction ℂ) := by
  ext n
  rcases eq_or_ne n 0 with rfl | hn
  · simp [coefficientArithmetic]
  · have h1 : n - 1 + 1 = n := Nat.succ_pred_eq_of_ne_zero hn
    simp [coefficientArithmetic, moebiusSeq, hn, h1]

/-- The Möbius-dilated profile is the compiled dilation kernel of the Möbius arithmetic
function: the peel's engine is the existing bank, not a new object. -/
theorem theta_moebiusSeq_eq_dilationKernel (g : ℝ → ℂ) (x : ℝ) :
    theta moebiusSeq g x =
      dilationKernel ((μ : ArithmeticFunction ℤ) : ArithmeticFunction ℂ) g x := by
  rw [theta_eq_positiveTheta, coefficientArithmetic_moebiusSeq]
  rfl

/-! ## The `1/ζ` identification of the Möbius readout -/

/-- On the half-plane `1 < re s` where the Möbius Dirichlet readout is absolutely
summable, that readout is `(riemannZeta s)⁻¹` — Mathlib's `ζ ⋆ μ = δ` in the readout
chart.  This is the identification layer of the peel, not its engine. -/
theorem dirichlet_moebiusSeq_eq_zeta_inv {s : ℂ} (hs : 1 < s.re) :
    dirichlet moebiusSeq s = (riemannZeta s)⁻¹ := by
  have hsum : Summable (LSeries.term ↗μ s) := LSeriesSummable_moebius_iff.mpr hs
  have hshift : LSeries ↗μ s = dirichlet moebiusSeq s := by
    rw [LSeries, hsum.tsum_eq_zero_add, LSeries.term_zero, zero_add]
    refine tsum_congr fun n => ?_
    rw [LSeries.term_of_ne_zero (Nat.succ_ne_zero n)]
    rw [show ((n + 1 : ℕ) : ℂ) ^ (-s) = (((n + 1 : ℕ) : ℂ) ^ s)⁻¹ from cpow_neg _ s]
    rw [moebiusSeq, div_eq_mul_inv]
  have hζμ := LSeries_zeta_mul_Lseries_moebius hs
  rw [LSeries_zeta_eq_riemannZeta hs] at hζμ
  have hζ0 : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_one_lt_re hs
  rw [← hshift]
  field_simp
  linear_combination hζμ

/-! ## The peel corollary -/

/-- **The zeta-peel at the Mellin layer**: the Möbius-dilated profile's Mellin transform
is `(riemannZeta s)⁻¹` times the profile's — one `ζ`-factor divided out of the readout by
a carrier-level dilation resummation.  Both side conditions of the dilation identity are
discharged automatically from `|μ| ≤ 1` on the half-plane `1 < re s` of absolute
summability of the Möbius readout. -/
theorem zetaPeel_hasMellin (g : ℝ → ℂ) {s : ℂ}
    (hg : MellinConvergent g s) (hs : 1 < s.re) :
    HasMellin (theta moebiusSeq g) s ((riemannZeta s)⁻¹ * mellin g s) := by
  have hbound : ∀ n : ℕ, ‖moebiusSeq n‖ ≤ 1 * (((n + 1 : ℕ) : ℝ) ^ (0 : ℝ)) := by
    intro n
    rw [Real.rpow_zero, mul_one]
    exact moebiusSeq_norm_le_one n
  have hs' : (0 : ℝ) + 1 < s.re := by linarith
  have h := theta_hasMellin_of_polynomial moebiusSeq g s 1 0 hg hbound hs'
  rwa [dirichlet_moebiusSeq_eq_zeta_inv hs] at h

/-- The peel corollary in equation form: `mellin (θ_μ g) s = ζ(s)⁻¹ · mellin g s` for
`1 < re s`, whenever `mellin g s` converges. -/
theorem zetaPeel_mellin (g : ℝ → ℂ) {s : ℂ}
    (hg : MellinConvergent g s) (hs : 1 < s.re) :
    mellin (theta moebiusSeq g) s = (riemannZeta s)⁻¹ * mellin g s :=
  (zetaPeel_hasMellin g hg hs).2

end CriticalLinePhasor.ZetaPeel

#print axioms CriticalLinePhasor.ZetaPeel.mellin_dilation
#print axioms CriticalLinePhasor.ZetaPeel.moebiusSeq
#print axioms CriticalLinePhasor.ZetaPeel.moebiusSeq_norm_le_one
#print axioms CriticalLinePhasor.ZetaPeel.coefficientArithmetic_moebiusSeq
#print axioms CriticalLinePhasor.ZetaPeel.theta_moebiusSeq_eq_dilationKernel
#print axioms CriticalLinePhasor.ZetaPeel.dirichlet_moebiusSeq_eq_zeta_inv
#print axioms CriticalLinePhasor.ZetaPeel.zetaPeel_hasMellin
#print axioms CriticalLinePhasor.ZetaPeel.zetaPeel_mellin
