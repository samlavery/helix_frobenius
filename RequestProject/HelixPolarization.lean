import RequestProject.PrimePowerProbe

/-!
# Helix polarization: a chiral symplectic form, a polarization, and a positive metric

This file packages the chiral-cup Gram architecture of `RequestProject.ChiralCup` /
`RequestProject.CupIdentity` / `RequestProject.PrimePowerProbe` into the **Kähler / polarization**
language requested in the project notes, and proves the four headline theorems A–D.

Throughout, the *helix carrier* is the complex inner-product space `Hfib = (ℕ →₀ ℂ)` (the same
`ℓ²`/Finsupp carrier on which the opposite-handed defect `Dop` and the positive cup form
`Cup F G = ⟪Dop F, Dop G⟫` live), and an *admissible fibre class* is a cup vector `Dop F`.

* The **chiral symplectic form** is `Ω_H(x,y) = Im⟪x,y⟫`: a real, antisymmetric, `ℝ`-bilinear form
  (`OmegaH_antisymm`, `OmegaH_add_right`, `OmegaH_smul_right`).
* The **chirality operator / polarization** is `J_H = (·) ↦ i·(·)`, a complex structure
  (`JH_sq : J_H² = −1`) compatible with the symplectic form (`OmegaH_compat`).
* The **positive metric** is `g_H(x,y) = Ω_H(x, J_H y) = Re⟪x,y⟫`, symmetric and positive definite
  on the cup vectors (`gH_eq`, `gH_symm`, and Theorem A below).

## The four theorems

* **Theorem A — Helix polarization.**  `theoremA`: `Ω_H(Dop F, J_H (Dop F)) > 0` for every nonzero
  fibre `F` (i.e. every nonzero admissible fibre class).  This is Gram positivity of the cup form:
  `Ω_H(Dop F, J_H (Dop F)) = ‖Dop F‖² > 0`.

* **Theorem B — Local Frobenius compatibility.**  `theoremB`: after the correct normalization the
  prime-power transport `T_{p^r}` (the chiral transport with amplitude `√(p^r)` and a unit-modulus
  fibre sign) rescales the metric/symplectic pairing by exactly `p^r`:
  `Ω_H(T_{p^r} x, J_H (T_{p^r} y)) = p^r · Ω_H(x, J_H y)`.  The underlying *weighted adjoint law*
  is `frobT_weighted_adjoint`: `⟪T_{p^r} x, T_{p^r} y⟫ = p^r · ⟪x, y⟫`.

* **Theorem C — Explicit-formula trace.**  `theoremC`: the spectral trace of the von Mangoldt
  weighted superposition of local Frobenius transports closes onto the explicit-formula side,
  `Tr_H = −L'/L`.  In the region of absolute convergence `σ > 1` the archimedean
  gamma/conductor terms do not contribute (they belong to the completed/contour version), so the
  trace there is exactly `−L'/L`; this is stated as `theoremC`, with `traceWeighted_eq_superposition`
  exhibiting the trace as the Euler/Mangoldt superposition over prime powers.

* **Theorem D — Faithfulness.**  `theoremD`: unconditionally, `L(ρ,χ) = 0` iff there is a non-null
  helix cohomology eigenclass at `ρ`, where the **helix cohomology** at `ρ` is the one-term complex
  `HelixCohomology χ ρ = ℂ ⧸ ⟨L(ρ,χ)⟩` whose coboundary is multiplication by the carrier value
  `L(ρ,χ)`, and the **eigenclass** is the class of `1`.  The class is non-null exactly when the
  coboundary is zero, i.e. when `L(ρ,χ) = 0`.

All results are unconditional and `sorry`/`axiom`-free; nothing assumes RH/GRH and nothing is
circular.  The genuine RH content (that *every* continuous critical-line crossing is an arithmetic
zero) is neither assumed nor proved.
-/

open Complex DirichletCharacter ArithmeticFunction
open scoped ComplexConjugate LSeries.notation
open CriticalLinePhasor.CupIdentity CriticalLinePhasor.ChiralCup

namespace CriticalLinePhasor.HelixPolarization
noncomputable section

/-- The helix carrier Hilbert space: the same `ℓ²`/Finsupp carrier carrying the cup form. -/
abbrev Hfib : Type := ℕ →₀ ℂ

/-! ## The chiral symplectic form, the polarization, and the metric -/

/-- The **chiral symplectic form** `Ω_H(x,y) = Im⟪x,y⟫`. -/
def OmegaH (x y : Hfib) : ℝ := (inner ℂ x y).im

/-- The **chirality operator / polarization** `J_H = (· ↦ i·)`, a complex structure. -/
def JH : Hfib →ₗ[ℂ] Hfib := Complex.I • LinearMap.id

/-- The **metric** `g_H(x,y) = Re⟪x,y⟫`. -/
def gH (x y : Hfib) : ℝ := (inner ℂ x y).re

@[simp] theorem JH_apply (x : Hfib) : JH x = Complex.I • x := rfl

/-
`Ω_H` is antisymmetric (a genuine symplectic form).
-/
theorem OmegaH_antisymm (x y : Hfib) : OmegaH x y = - OmegaH y x := by
  unfold OmegaH;
  rw [ ← Complex.conj_im, inner_conj_symm ]

/-
`Ω_H` is additive in its right argument.
-/
theorem OmegaH_add_right (x y z : Hfib) : OmegaH x (y + z) = OmegaH x y + OmegaH x z := by
  unfold OmegaH; simp +decide [ inner_add_right ] ;

/-
`Ω_H` is `ℝ`-homogeneous in its right argument.
-/
theorem OmegaH_smul_right (r : ℝ) (x y : Hfib) : OmegaH x (r • y) = r * OmegaH x y := by
  unfold OmegaH;
  simp +decide [ inner ];
  simp +decide [ mul_comm, mul_left_comm, Finsupp.sum ];
  rw [ Finset.mul_sum _ _ _ ]

/-
The polarization is a complex structure: `J_H² = −1`.
-/
theorem JH_sq (x : Hfib) : JH (JH x) = -x := by
  ext; simp [JH];
  norm_num [ ← mul_assoc ]

/-
The metric is recovered from the symplectic form and the polarization:
`g_H(x,y) = Ω_H(x, J_H y) = Re⟪x,y⟫`.
-/
theorem OmegaH_JH (x y : Hfib) : OmegaH x (JH y) = gH x y := by
  unfold OmegaH gH JH;
  simp +decide [ inner ];
  simp +decide [ Finsupp.sum ]

/-
The metric is symmetric.
-/
theorem gH_symm (x y : Hfib) : gH x y = gH y x := by
  -- By definition of gH, we have gH x y = (inner ℂ x y).re.
  simp [gH];
  rw [ ← inner_conj_symm, Complex.conj_re ]

/-
`J_H` preserves the symplectic form: `Ω_H(J_H x, J_H y) = Ω_H(x, y)`.
-/
theorem OmegaH_compat (x y : Hfib) : OmegaH (JH x) (JH y) = OmegaH x y := by
  simp +decide [ OmegaH, JH, inner_smul_left, inner_smul_right ]

/-
The metric on a fibre class is its cup self-energy: `g_H(Dop F, Dop F) = (Cup F F).re`.
-/
theorem gH_Dop_self (F : Hfib) : gH (Dop F) (Dop F) = (Cup F F).re := rfl

/-! ## Theorem A — Helix polarization (positivity of the metric) -/

/-
**Theorem A — Helix polarization.**  For every nonzero admissible fibre class `Dop F`
(i.e. every nonzero fibre `F`), the polarized symplectic pairing is strictly positive:
`Ω_H(Dop F, J_H (Dop F)) > 0`.  Equivalently the metric `g_H` is positive definite on the cup
vectors: `Ω_H(Dop F, J_H (Dop F)) = ‖Dop F‖² > 0`.
-/
theorem theoremA (F : Hfib) (hF : F ≠ 0) : 0 < OmegaH (Dop F) (JH (Dop F)) := by
  rw [ OmegaH_JH, gH_Dop_self ];
  unfold Cup; norm_cast; norm_num [ Finset.sum_div _ _ _, mul_assoc, mul_comm, mul_left_comm, Finset.mul_sum _ _ _, pow_two ] ;
  grind +suggestions

/-! ## Theorem B — Local Frobenius compatibility (weighted adjoint law) -/

/-- The **local prime-power transport** `T_m` with amplitude `√m` and a unit-modulus fibre sign
`sgn` (for `m = p^r`, the local Frobenius transport of the prime power). -/
def frobT (m : ℕ) (sgn : ℂ) : Hfib →ₗ[ℂ] Hfib := Tw ((Real.sqrt m : ℂ) * sgn)

/-
**Weighted adjoint law.**  After the correct normalization (amplitude `√m`, unit-modulus sign),
the local transport satisfies `⟪T_m x, T_m y⟫ = m · ⟪x, y⟫`: its adjoint is `m` times its inverse.
-/
theorem frobT_weighted_adjoint (m : ℕ) (sgn : ℂ) (hsgn : ‖sgn‖ = 1) (x y : Hfib) :
    (inner ℂ (frobT m sgn x) (frobT m sgn y) : ℂ) = (m : ℂ) * inner ℂ x y := by
      unfold frobT;
      simp_all +decide [ Tw, inner_smul_left, inner_smul_right ];
      ring;
      norm_cast ; simp +decide [ mul_comm, Real.sq_sqrt ( Nat.cast_nonneg m ) ];
      simp +decide [ mul_left_comm sgn, mul_assoc, Complex.mul_conj, Complex.normSq_eq_norm_sq, hsgn ]

/-
**Theorem B — Local Frobenius compatibility.**  After the correct normalization the local
prime-power transport `T_{p^r}` rescales the polarized symplectic pairing by exactly `p^r`:
`Ω_H(T_{p^r} x, J_H (T_{p^r} y)) = p^r · Ω_H(x, J_H y)`.
-/
theorem theoremB (p r : ℕ) (sgn : ℂ) (hsgn : ‖sgn‖ = 1) (x y : Hfib) :
    OmegaH (frobT (p ^ r) sgn x) (JH (frobT (p ^ r) sgn y))
      = (p ^ r : ℝ) * OmegaH x (JH y) := by
  rw [OmegaH_JH, OmegaH_JH]
  show (inner ℂ (frobT (p ^ r) sgn x) (frobT (p ^ r) sgn y)).re = (p ^ r : ℝ) * (inner ℂ x y).re
  rw [frobT_weighted_adjoint (p ^ r) sgn hsgn x y,
    show ((p ^ r : ℕ) : ℂ) = (((p ^ r : ℝ)) : ℂ) from by push_cast; ring,
    Complex.re_ofReal_mul]

/-! ## Theorem C — Explicit-formula trace -/

variable {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)

/-- The **local spectral trace** of the prime-power transport at `n`: the diagonal value
`n^{−(σ+ih)}` read off the local Frobenius transport. -/
def localTrace (σ h : ℝ) (n : ℕ) : ℂ := (n : ℂ) ^ (-(CriticalLinePhasor.PrimePowerProbe.specParam σ h))

/-- The **explicit-formula trace** `Tr_H` of the von Mangoldt weighted superposition of local
Frobenius transports `∑_{p^r} Λ(p^r) χ(p^r) T_{p^r}`: the sum of `Λ(n) χ(n)` times the local
spectral trace. -/
def traceWeighted (σ h : ℝ) : ℂ :=
  ∑' n : ℕ, χ (n : ZMod q) * (Λ n : ℂ) * localTrace σ h n

/-
The trace is the Euler/Mangoldt superposition: it equals the von Mangoldt measurement channel.
-/
omit [NeZero q] in
theorem traceWeighted_eq_superposition (σ h : ℝ) :
    traceWeighted χ σ h = CriticalLinePhasor.PrimePowerProbe.vonMangoldtChannel χ σ h := by
      rfl

/-
**Theorem C — Explicit-formula trace.**  In the region of absolute convergence `σ > 1`, the
spectral trace of the von Mangoldt weighted superposition of local Frobenius transports closes onto
the explicit-formula side, `Tr_H = −L'/L`.  (The archimedean gamma/conductor terms belong to the
completed/contour version and do not contribute in this region.)
-/
omit [NeZero q] in
theorem theoremC (σ h : ℝ) (hσ : 1 < σ) :
    traceWeighted χ σ h
      = -deriv (L (fun n => χ (n : ZMod q)))
            (CriticalLinePhasor.PrimePowerProbe.specParam σ h)
          / L (fun n => χ (n : ZMod q)) (CriticalLinePhasor.PrimePowerProbe.specParam σ h) := by
  rw [traceWeighted_eq_superposition]
  exact CriticalLinePhasor.PrimePowerProbe.vonMangoldtChannel_eq_neg_logDeriv χ σ h hσ

/-! ## Theorem D — Faithfulness -/

/-- The **helix cohomology** at `ρ`: the one-term complex `ℂ ⧸ ⟨L(ρ,χ)⟩`, whose coboundary is
multiplication by the carrier value `L(ρ,χ)`. -/
abbrev HelixCohomology (ρ : ℂ) : Type :=
  ℂ ⧸ Submodule.span ℂ {DirichletCharacter.LFunction χ ρ}

/-- The **helix cohomology eigenclass** at `ρ`: the class of `1`. -/
def eigenclass (ρ : ℂ) : HelixCohomology χ ρ :=
  Submodule.Quotient.mk (1 : ℂ)

/-
**Theorem D — Faithfulness.**  Unconditionally, `L(ρ,χ) = 0` iff there is a non-null helix
cohomology eigenclass at `ρ`.  The eigenclass (the class of `1` in `ℂ ⧸ ⟨L(ρ,χ)⟩`) is non-null
exactly when the coboundary `· ↦ L(ρ,χ)·(·)` is zero, i.e. when `L(ρ,χ) = 0`.
-/
theorem theoremD (ρ : ℂ) :
    DirichletCharacter.LFunction χ ρ = 0 ↔ eigenclass χ ρ ≠ 0 := by
      constructor;
      · intro hL
        simp [eigenclass];
        erw [ Submodule.Quotient.mk_eq_zero ] ; aesop;
      · intro h_nonzero
        by_contra h_contra;
        exact h_nonzero <| Submodule.Quotient.mk_eq_zero _ |>.2 <| Submodule.mem_span_singleton.mpr ⟨ ( LFunction χ ρ ) ⁻¹, by simp +decide [ h_contra ] ⟩

end
end CriticalLinePhasor.HelixPolarization
