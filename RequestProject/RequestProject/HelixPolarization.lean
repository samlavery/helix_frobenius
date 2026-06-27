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

/-! ## Theorem 1 — Welding positivity (A) to the prime-power ledger (C)

The positive polarization metric `g_H`, evaluated on the truncated probe fibre, **equals the von
Mangoldt ledger energy**.  Composing `gH_Dop_self` (`g_H(Dop F, Dop F) = (Cup F F).re`) with
`cup_intertwining` (`Cup(probeFibre) = 2·∑‖channelTerm‖²`) makes A's positivity and C's arithmetic
channel the *same number*.
-/

omit [NeZero q] in
/-- **Theorem 1 — The polarization metric on the probe fibre is the ledger energy.**
`g_H(Dop (probeFibre χ σ h N), Dop (probeFibre χ σ h N)) = 2·∑_{n<N} ‖χ(n)·Λ(n)·n^{−(σ+ih)}‖²`. -/
theorem gH_probeFibre_eq_ledgerEnergy (σ h : ℝ) (N : ℕ) :
    gH (Dop (CriticalLinePhasor.PrimePowerProbe.probeFibre χ σ h N))
       (Dop (CriticalLinePhasor.PrimePowerProbe.probeFibre χ σ h N))
      = 2 * ∑ n ∈ Finset.range N,
          ‖CriticalLinePhasor.PrimePowerProbe.channelTerm χ σ h n‖ ^ 2 := by
  rw [gH_Dop_self, CriticalLinePhasor.PrimePowerProbe.cup_intertwining, Complex.ofReal_re]

/-! ## Theorem 2 — Collapsing the Kähler triple into a single polarization

The three forms `g_H`, `Ω_H`, `J_H` are the real/imaginary parts of one Hermitian inner product:
`⟪x,y⟫ = g_H(x,y) + i·Ω_H(x,y)`.  This is literally `Complex.re_add_im` on `⟪x,y⟫`, and is the
actual content of the word *polarization*.
-/

/-- **Theorem 2 — Kähler collapse.**  The metric and the symplectic form are the real and
imaginary parts of the single Hermitian inner product: `⟪x,y⟫ = g_H(x,y) + i·Ω_H(x,y)`. -/
theorem inner_eq_gH_add_I_OmegaH (x y : Hfib) :
    (inner ℂ x y : ℂ) = (gH x y : ℂ) + Complex.I * (OmegaH x y : ℂ) := by
  unfold gH OmegaH
  rw [mul_comm]
  exact (Complex.re_add_im _).symm

/-! ## Theorem 3 — The Frobenius monoid action by polarization similitudes

Since `frobT m sgn = (√m·sgn)•id`, the transports compose multiplicatively:
`frobT (m*n) (s₁*s₂) = frobT m s₁ ∘ frobT n s₂`, with the amplitudes multiplying as `√m·√n = √(mn)`
and the unit-modulus signs multiplying.  Together with `frobT 1 1 = id` this promotes the transports
to a **representation of the multiplicative monoid `(ℕ, ×)` by polarization similitudes**.
-/

/-- The identity transport: `frobT 1 1 = id`. -/
theorem frobT_one : frobT 1 1 = LinearMap.id := by
  unfold frobT Tw
  simp

/-- **Theorem 3 — Multiplicative Frobenius monoid action.**  The local transports compose:
`frobT (m*n) (s₁*s₂) = frobT m s₁ ∘ₗ frobT n s₂` (amplitudes `√m·√n = √(mn)`). -/
theorem frobT_mul (m n : ℕ) (s₁ s₂ : ℂ) :
    frobT (m * n) (s₁ * s₂) = frobT m s₁ ∘ₗ frobT n s₂ := by
  unfold frobT Tw
  rw [LinearMap.smul_comp, LinearMap.comp_smul, LinearMap.id_comp, smul_smul]
  congr 1
  rw [Nat.cast_mul, Real.sqrt_mul (Nat.cast_nonneg m)]
  push_cast
  ring

/-! ## Theorem 4 — Giving D an actual differential (the two-term complex)

We replace the one-term quotient `ℂ ⧸ ⟨L(ρ)⟩` of `theoremD` by the **cohomology of the two-term
complex** `ℂ --(·L(ρ))--> ℂ`: `H⁰ = ker`, `H¹ = coker`.  The coboundary is honest multiplication by
the carrier value `L(ρ,χ)`.  Both `dim H⁰` and `dim H¹` jump from `0` to `1` exactly when
`L(ρ,χ) = 0`, so `dim H¹` detects the zero with a real coboundary instead of a quotient.
-/

/-- The **coboundary** of the two-term helix complex `ℂ --(·L(ρ))--> ℂ`: multiplication by the
carrier value `L(ρ,χ)`. -/
def coboundaryD (ρ : ℂ) : ℂ →ₗ[ℂ] ℂ := (DirichletCharacter.LFunction χ ρ) • LinearMap.id

/-- `H⁰` of the two-term complex: the kernel of the coboundary. -/
abbrev helixH0 (ρ : ℂ) : Submodule ℂ ℂ := LinearMap.ker (coboundaryD χ ρ)

/-- `H¹` of the two-term complex: the cokernel of the coboundary. -/
abbrev helixH1 (ρ : ℂ) : Type := ℂ ⧸ LinearMap.range (coboundaryD χ ρ)

@[simp] theorem coboundaryD_apply (ρ z : ℂ) :
    coboundaryD χ ρ z = DirichletCharacter.LFunction χ ρ * z := rfl

/-- **Theorem 4 (H¹).**  `dim H¹` of the two-term complex jumps from `0` to `1` exactly when the
carrier vanishes: `dim H¹ = 1 ⇔ L(ρ,χ) = 0` (and `= 0` otherwise). -/
theorem theoremD_H1_finrank (ρ : ℂ) :
    Module.finrank ℂ (helixH1 χ ρ)
      = if DirichletCharacter.LFunction χ ρ = 0 then 1 else 0 := by
  by_cases hL : DirichletCharacter.LFunction χ ρ = 0
  · rw [if_pos hL]
    have hr : LinearMap.range (coboundaryD χ ρ) = ⊥ := by
      unfold coboundaryD; rw [hL, zero_smul, LinearMap.range_zero]
    show Module.finrank ℂ (ℂ ⧸ LinearMap.range (coboundaryD χ ρ)) = 1
    rw [(Submodule.quotEquivOfEqBot _ hr).finrank_eq, Module.finrank_self]
  · rw [if_neg hL]
    have hr : LinearMap.range (coboundaryD χ ρ) = ⊤ := by
      rw [LinearMap.range_eq_top]
      intro y
      exact ⟨y / DirichletCharacter.LFunction χ ρ, by rw [coboundaryD_apply]; field_simp⟩
    haveI : Subsingleton (helixH1 χ ρ) := by
      show Subsingleton (ℂ ⧸ LinearMap.range (coboundaryD χ ρ))
      rw [Submodule.Quotient.subsingleton_iff]; exact hr
    exact Module.finrank_zero_of_subsingleton

/-- **Theorem 4 (H⁰).**  `dim H⁰` of the two-term complex jumps from `0` to `1` exactly when the
carrier vanishes: `dim H⁰ = 1 ⇔ L(ρ,χ) = 0` (and `= 0` otherwise). -/
theorem theoremD_H0_finrank (ρ : ℂ) :
    Module.finrank ℂ (helixH0 χ ρ)
      = if DirichletCharacter.LFunction χ ρ = 0 then 1 else 0 := by
  show Module.finrank ℂ (LinearMap.ker (coboundaryD χ ρ)) = _
  by_cases hL : DirichletCharacter.LFunction χ ρ = 0
  · rw [if_pos hL,
      show LinearMap.ker (coboundaryD χ ρ) = ⊤ from by
        unfold coboundaryD; rw [hL, zero_smul, LinearMap.ker_zero],
      finrank_top, Module.finrank_self]
  · rw [if_neg hL,
      show LinearMap.ker (coboundaryD χ ρ) = ⊥ from by
        rw [LinearMap.ker_eq_bot]
        intro a b h
        exact mul_left_cancel₀ hL (by simpa [coboundaryD_apply] using h),
      finrank_bot]

/-- **Theorem 4 (detection).**  The two-term complex detects the zero: `H¹` is nontrivial iff the
carrier vanishes. -/
theorem theoremD_diff (ρ : ℂ) :
    Nontrivial (helixH1 χ ρ) ↔ DirichletCharacter.LFunction χ ρ = 0 := by
  show Nontrivial (ℂ ⧸ LinearMap.range (coboundaryD χ ρ)) ↔ _
  rw [Submodule.Quotient.nontrivial_iff]
  constructor
  · intro hne
    by_contra hL
    apply hne
    rw [LinearMap.range_eq_top]
    intro y
    exact ⟨y / DirichletCharacter.LFunction χ ρ, by rw [coboundaryD_apply]; field_simp⟩
  · intro hL hne
    rw [show LinearMap.range (coboundaryD χ ρ) = ⊥ from by
        unfold coboundaryD; rw [hL, zero_smul, LinearMap.range_zero]] at hne
    exact bot_ne_top hne

/-! ## Theorem 4 (germ-level) — keying `dim H¹` to the order of the zero

Working in the **germ ring** `ℂ⟦X⟧ = ℂ[[s−ρ]]`, replace the constant coboundary by multiplication
by the leading Taylor jet `X^n` of a zero of order `n` (the order-`n` part of the Taylor jet of `L`
at `ρ`; any germ of order `n` generates the same ideal `(X^n)`).  The cokernel of the germ complex
`ℂ⟦X⟧ --(·X^n)--> ℂ⟦X⟧` then has dimension exactly `n`, so `dim H¹` reads off the *order* of the
zero, refining the rank-`≤1` detection of `theoremD_H1_finrank`.
-/

open PowerSeries in
/-- The **germ coboundary**: multiplication by the monomial Taylor jet `X^n` on `ℂ⟦X⟧`. -/
noncomputable def germCoboundary (n : ℕ) : PowerSeries ℂ →ₗ[ℂ] PowerSeries ℂ :=
  LinearMap.mulLeft ℂ ((PowerSeries.X : PowerSeries ℂ) ^ n)

/-- `H¹` of the germ complex: the cokernel of the germ coboundary. -/
abbrev germH1 (n : ℕ) : Type := PowerSeries ℂ ⧸ LinearMap.range (germCoboundary n)

open PowerSeries in
/-- The **jet-reading map** `φ ↦ (coeff 0 φ, …, coeff (n−1) φ)` reading off the first `n` Taylor
coefficients. -/
noncomputable def jetRead (n : ℕ) : PowerSeries ℂ →ₗ[ℂ] (Fin n → ℂ) :=
  LinearMap.pi (fun i : Fin n => PowerSeries.coeff (R := ℂ) (i : ℕ))

open PowerSeries in
theorem jetRead_surjective (n : ℕ) : Function.Surjective (jetRead n) := by
  intro v
  refine ⟨PowerSeries.mk (fun m => if h : m < n then v ⟨m, h⟩ else 0), ?_⟩
  funext i
  have hi : (i : ℕ) < n := i.2
  simp [jetRead, PowerSeries.coeff_mk, hi]

open PowerSeries in
theorem ker_jetRead_eq_range_germCoboundary (n : ℕ) :
    LinearMap.ker (jetRead n) = LinearMap.range (germCoboundary n) := by
  ext φ
  simp only [LinearMap.mem_ker, LinearMap.mem_range, jetRead, germCoboundary,
    LinearMap.mulLeft_apply, LinearMap.pi_apply, funext_iff, Pi.zero_apply]
  constructor
  · intro h
    have hd : (PowerSeries.X : PowerSeries ℂ) ^ n ∣ φ := by
      rw [PowerSeries.X_pow_dvd_iff]
      intro m hm
      exact h ⟨m, hm⟩
    obtain ⟨g, hg⟩ := hd
    exact ⟨g, hg.symm⟩
  · rintro ⟨g, rfl⟩ i
    have hd : (PowerSeries.X : PowerSeries ℂ) ^ n ∣ (PowerSeries.X ^ n * g) := Dvd.intro g rfl
    rw [PowerSeries.X_pow_dvd_iff] at hd
    exact hd i i.2

/-- **Theorem 4 (germ-level).**  The germ cokernel detects the *order* of the zero: for the
order-`n` Taylor jet `X^n`, `dim H¹ = n`. -/
theorem germH1_finrank (n : ℕ) : Module.finrank ℂ (germH1 n) = n := by
  have hker := ker_jetRead_eq_range_germCoboundary n
  have e : germH1 n ≃ₗ[ℂ] (Fin n → ℂ) := by
    show (PowerSeries ℂ ⧸ LinearMap.range (germCoboundary n)) ≃ₗ[ℂ] (Fin n → ℂ)
    rw [← hker]
    exact LinearMap.quotKerEquivOfSurjective (jetRead n) (jetRead_surjective n)
  rw [e.finrank_eq, Module.finrank_fin_fun]

end
end CriticalLinePhasor.HelixPolarization
