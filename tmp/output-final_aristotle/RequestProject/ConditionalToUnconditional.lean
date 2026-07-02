import RequestProject.DeBranges

/-!
# Can the conditional results be made unconditional?

This file answers the question "can we convert the conditional theorems to unconditional?"
honestly and constructively.

Almost every "critical-line"/"no off-axis zero" theorem in the development carries a hypothesis
`IsHB E` (Hermite–Biehler positivity of the structure function `E`) — for example
`hb_no_zero_upper`, `hb_no_offaxis_spectral_zero`, `hb_domination_dichotomy`,
`rigidity_excludes_offaxis_zero`, `deBrangesKernel_diag_nonneg`, `deBranges_balance_iff_real`.

There are **two** different answers depending on which structure function `E` is meant:

1. **For an `E` built from a Dirichlet `L`-function (`Λ`-built `E`), the answer is "no, not
   unconditionally" — discharging `IsHB E` for such an `E` is *exactly* the statement that there
   are no off-line zeros, i.e. the Riemann Hypothesis (for `ζ`) / GRH (for general `χ`).**  So
   "converting these conditionals to unconditional" for the arithmetic structure function is
   equivalent to proving RH/GRH, which is open and is neither assumed nor proved anywhere in this
   project.  This is the honesty boundary already documented throughout `DeBranges.lean`.

2. **For a *concrete* structure function whose Hermite–Biehler property is itself a theorem, the
   conditionals collapse to genuinely unconditional corollaries.**  The project already proves one
   such `IsHB` fact unconditionally: `paleyWiener_isHB : IsHB paleyWiener` for the Paley–Wiener
   function `E(z) = e^{-i z}`.  Feeding that proof into the conditional theorems turns each of them
   into an `IsHB`-free statement.  This section records those unconditional instances, both to show
   the conditional machinery is non-vacuous and to make precise *where* the conversion is and isn't
   available.

The punchline of the Paley–Wiener instance is recognizable classical analysis: its `B`-component is
`Complex.sin` (`paleyWiener_Bcomp`), so "no off-axis spectral zero" becomes the unconditional fact
that `sin` has no zeros off the real axis.
-/

namespace CriticalLinePhasor.DeBranges

/-! ## Unconditional corollaries for the concrete Paley–Wiener structure function

Each statement below is an `IsHB`-free corollary obtained by discharging the `IsHB` hypothesis of a
conditional theorem with `paleyWiener_isHB`. -/

/-- **Unconditional.**  The Paley–Wiener function has no zeros in the open upper half-plane.
This is `hb_no_zero_upper` with the hypothesis discharged by `paleyWiener_isHB`. -/
theorem paleyWiener_no_zero_upper {z : ℂ} (hz : 0 < z.im) : paleyWiener z ≠ 0 :=
  hb_no_zero_upper paleyWiener_isHB hz

/-- **Unconditional.**  Off the real axis one chirality strictly dominates the other for the
Paley–Wiener function (`hb_domination_dichotomy` discharged). -/
theorem paleyWiener_domination {z : ℂ} (hz : z.im ≠ 0) :
    ‖Estar paleyWiener z‖ < ‖paleyWiener z‖ ∨ ‖paleyWiener z‖ < ‖Estar paleyWiener z‖ :=
  hb_domination_dichotomy paleyWiener_isHB hz

/-- **Unconditional.**  No off-axis balance for the Paley–Wiener function
(`hb_no_offaxis_balance` discharged). -/
theorem paleyWiener_no_offaxis_balance {z : ℂ} (hz : z.im ≠ 0) :
    ‖paleyWiener z‖ ≠ ‖Estar paleyWiener z‖ :=
  hb_no_offaxis_balance paleyWiener_isHB hz

/-- **Unconditional.**  No off-axis spectral zero for the Paley–Wiener function: its `B`-component
has no zeros off the real axis (`rigidity_excludes_offaxis_zero` discharged). -/
theorem paleyWiener_no_offaxis_spectral_zero {z : ℂ} (hz : z.im ≠ 0) :
    Bcomp paleyWiener z ≠ 0 :=
  rigidity_excludes_offaxis_zero paleyWiener_isHB hz

/-- **Unconditional, classical.**  Reading the previous corollary through `paleyWiener_Bcomp`
(`Bcomp paleyWiener = Complex.sin`): the complex sine has no zeros off the real axis.  This is the
fully unconditional content of the "no off-line zero" theorem for the one structure function whose
Hermite–Biehler property is provable. -/
theorem sin_ne_zero_of_im_ne_zero {z : ℂ} (hz : z.im ≠ 0) : Complex.sin z ≠ 0 := by
  rw [← paleyWiener_Bcomp]
  exact rigidity_excludes_offaxis_zero paleyWiener_isHB hz

/-- **Unconditional.**  Diagonal positivity of the de Branges reproducing kernel for the
Paley–Wiener function (`deBrangesKernel_diag_nonneg` discharged). -/
theorem paleyWiener_kernel_diag_nonneg {w : ℂ} (hw : w.im ≠ 0) :
    0 ≤ (deBrangesKernel paleyWiener w w).re :=
  deBrangesKernel_diag_nonneg paleyWiener_isHB hw

/-! ## The next round of conditionals, made unconditional

The classification test (RH-strength is not by itself a reason to stop — ask only whether
discharging the hypothesis *assumes RH* or is *circular*; if neither, it is a valid target):

* Every `IsHB E` hypothesis below is, for a *concrete* structure function whose Hermite–Biehler
  property is itself a theorem, a **valid target**: discharging it neither assumes RH nor is
  circular (it is the already-proved fact `paleyWiener_isHB`).  Only for a `Λ`-built arithmetic `E`
  does discharging `IsHB E` coincide with RH/GRH.

So the conditional theorems of `DeBranges.lean` that still carried an `IsHB` hypothesis after the
first round are converted here, all by feeding in `paleyWiener_isHB`.  The recognizable classical
payoffs are isolated separately (`sin_zeros_real`, `sin_zeros_discrete`). -/

/-- `E* = e^{i z}` for the Paley–Wiener function never vanishes (exponentials are nonzero), so the
hypotheses `E* z ≠ 0` of the conjugate-block theorems are themselves dischargeable. -/
theorem paleyWiener_Estar_ne_zero (z : ℂ) : Estar paleyWiener z ≠ 0 := by
  rw [paleyWiener_Estar]; exact Complex.exp_ne_zero _

/-- The Paley–Wiener function is entire. -/
theorem paleyWiener_analyticOnNhd : AnalyticOnNhd ℂ paleyWiener Set.univ := by
  intro z _
  have h1 : AnalyticAt ℂ (fun z : ℂ => Complex.I * z) z :=
    analyticAt_const.mul analyticAt_id
  have h2 : AnalyticAt ℂ (fun z : ℂ => Complex.exp (-(Complex.I * z))) z :=
    AnalyticAt.cexp h1.neg
  exact h2

/-- **Unconditional.**  Lower-half-plane domination (`hb_lower` discharged). -/
theorem paleyWiener_hb_lower {z : ℂ} (hz : z.im < 0) :
    ‖paleyWiener z‖ < ‖Estar paleyWiener z‖ :=
  hb_lower paleyWiener_isHB hz

/-- **Unconditional.**  Modulus balance forces the real axis (`norm_eq_imp_im_zero` discharged). -/
theorem paleyWiener_norm_eq_imp_im_zero {z : ℂ}
    (h : ‖paleyWiener z‖ = ‖Estar paleyWiener z‖) : z.im = 0 :=
  norm_eq_imp_im_zero paleyWiener_isHB h

/-- **Unconditional.**  Every zero of the `A`-component is real (`Acomp_zero_im_eq_zero`). -/
theorem paleyWiener_Acomp_zero_im_eq_zero {z : ℂ} (hz : Acomp paleyWiener z = 0) :
    z.im = 0 :=
  Acomp_zero_im_eq_zero paleyWiener_isHB hz

/-- **Unconditional.**  Every zero of the `B`-component is real (`Bcomp_zero_im_eq_zero`). -/
theorem paleyWiener_Bcomp_zero_im_eq_zero {z : ℂ} (hz : Bcomp paleyWiener z = 0) :
    z.im = 0 :=
  Bcomp_zero_im_eq_zero paleyWiener_isHB hz

/-- **Unconditional, classical.**  Since `Bcomp paleyWiener = Complex.sin`, the previous corollary
says the complex sine has only **real** zeros. -/
theorem sin_zeros_real {z : ℂ} (hz : Complex.sin z = 0) : z.im = 0 :=
  paleyWiener_Bcomp_zero_im_eq_zero (by rw [paleyWiener_Bcomp]; exact hz)

/-- **Unconditional.**  The `B`-component is not identically zero (`Bcomp_not_eventually_zero`). -/
theorem paleyWiener_Bcomp_not_eventually_zero : ∃ z : ℂ, Bcomp paleyWiener z ≠ 0 :=
  Bcomp_not_eventually_zero paleyWiener_isHB

/-- **Unconditional.**  The zeros of the `B`-component are isolated (`Bcomp_zeros_discrete`),
discharging both the entirety and the Hermite–Biehler hypotheses. -/
theorem paleyWiener_Bcomp_zeros_discrete (z₀ : ℂ) :
    ∀ᶠ z in nhdsWithin z₀ {z₀}ᶜ, Bcomp paleyWiener z ≠ 0 :=
  Bcomp_zeros_discrete paleyWiener_analyticOnNhd paleyWiener_isHB z₀

/-- **Unconditional, classical.**  The zeros of `Complex.sin` are isolated (a discrete spectrum). -/
theorem sin_zeros_discrete (z₀ : ℂ) :
    ∀ᶠ z in nhdsWithin z₀ {z₀}ᶜ, Complex.sin z ≠ 0 := by
  have := paleyWiener_Bcomp_zeros_discrete z₀
  rwa [paleyWiener_Bcomp] at this

/-- **Unconditional.**  Off the real axis the Paley–Wiener carrier is rigid (`carrierRigid_of_isHB`). -/
theorem paleyWiener_carrierRigid {z : ℂ} (hz : z.im ≠ 0) :
    CarrierRigid paleyWiener z :=
  carrierRigid_of_isHB paleyWiener_isHB hz

/-- **Unconditional.**  Helix/anti-helix balance holds exactly on the real axis
(`deBranges_balance_iff_real`). -/
theorem paleyWiener_balance_iff_real (z : ℂ) :
    ‖paleyWiener z‖ = ‖Estar paleyWiener z‖ ↔ z.im = 0 :=
  deBranges_balance_iff_real paleyWiener_isHB z

/-- **Unconditional.**  The chiral-quotient block is unimodular iff `z` is real
(`conjugate_det_one_iff_reality`, with the `E* z ≠ 0` hypothesis also discharged). -/
theorem paleyWiener_conjugate_det_one_iff_reality (z : ℂ) :
    (conjPairBlock (paleyWiener z / Estar paleyWiener z)).det = 1 ↔ z.im = 0 :=
  conjugate_det_one_iff_reality paleyWiener_isHB (paleyWiener_Estar_ne_zero z)

/-- **Unconditional.**  Off the real axis the chiral-quotient block is not unimodular
(`conjPairBlock_quotient_det_ne_one_offaxis`). -/
theorem paleyWiener_conjPairBlock_quotient_det_ne_one_offaxis {z : ℂ} (hz : z.im ≠ 0) :
    (conjPairBlock (paleyWiener z / Estar paleyWiener z)).det ≠ 1 :=
  conjPairBlock_quotient_det_ne_one_offaxis paleyWiener_isHB (paleyWiener_Estar_ne_zero z) hz

/-- **Unconditional.**  The unimodular conjugate block unifies the three layers for the
Paley–Wiener function (`unimodular_block_unifies`). -/
theorem paleyWiener_unimodular_block_unifies (z : ℂ) :
    ((conjPairBlock (paleyWiener z / Estar paleyWiener z)).det = 1
        ↔ ‖paleyWiener z‖ = ‖Estar paleyWiener z‖)
      ∧ ((conjPairBlock (paleyWiener z / Estar paleyWiener z)).det = 1 ↔ z.im = 0)
      ∧ (Bcomp paleyWiener z = 0 → ‖paleyWiener z‖ = ‖Estar paleyWiener z‖)
      ∧ (z.im ≠ 0 → (conjPairBlock (paleyWiener z / Estar paleyWiener z)).det ≠ 1) :=
  unimodular_block_unifies paleyWiener_isHB (paleyWiener_Estar_ne_zero z)

end CriticalLinePhasor.DeBranges
