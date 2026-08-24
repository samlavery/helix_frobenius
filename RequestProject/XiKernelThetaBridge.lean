import RequestProject.ThetaWronskianSuzukiGram

/-!
# The theta bridge, termwise: the formal derivatives ARE the derivatives

`ThetaWronskianSuzukiGram` defines `xiThetaSeriesDeriv1` and `xiThetaSeriesDeriv2` as
*formal* height derivatives of the positive theta term `xiThetaSeriesTerm` — explicit
closed forms, with (grep, 2026-08-24) no theorem identifying them with `deriv`.  This
file supplies that identification, which is the composition step in

  `riemannXiKernel u = ψ″(u) − ψ(u)/4`,   `ψ = ψ_mellin` (MellinPathToXi.lean)

Writing `Q = xiKernelQ n u = π(n+1)²e^{2u}`, so `Q′ = 2Q`:

* `xiThetaSeriesTerm n u = e^{−Q}`
* `xiThetaSeriesDeriv1 n u = −2Q·e^{−Q}`   — indeed `(e^{−Q})′`
* `xiThetaSeriesDeriv2 n u = (4Q² − 4Q)·e^{−Q}` — indeed `(e^{−Q})″`

Composed with the compiled `four_mul_riemannXiKernelTerm_eq_thetaOperatorTerm`, this
gives the termwise operator identity with genuine derivatives (`riemannXiKernelTerm_eq_op`).

CONTEXT (verified at source, 2026-08-24).  The other half of the bridge is already
compiled: `ZD.riemannXi_eq_observable` gives
`ξ s = (s(s−1)/2)·I_theta_of ψ_mellin s + 1/2` with
`ψ_mellin t = (HurwitzZeta.evenKernel 0 (exp (2t)) − 1)·exp (t/2)` — built from
Mathlib's theta kernel, not from `ξ`, hence non-circular.  (`ThetaTransport.ψ_theta`
by contrast IS defined from `ξ` and would be circular here.)

NUMERICS (2026-08-24, not formalised): `ψ″(u) − ψ(u)/4` vs `riemannXiKernel u` agrees
to 1.4e−6 / 1.7e−6 / 2.0e−5 at u = 0.05 / 0.2 / 0.5, at the finite-difference floor.

SCOPE: nothing here mentions zeros, `Ξ` on the critical line, or positivity of any
quadratic form.  It is a calculus identity for one series term.
-/

open Real

noncomputable section

namespace CriticalLinePhasor.XiKernelBridge

open CriticalLinePhasor.ThetaWronskianSuzukiGram

/-- `Q(u) = π(n+1)²e^{2u}` has `Q′ = 2Q`. -/
theorem hasDerivAt_xiKernelQ (n : ℕ) (u : ℝ) :
    HasDerivAt (xiKernelQ n) (2 * xiKernelQ n u) u := by
  have hfun : xiKernelQ n
      = fun v : ℝ => Real.pi * ((n : ℝ) + 1) ^ 2 * Real.exp (2 * v) := by
    funext v; rfl
  have hval : 2 * xiKernelQ n u
      = Real.pi * ((n : ℝ) + 1) ^ 2 * (Real.exp (2 * u) * 2) := by
    unfold xiKernelQ; ring
  have h1 : HasDerivAt (fun v : ℝ => 2 * v) 2 u := by
    simpa using (hasDerivAt_id u).const_mul (2 : ℝ)
  have h2 : HasDerivAt (fun v : ℝ => Real.exp (2 * v)) (Real.exp (2 * u) * 2) u := h1.exp
  rw [hval, hfun]
  exact h2.const_mul _

/-- The theta term is `e^{−Q}`. -/
theorem xiThetaSeriesTerm_eq (n : ℕ) (u : ℝ) :
    xiThetaSeriesTerm n u = Real.exp (-xiKernelQ n u) := by
  simp only [xiThetaSeriesTerm, xiKernelQ]
  ring_nf

/-- **`xiThetaSeriesDeriv1` is the derivative of `xiThetaSeriesTerm`.** -/
theorem hasDerivAt_xiThetaSeriesTerm (n : ℕ) (u : ℝ) :
    HasDerivAt (xiThetaSeriesTerm n) (xiThetaSeriesDeriv1 n u) u := by
  have hfun : xiThetaSeriesTerm n = fun v => Real.exp (-xiKernelQ n v) := by
    funext v; exact xiThetaSeriesTerm_eq n v
  have hval : xiThetaSeriesDeriv1 n u
      = Real.exp (-xiKernelQ n u) * -(2 * xiKernelQ n u) := by
    unfold xiThetaSeriesDeriv1; ring
  rw [hfun, hval]
  exact ((hasDerivAt_xiKernelQ n u).neg).exp

/-- **`xiThetaSeriesDeriv2` is the derivative of `xiThetaSeriesDeriv1`.** -/
theorem hasDerivAt_xiThetaSeriesDeriv1 (n : ℕ) (u : ℝ) :
    HasDerivAt (xiThetaSeriesDeriv1 n) (xiThetaSeriesDeriv2 n u) u := by
  have hfun : xiThetaSeriesDeriv1 n
      = fun v => -2 * xiKernelQ n v * Real.exp (-xiKernelQ n v) := by
    funext v; rfl
  have hQ := hasDerivAt_xiKernelQ n u
  have hA : HasDerivAt (fun v => -2 * xiKernelQ n v) (-2 * (2 * xiKernelQ n u)) u :=
    hQ.const_mul (-2 : ℝ)
  have hB : HasDerivAt (fun v => Real.exp (-xiKernelQ n v))
      (Real.exp (-xiKernelQ n u) * -(2 * xiKernelQ n u)) u := (hQ.neg).exp
  have hval : xiThetaSeriesDeriv2 n u
      = -2 * (2 * xiKernelQ n u) * Real.exp (-xiKernelQ n u)
        + -2 * xiKernelQ n u * (Real.exp (-xiKernelQ n u) * -(2 * xiKernelQ n u)) := by
    unfold xiThetaSeriesDeriv2; ring
  rw [hfun, hval]
  exact hA.mul hB

/-- `deriv` forms of the two lemmas. -/
theorem deriv_xiThetaSeriesTerm (n : ℕ) (u : ℝ) :
    deriv (xiThetaSeriesTerm n) u = xiThetaSeriesDeriv1 n u :=
  (hasDerivAt_xiThetaSeriesTerm n u).deriv

theorem deriv_xiThetaSeriesDeriv1 (n : ℕ) (u : ℝ) :
    deriv (xiThetaSeriesDeriv1 n) u = xiThetaSeriesDeriv2 n u :=
  (hasDerivAt_xiThetaSeriesDeriv1 n u).deriv

theorem deriv2_xiThetaSeriesTerm (n : ℕ) (u : ℝ) :
    deriv (deriv (xiThetaSeriesTerm n)) u = xiThetaSeriesDeriv2 n u := by
  have hfun : deriv (xiThetaSeriesTerm n) = xiThetaSeriesDeriv1 n := by
    funext v; exact deriv_xiThetaSeriesTerm n v
  rw [hfun]; exact deriv_xiThetaSeriesDeriv1 n u

/-- **THE TERMWISE OPERATOR IDENTITY, with genuine derivatives.**
`4·riemannXiKernelTerm n u = e^{u/2}·2·( (e^{−Q})″ + (e^{−Q})′ )`.
Composition of the compiled formal identity with the derivative identifications. -/
theorem riemannXiKernelTerm_eq_op (n : ℕ) (u : ℝ) :
    4 * riemannXiKernelTerm n u
      = Real.exp (u / 2) *
        (2 * (deriv (deriv (xiThetaSeriesTerm n)) u + deriv (xiThetaSeriesTerm n) u)) := by
  rw [deriv2_xiThetaSeriesTerm, deriv_xiThetaSeriesTerm]
  exact four_mul_riemannXiKernelTerm_eq_thetaOperatorTerm n u

/-! ### The series identification with Mathlib's theta kernel -/

/-- **The positive theta modes sum to `(evenKernel 0 (e^{2u}) − 1)/2`.**
This is the object `ψ_mellin` is built from:
`ψ_mellin u = (evenKernel 0 (e^{2u}) − 1)·e^{u/2} = 2·e^{u/2}·Σ_n xiThetaSeriesTerm n u`. -/
theorem hasSum_xiThetaSeriesTerm (u : ℝ) :
    HasSum (fun n : ℕ => xiThetaSeriesTerm n u)
      ((HurwitzZeta.evenKernel 0 (Real.exp (2 * u)) - 1) / 2) := by
  have ht : (0 : ℝ) < Real.exp (2 * u) := Real.exp_pos _
  have h := HurwitzZeta.hasSum_nat_cosKernel₀ (0 : ℝ) ht
  have hek : HurwitzZeta.evenKernel 0 (Real.exp (2 * u))
      = HurwitzZeta.cosKernel 0 (Real.exp (2 * u)) := by
    rw [HurwitzZeta.evenKernel_eq_cosKernel_of_zero]
  rw [hek]
  have h2 := h.div_const 2
  refine h2.congr_fun fun n => ?_
  simp [xiThetaSeriesTerm]

/-! ### Differentiation under the sum, and the assembly -/

/-- The positive-mode theta sum, as a function of height. -/
def thetaSum (u : ℝ) : ℝ := ∑' n : ℕ, xiThetaSeriesTerm n u

theorem thetaSum_eq (u : ℝ) :
    thetaSum u = (HurwitzZeta.evenKernel 0 (Real.exp (2 * u)) - 1) / 2 :=
  (hasSum_xiThetaSeriesTerm u).tsum_eq

private theorem mem_ball (u : ℝ) : u ∈ Set.Ioo (u - 1) (u + 1) := by
  constructor <;> linarith

/-- **`thetaSum` is differentiable, with the termwise derivative.** -/
theorem hasDerivAt_thetaSum (u : ℝ) :
    HasDerivAt thetaSum (∑' n : ℕ, xiThetaSeriesDeriv1 n u) u := by
  refine hasDerivAt_tsum_of_isPreconnected
    (((xiThetaLocalMajorantCoeff_summable 1 u).mul_left 2))
    isOpen_Ioo (convex_Ioo _ _).isPreconnected
    (fun n y _ => hasDerivAt_xiThetaSeriesTerm n y)
    (fun n y hy => xiThetaSeriesDeriv1_norm_le_local n hy)
    (mem_ball u) ?_ (mem_ball u)
  exact (hasSum_xiThetaSeriesTerm u).summable

/-- **The termwise first derivative sum is itself differentiable.** -/
theorem hasDerivAt_tsum_Deriv1 (u : ℝ) :
    HasDerivAt (fun v => ∑' n : ℕ, xiThetaSeriesDeriv1 n v)
      (∑' n : ℕ, xiThetaSeriesDeriv2 n u) u := by
  refine hasDerivAt_tsum_of_isPreconnected
    (((xiThetaLocalMajorantCoeff_summable 2 u).mul_left 4).add
      ((xiThetaLocalMajorantCoeff_summable 1 u).mul_left 4))
    isOpen_Ioo (convex_Ioo _ _).isPreconnected
    (fun n y _ => hasDerivAt_xiThetaSeriesDeriv1 n y)
    (fun n y hy => xiThetaSeriesDeriv2_norm_le_local n hy)
    (mem_ball u) ?_ (mem_ball u)
  exact Summable.of_norm_bounded ((xiThetaLocalMajorantCoeff_summable 1 u).mul_left 2)
    (fun n => xiThetaSeriesDeriv1_norm_le_local n (mem_ball u))

/-- **ψ_mellin**, spelled out: `(evenKernel 0 (e^{2u}) − 1)·e^{u/2}`. -/
def psi (u : ℝ) : ℝ := (HurwitzZeta.evenKernel 0 (Real.exp (2 * u)) - 1) * Real.exp (u / 2)

theorem psi_eq (u : ℝ) : psi u = 2 * Real.exp (u / 2) * thetaSum u := by
  rw [psi, thetaSum_eq]; ring

private theorem hasDerivAt_halfExp (u : ℝ) :
    HasDerivAt (fun v : ℝ => Real.exp (v / 2)) (Real.exp (u / 2) * (1 / 2)) u := by
  have h : HasDerivAt (fun v : ℝ => v / 2) (1 / 2 : ℝ) u := by
    simpa using (hasDerivAt_id u).div_const 2
  simpa using h.exp

/-- First derivative of `ψ`. -/
def psiD1 (u : ℝ) : ℝ :=
  Real.exp (u / 2) * (thetaSum u + 2 * ∑' n : ℕ, xiThetaSeriesDeriv1 n u)

theorem hasDerivAt_psi (u : ℝ) : HasDerivAt psi (psiD1 u) u := by
  have hfun : psi = fun v => 2 * (Real.exp (v / 2) * thetaSum v) := by
    funext v; rw [psi_eq]; ring
  have h := ((hasDerivAt_halfExp u).mul (hasDerivAt_thetaSum u)).const_mul (2 : ℝ)
  have hval : psiD1 u
      = 2 * (Real.exp (u / 2) * (1 / 2) * thetaSum u
          + Real.exp (u / 2) * ∑' n : ℕ, xiThetaSeriesDeriv1 n u) := by
    unfold psiD1; ring
  rw [hfun, hval]
  exact h

/-- Second derivative of `ψ`. -/
def psiD2 (u : ℝ) : ℝ :=
  Real.exp (u / 2) *
    (1 / 2 * thetaSum u + 2 * ∑' n : ℕ, xiThetaSeriesDeriv1 n u
      + 2 * ∑' n : ℕ, xiThetaSeriesDeriv2 n u)

theorem hasDerivAt_psiD1 (u : ℝ) : HasDerivAt psiD1 (psiD2 u) u := by
  have hfun : psiD1 = fun v =>
      Real.exp (v / 2) * (thetaSum v + 2 * ∑' n : ℕ, xiThetaSeriesDeriv1 n v) := rfl
  have hinner : HasDerivAt
      (fun v => thetaSum v + 2 * ∑' n : ℕ, xiThetaSeriesDeriv1 n v)
      ((∑' n : ℕ, xiThetaSeriesDeriv1 n u) + 2 * ∑' n : ℕ, xiThetaSeriesDeriv2 n u) u :=
    (hasDerivAt_thetaSum u).add ((hasDerivAt_tsum_Deriv1 u).const_mul (2 : ℝ))
  have h := (hasDerivAt_halfExp u).mul hinner
  have hval : psiD2 u
      = Real.exp (u / 2) * (1 / 2) * (thetaSum u + 2 * ∑' n : ℕ, xiThetaSeriesDeriv1 n u)
        + Real.exp (u / 2) *
          ((∑' n : ℕ, xiThetaSeriesDeriv1 n u) + 2 * ∑' n : ℕ, xiThetaSeriesDeriv2 n u) := by
    unfold psiD2; ring
  rw [hfun, hval]
  exact h

/-- **THE COMPOSITION.**  `riemannXiKernel u = ψ″(u) − ψ(u)/4`, with `ψ = ψ_mellin`
built from Mathlib's theta kernel.  This is the `K = h″ − h/4` identity. -/
theorem riemannXiKernel_eq_psi_operator (u : ℝ) :
    riemannXiKernel u = deriv (deriv psi) u - psi u / 4 := by
  have hd1 : deriv psi = psiD1 := funext fun v => (hasDerivAt_psi v).deriv
  have hd2 : deriv (deriv psi) u = psiD2 u := by
    rw [hd1]; exact (hasDerivAt_psiD1 u).deriv
  rw [hd2, psi_eq]
  -- both sides are `2·e^{u/2}·(ΣD1 + ΣD2)`
  have hsum1 : Summable fun n : ℕ => xiThetaSeriesDeriv1 n u :=
    Summable.of_norm_bounded ((xiThetaLocalMajorantCoeff_summable 1 u).mul_left 2)
      (fun n => xiThetaSeriesDeriv1_norm_le_local n (mem_ball u))
  have hsum2 : Summable fun n : ℕ => xiThetaSeriesDeriv2 n u :=
    Summable.of_norm_bounded
      (((xiThetaLocalMajorantCoeff_summable 2 u).mul_left 4).add
        ((xiThetaLocalMajorantCoeff_summable 1 u).mul_left 4))
      (fun n => xiThetaSeriesDeriv2_norm_le_local n (mem_ball u))
  have hK : riemannXiKernel u
      = 2 * Real.exp (u / 2) *
        ((∑' n : ℕ, xiThetaSeriesDeriv2 n u) + ∑' n : ℕ, xiThetaSeriesDeriv1 n u) := by
    have hterm : ∀ n : ℕ, 4 * riemannXiKernelTerm n u
        = Real.exp (u / 2) * (2 * (xiThetaSeriesDeriv2 n u + xiThetaSeriesDeriv1 n u)) :=
      fun n => four_mul_riemannXiKernelTerm_eq_thetaOperatorTerm n u
    rw [riemannXiKernel, ← tsum_mul_left, tsum_congr hterm]
    calc ∑' n : ℕ, Real.exp (u / 2) * (2 * (xiThetaSeriesDeriv2 n u + xiThetaSeriesDeriv1 n u))
        = Real.exp (u / 2) * ∑' n : ℕ, (2 * (xiThetaSeriesDeriv2 n u + xiThetaSeriesDeriv1 n u)) :=
          tsum_mul_left
      _ = Real.exp (u / 2) * (2 * ∑' n : ℕ, (xiThetaSeriesDeriv2 n u + xiThetaSeriesDeriv1 n u)) := by
          rw [tsum_mul_left]
      _ = Real.exp (u / 2) *
            (2 * ((∑' n : ℕ, xiThetaSeriesDeriv2 n u) + ∑' n : ℕ, xiThetaSeriesDeriv1 n u)) := by
          rw [hsum2.tsum_add hsum1]
      _ = 2 * Real.exp (u / 2) *
            ((∑' n : ℕ, xiThetaSeriesDeriv2 n u) + ∑' n : ℕ, xiThetaSeriesDeriv1 n u) := by ring
  rw [hK]
  simp only [psiD2]
  ring

end CriticalLinePhasor.XiKernelBridge

section AxiomAudit
#print axioms CriticalLinePhasor.XiKernelBridge.hasDerivAt_xiThetaSeriesTerm
#print axioms CriticalLinePhasor.XiKernelBridge.hasDerivAt_xiThetaSeriesDeriv1
#print axioms CriticalLinePhasor.XiKernelBridge.deriv2_xiThetaSeriesTerm
#print axioms CriticalLinePhasor.XiKernelBridge.riemannXiKernelTerm_eq_op
#print axioms CriticalLinePhasor.XiKernelBridge.hasSum_xiThetaSeriesTerm
#print axioms CriticalLinePhasor.XiKernelBridge.hasDerivAt_thetaSum
#print axioms CriticalLinePhasor.XiKernelBridge.hasDerivAt_psi
#print axioms CriticalLinePhasor.XiKernelBridge.riemannXiKernel_eq_psi_operator
end AxiomAudit
