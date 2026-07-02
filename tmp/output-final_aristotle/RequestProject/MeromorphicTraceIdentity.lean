import RequestProject.ClosedForm
import RequestProject.SelfAdjointGeneratorReadout

/-!
# The meromorphic trace identity: `state resolvent trace = -Λ'/Λ + known correction`

The **state resolvent trace** is `-L'/L = -logDeriv (LFunction χ)` (the logarithmic-derivative
trace of the configured state operator; in the absolute-convergence regime it is the von Mangoldt
Dirichlet series `∑ χ(n)Λ(n) n^{-s}`, cf. `HelixPolarization.theoremC`).  Completing the carrier by
the archimedean Gamma factor, `Λ(s,χ) = gammaFactor(χ,s)·L(s,χ)`
(`Tate.completedLFunction_eq_gammaFactor_mul`), and taking logarithmic derivatives gives the
**meromorphic trace identity**
```
-L'/L  =  -Λ'/Λ  +  (gammaFactor)'/gammaFactor ,
```
i.e. the state resolvent trace equals `-Λ'/Λ` plus the **known correction** `(gammaFactor)'/gammaFactor`
— the logarithmic derivative of the explicit archimedean factor.

**Connection to the self-adjoint spectral operator.**  The configured spectral operator
`SpectralFiber.specOp χ s` has determinant exactly `L(s,χ)` (`configured_det_eq_Lspec`); its
logarithmic-derivative trace `-d/ds log det = -L'/L` is the state resolvent trace.  So the identity
reads off the spectral operator: `spectral_operator_trace_identity`.

The identity is meromorphic: it holds wherever the logarithmic derivatives are the genuine `f'/f`,
i.e. away from the zeros/poles.  On `Re s > 0` the gamma factor is nonzero
(`Tate.gammaFactor_ne_zero_of_re_pos`), so the only restriction is `L(s,χ) ≠ 0` (the hypothesis
`hL`), together with differentiability of `L` (`s ≠ 1 ∨ χ ≠ 1`).

No `axiom`, no `sorry`.
-/

open Complex Filter Topology DirichletCharacter
open scoped BigOperators

namespace CriticalLinePhasor.Tate

variable {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)

/-! ## Differentiability of the archimedean factor on `Re s > 0` -/

/-- `Gammaℝ` is differentiable on the right half-plane `Re s > 0`. -/
theorem differentiableAt_Gammaℝ_of_re_pos {s : ℂ} (hs : 0 < s.re) :
    DifferentiableAt ℂ Complex.Gammaℝ s := by
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have h1 : DifferentiableAt ℂ (fun z : ℂ => (Real.pi : ℂ) ^ (-z / 2)) s :=
    DifferentiableAt.const_cpow (by fun_prop) (Or.inl hpi)
  have hsne : ∀ m : ℕ, s / 2 ≠ -(m : ℂ) := by
    intro m h
    have hre : (s / 2).re = (-(m : ℂ)).re := congrArg Complex.re h
    have e1 : (s / 2).re = s.re / 2 := by
      rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num, Complex.div_ofReal_re]
    rw [e1] at hre
    simp only [Complex.neg_re, Complex.natCast_re] at hre
    nlinarith [Nat.cast_nonneg (α := ℝ) m, hs]
  have h2 : DifferentiableAt ℂ (fun z : ℂ => Complex.Gamma (z / 2)) s :=
    (Complex.differentiableAt_Gamma (s / 2) hsne).comp s (by fun_prop)
  show DifferentiableAt ℂ (fun z : ℂ => (Real.pi : ℂ) ^ (-z / 2) * Complex.Gamma (z / 2)) s
  exact h1.mul h2

omit [NeZero q] in
/-- The Dirichlet archimedean factor `gammaFactor χ` is differentiable on `Re s > 0`. -/
theorem differentiableAt_gammaFactor_of_re_pos {s : ℂ} (hs : 0 < s.re) :
    DifferentiableAt ℂ (gammaFactor χ) s := by
  rcases χ.even_or_odd with hχ | hχ
  · have hfun : (gammaFactor χ) = fun z => Complex.Gammaℝ z := funext hχ.gammaFactor_def
    rw [hfun]; exact differentiableAt_Gammaℝ_of_re_pos hs
  · have hfun : (gammaFactor χ) = fun z => Complex.Gammaℝ (z + 1) := funext hχ.gammaFactor_def
    rw [hfun]
    have hs1' : 0 < (s + 1).re := by simp only [Complex.add_re, Complex.one_re]; linarith
    have hout : DifferentiableAt ℂ Complex.Gammaℝ (s + 1) := differentiableAt_Gammaℝ_of_re_pos hs1'
    have hin : DifferentiableAt ℂ (fun z : ℂ => z + 1) s := by fun_prop
    exact hout.comp s hin

/-! ## The meromorphic trace identity -/

/--
**The meromorphic trace identity.**  For `Re s > 0`, away from a zero of `L` (`hL`) and with `L`
differentiable (`s ≠ 1 ∨ χ ≠ 1`), the state resolvent trace `-L'/L` equals `-Λ'/Λ` plus the known
archimedean correction `(gammaFactor)'/gammaFactor`:
```
-logDeriv (LFunction χ) s
  = -logDeriv (completedLFunction χ) s + logDeriv (gammaFactor χ) s .
```
This is the logarithmic-derivative form of the completion `Λ = gammaFactor·L`.
-/
theorem state_resolvent_trace_eq {s : ℂ} (hs : 0 < s.re)
    (hs1 : s ≠ 1 ∨ χ ≠ 1) (hL : LFunction χ s ≠ 0) :
    -logDeriv (LFunction χ) s
      = -logDeriv (completedLFunction χ) s + logDeriv (gammaFactor χ) s := by
  have hG : gammaFactor χ s ≠ 0 := gammaFactor_ne_zero_of_re_pos χ hs
  have hGdiff : DifferentiableAt ℂ (gammaFactor χ) s := differentiableAt_gammaFactor_of_re_pos χ hs
  have hLdiff : DifferentiableAt ℂ (LFunction χ) s := differentiableAt_LFunction χ s hs1
  -- `Λ` agrees with `gammaFactor·L` on the open half-plane, a neighbourhood of `s`
  have heq : completedLFunction χ =ᶠ[nhds s] fun z => gammaFactor χ z * LFunction χ z := by
    have hopen : IsOpen {z : ℂ | 0 < z.re} := isOpen_lt continuous_const Complex.continuous_re
    filter_upwards [hopen.mem_nhds hs] with z hz
    exact completedLFunction_eq_gammaFactor_mul χ hz
  have hcong : logDeriv (completedLFunction χ) s
      = logDeriv (fun z => gammaFactor χ z * LFunction χ z) s := by
    rw [logDeriv_apply, logDeriv_apply, heq.deriv_eq, heq.eq_of_nhds]
  have hsplit : logDeriv (completedLFunction χ) s
      = logDeriv (gammaFactor χ) s + logDeriv (LFunction χ) s := by
    rw [hcong, logDeriv_mul s hG hL hGdiff hLdiff]
  rw [hsplit]; ring

/-! ## Connection to the self-adjoint spectral operator -/

/--
**The trace identity, read off the configured spectral operator.**

The determinant of the configured spectral operator `SpectralFiber.specOp χ s` is exactly `L(s,χ)`
(`SelfAdjointGenerator.configured_det_eq_Lspec`, since `Lspec χ = LFunction χ`).  Hence its
logarithmic-derivative resolvent trace `-d/ds log det (specOp χ s) = -L'/L` is the state resolvent
trace, and the meromorphic identity reads:
```
-logDeriv (s ↦ det (specOp χ s)) s = -logDeriv (completedLFunction χ) s + logDeriv (gammaFactor χ) s .
```
So the state resolvent trace of the spectral operator equals `-Λ'/Λ` plus the known archimedean
correction.
-/
theorem spectral_operator_trace_identity {s : ℂ} (hs : 0 < s.re)
    (hs1 : s ≠ 1 ∨ χ ≠ 1) (hL : LFunction χ s ≠ 0) :
    -logDeriv (fun z => LinearMap.det (CriticalLinePhasor.SpectralFiber.specOp χ z)) s
      = -logDeriv (completedLFunction χ) s + logDeriv (gammaFactor χ) s := by
  have hfun : (fun z => LinearMap.det (CriticalLinePhasor.SpectralFiber.specOp χ z))
      = LFunction χ := by
    funext z
    rw [CriticalLinePhasor.SelfAdjointGenerator.configured_det_eq_Lspec]
    rfl
  rw [hfun]
  exact state_resolvent_trace_eq χ hs hs1 hL

/-! ## The self-adjoint von Neumann operator's resolvent trace

The genuinely **self-adjoint** spectral operator is the von Neumann operator
`vonNeumannOp γ = γ • id` (`γ` real); its configured resolvent
`SelfAdjointGenerator.specOp (vonNeumannOp γ) s = (γ - specHeight s) • id` has determinant the signed
mode `specBchan γ s = γ - specHeight s` (`specBchan_eq_det`).  Its resolvent-determinant trace
`logDeriv (det)` is computed unconditionally below; its single pole sits exactly at the self-adjoint
cancellation `specHeight s = γ`, which lies on the critical line (`sign_flip_only_on_real_axis`).

This is the self-adjoint companion of the meromorphic trace identity: the L-readout operator
(`SpectralFiber.specOp`, determinant `= L`) drives the state resolvent trace `-L'/L = -Λ'/Λ + corr`,
while the self-adjoint von Neumann operator gives the resolvent trace `I / specBchan`.  Identifying
the singularities of the two traces (zeros of `L` ↔ eigenvalues of the self-adjoint generator) is the
Hilbert–Pólya correspondence — deliberately **not** asserted here. -/

open CriticalLinePhasor.SelfAdjointGenerator CriticalLinePhasor.UnconditionalFrobenius in
/-- **The self-adjoint von Neumann operator's resolvent-determinant trace.**  Unconditionally,
`logDeriv (s ↦ det (specOp (vonNeumannOp γ) s)) = I / specBchan γ s` (`= I / (γ - specHeight s)`):
the resolvent trace of the self-adjoint generator, with its pole at the self-adjoint cancellation. -/
theorem vonNeumann_resolvent_trace (γ : ℝ) (s : ℂ) :
    logDeriv (fun z => LinearMap.det (specOp (vonNeumannOp γ) z)) s
      = Complex.I / specBchan γ s := by
  have hfun : (fun z => LinearMap.det (specOp (vonNeumannOp γ) z))
      = fun z => specBchan γ z := funext (fun z => specBchan_eq_det γ z)
  rw [hfun, logDeriv_apply]
  have hderiv : deriv (fun z => specBchan γ z) s = Complex.I := by
    have hH : HasDerivAt (fun z : ℂ => specBchan γ z) Complex.I s := by
      simp only [specBchan, specHeight]
      have h0 : HasDerivAt (fun z : ℂ => -Complex.I * (z - 1 / 2)) (-Complex.I) s := by
        simpa using ((hasDerivAt_id s).sub_const (1 / 2 : ℂ)).const_mul (-Complex.I)
      simpa using h0.const_sub (γ : ℂ)
    exact hH.deriv
  rw [hderiv]

end CriticalLinePhasor.Tate
