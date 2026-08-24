import RequestProject.ThetaWronskianSuzukiGram

/-!
# The J-kernel and its vertical sign law

Riemann's kernel `Φ = riemannXiKernel` is positive on the half-line
(`riemannXiKernel_pos`).  Extended evenly to `ℝ` it drives the following object.

For the transform `Ξ(z) = c·∫_ℝ Φ(|u|) e^{izu} du` one has `Ξ′ = i·N` with
`N(z) = c·∫ uΦ(|u|)e^{izu}du`, and the Herglotz condition for `−Ξ′/Ξ` on the upper
half-plane is `Re[N·conj Ξ] ≤ 0`.  Symmetrising that double integral in
`s = u+v`, `d = u−v` turns it into

  `Re[N·conj Ξ] = (c²/4) ∫∫ s·Φ((s+d)/2)·Φ((s−d)/2)·cos(xd)·e^{−ys} ds dd`

whose inner `s`-integrand is `jKernel d s · exp (−y·s)`.

**This file proves the unconditional half: that inner integrand is ODD in `s`, hence
its symmetric pairing is pointwise `≤ 0` for every `y ≥ 0`.**  The sign comes from
`Φ ≥ 0` and evenness alone — no zero-location input of any kind.

SCOPE, stated exactly.  Nothing in this file asserts anything about `Ξ`, about zeros,
or about the Herglotz property.  What is proved is the sign law for the kernel, which
needs no bridge.

CORRECTION (2026-08-24).  An earlier version of this docstring claimed the integral
representation of `ξ` is "not in this tree".  That was false, and it came from grepping
for two literal identifiers rather than following the chain.  The representation IS
compiled:

* `ZD.riemannXi_eq_observable` (MellinPathToXi.lean, std axioms) —
  `ξ s = (s(s−1)/2) · I_theta_of ψ_mellin s + 1/2`, with
  `I_theta_of ψ s = ∫_{Ioi 0} 2·cosh((s−½)t)·ψ t` and
  `ψ_mellin t = (HurwitzZeta.evenKernel 0 (exp (2t)) − 1)·exp (t/2)`.
  `ψ_mellin` is built from Mathlib's theta kernel, NOT from `ξ` — non-circular.
  (Contrast `ThetaTransport.ψ_theta`, which IS defined from `ξ` by inverse cosine
  transform and would be circular for this purpose.)
* `four_mul_riemannXiKernelTerm_eq_thetaOperatorTerm` (ThetaWronskianSuzukiGram.lean) —
  relates `riemannXiKernel` to `xiThetaSeriesDeriv1/2`.

So the remaining work on that axis is the COMPOSITION `riemannXiKernel ↔ ψ_mellin`
(the `K = h″ − h/4` two-derivative step in the chart `s = ½ + iz`, where
`cosh((s−½)t) = cos(zt)`), not a bridge from scratch.

Numerically (transcript 2026-08-24, not formalised): with that representation the
normalisation is `c = 2` to 1e−21, the symmetrisation identity holds to 6.4e−16, and
`J_y(d) < 0` at every tested `d`.
-/

open Real

noncomputable section

namespace CriticalLinePhasor.JKernel

open CriticalLinePhasor.ThetaWronskianSuzukiGram

/-- Riemann's kernel extended evenly to the whole line. -/
def phiEven (u : ℝ) : ℝ := riemannXiKernel |u|

@[simp] theorem phiEven_neg (u : ℝ) : phiEven (-u) = phiEven u := by
  simp [phiEven]

/-- `Φ ≥ 0` everywhere on the line, from the compiled half-line positivity. -/
theorem phiEven_nonneg (u : ℝ) : 0 ≤ phiEven u :=
  riemannXiKernel_nonneg (abs_nonneg u)

/-- The inner integrand of `J`: `s · Φ((s+d)/2) · Φ((s−d)/2)`. -/
def jKernel (d s : ℝ) : ℝ :=
  s * phiEven ((s + d) / 2) * phiEven ((s - d) / 2)

/-- **`jKernel` is odd in `s`** — this is exactly where the evenness of `Φ` is used,
and it is what makes the pairing below collapse. -/
theorem jKernel_neg (d s : ℝ) : jKernel d (-s) = -jKernel d s := by
  have h1 : (-s + d) / 2 = -((s - d) / 2) := by ring
  have h2 : (-s - d) / 2 = -((s + d) / 2) := by ring
  simp only [jKernel, h1, h2, phiEven_neg]
  ring

/-- On the positive half-line the integrand is nonnegative. -/
theorem jKernel_nonneg {s : ℝ} (hs : 0 ≤ s) (d : ℝ) : 0 ≤ jKernel d s :=
  mul_nonneg (mul_nonneg hs (phiEven_nonneg _)) (phiEven_nonneg _)

/-- **THE VERTICAL SIGN LAW (pointwise).**  For every `y ≥ 0` and every `s ≥ 0`, the
`±s` pairing of the weighted integrand is nonpositive:

  `jKernel d s · e^{−ys} + jKernel d (−s) · e^{ys} ≤ 0`.

Equivalently `= −2·jKernel d s·sinh (y s) ≤ 0`.  Unconditional: the only inputs are
`Φ ≥ 0` and `Φ` even. -/
theorem jKernel_pairing_nonpos {y s : ℝ} (hy : 0 ≤ y) (hs : 0 ≤ s) (d : ℝ) :
    jKernel d s * Real.exp (-(y * s)) + jKernel d (-s) * Real.exp (y * s) ≤ 0 := by
  have hys : 0 ≤ y * s := mul_nonneg hy hs
  have hexp : Real.exp (-(y * s)) ≤ Real.exp (y * s) :=
    Real.exp_le_exp.mpr (by linarith)
  have hj : 0 ≤ jKernel d s := jKernel_nonneg hs d
  have key : jKernel d s * (Real.exp (-(y * s)) - Real.exp (y * s)) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hj (by linarith)
  rw [jKernel_neg]
  nlinarith [key]

/-- The closed `sinh` form of the same pairing. -/
theorem jKernel_pairing_eq (d y s : ℝ) :
    jKernel d s * Real.exp (-(y * s)) + jKernel d (-s) * Real.exp (y * s)
      = -(2 * jKernel d s * Real.sinh (y * s)) := by
  rw [jKernel_neg, Real.sinh_eq]
  ring

end CriticalLinePhasor.JKernel

section AxiomAudit
#print axioms CriticalLinePhasor.JKernel.phiEven_nonneg
#print axioms CriticalLinePhasor.JKernel.jKernel_neg
#print axioms CriticalLinePhasor.JKernel.jKernel_pairing_nonpos
#print axioms CriticalLinePhasor.JKernel.jKernel_pairing_eq
end AxiomAudit
