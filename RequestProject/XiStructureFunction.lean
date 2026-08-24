import RequestProject.DVPSeatRealPart
import RequestProject.DeBranges

/-!
# The Lagarias structure function for `ξ`, and the Hermite–Biehler connector

The de Branges vocabulary of `DeBranges.lean` (`Estar`, `Acomp`, `Bcomp`, `IsHB`) is
instantiated here at the **explicit** structure function

  `E_ξ(z) = ξ(½ − iz) + ξ′(½ − iz)`.

Two identities carry the file, both pure functional-equation bookkeeping:

* `xiStructure_Estar` — `E*_ξ(z) = ξ(½ − iz) − ξ′(½ − iz)`, from conjugation
  equivariance (`riemannXi_conj`, `deriv_xi_conj`) followed by the functional
  equation and its derivative (`riemannXi_one_sub`, `deriv_xi_one_sub`).
* `xiStructure_Acomp` — **`A = ξ`**: the `A`-component of `E_ξ` is `ξ` itself, read
  in the spectral chart `z ↦ ½ − iz`.

Consequence (`rh_of_xiStructure_isHB`): since `DeBranges.Acomp_zero_im_eq_zero` forces
every zero of `A` onto the real axis whenever `E` is Hermite–Biehler, and the chart
sends a nontrivial zero `ρ` to `z = i(ρ − ½)` whose imaginary part is `Re ρ − ½`,

  `IsHB E_ξ  ⟹  every nontrivial zero has `Re ρ = ½`.

`xiStructure` is defined from `ξ` and `ξ′` alone: it mentions no zero set, no
`NontrivialZeros`, and no spectral coordinate.  The zero set enters only in the
consequence, never in the construction.

SIGN CHECK, worth stating because it is the whole content of the two identities: had the
derivative branch of the functional equation been taken with the wrong sign, the roles
would swap and `Acomp` would come out as `ξ′` rather than `ξ`.  `xiStructure_Bcomp`
records the other component as `i·ξ′` so both are pinned, not just the one used.
-/

open Complex ComplexConjugate
open CriticalLinePhasor.DeBranges

noncomputable section

namespace CriticalLinePhasor.XiStructure

open CriticalLinePhasor.DVP

/-- **The Lagarias structure function** `E_ξ(z) = ξ(½ − iz) + ξ′(½ − iz)`.
Built from `ξ` and its derivative only — no zero-location data anywhere. -/
def xiStructure (z : ℂ) : ℂ :=
  ZD.riemannXi (1 / 2 - Complex.I * z) + deriv ZD.riemannXi (1 / 2 - Complex.I * z)

/-- The chart conjugation identity: `conj(½ − i·conj z) = ½ + iz`. -/
theorem conj_chart (z : ℂ) :
    (starRingEnd ℂ) (1 / 2 - Complex.I * (starRingEnd ℂ) z) = 1 / 2 + Complex.I * z := by
  apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im]

/-- `ξ` is invariant under the chart reflection `z ↦ −z` (the functional equation). -/
theorem xi_chart_reflect (z : ℂ) :
    ZD.riemannXi (1 / 2 + Complex.I * z) = ZD.riemannXi (1 / 2 - Complex.I * z) := by
  have h1 : (1 : ℂ) - (1 / 2 + Complex.I * z) = 1 / 2 - Complex.I * z := by ring
  rw [← h1, ZD.ZeroCount.riemannXi_one_sub]

/-- `ξ′` is **anti**-invariant under the chart reflection (the differentiated
functional equation).  This sign is what puts `ξ` in the `A`-slot. -/
theorem deriv_xi_chart_reflect (z : ℂ) :
    deriv ZD.riemannXi (1 / 2 + Complex.I * z)
      = -deriv ZD.riemannXi (1 / 2 - Complex.I * z) := by
  have h1 : (1 : ℂ) - (1 / 2 + Complex.I * z) = 1 / 2 - Complex.I * z := by ring
  have h := deriv_xi_one_sub (1 / 2 + Complex.I * z)
  rw [h1] at h
  rw [h]; ring

/-- **The reflection**: `E*_ξ(z) = ξ(½ − iz) − ξ′(½ − iz)`. -/
theorem xiStructure_Estar (z : ℂ) :
    Estar xiStructure z
      = ZD.riemannXi (1 / 2 - Complex.I * z)
        - deriv ZD.riemannXi (1 / 2 - Complex.I * z) := by
  simp only [Estar, xiStructure]
  rw [map_add, ← CriticalLinePhasor.ContourArgument.riemannXi_conj, ← deriv_xi_conj,
    conj_chart, xi_chart_reflect, deriv_xi_chart_reflect]
  ring

/-- **The `A`-component is `ξ` itself.**  This is the bridge: the de Branges
spectrum of `E_ξ` is the zero set of `ξ` read in the chart `z ↦ ½ − iz`. -/
theorem xiStructure_Acomp (z : ℂ) :
    Acomp xiStructure z = ZD.riemannXi (1 / 2 - Complex.I * z) := by
  simp only [Acomp, xiStructure_Estar, xiStructure]
  ring

/-- The `B`-component is `i·ξ′` in the same chart — recorded so that both slots are
pinned and the sign in `deriv_xi_chart_reflect` is load-bearing rather than assumed. -/
theorem xiStructure_Bcomp (z : ℂ) :
    Bcomp xiStructure z = Complex.I * deriv ZD.riemannXi (1 / 2 - Complex.I * z) := by
  simp only [Bcomp, xiStructure_Estar, xiStructure]
  ring

/-- The spectral chart sends `z = i(ρ − ½)` to `ρ`. -/
theorem chart_at_zero (ρ : ℂ) :
    (1 : ℂ) / 2 - Complex.I * (Complex.I * (ρ - 1 / 2)) = ρ := by
  rw [← mul_assoc, Complex.I_mul_I]; ring

/-- The chart's imaginary part reads off the distance from the critical line. -/
theorem chart_im (ρ : ℂ) : (Complex.I * (ρ - 1 / 2)).im = ρ.re - 1 / 2 := by
  simp [Complex.mul_im, Complex.sub_re]

/-- **THE CONNECTOR.**  Hermite–Biehler positivity of the Lagarias structure function
`E_ξ = ξ + ξ′` implies the Riemann Hypothesis.

The construction of `E_ξ` uses no zero-location data; the zeros appear only here, in
the conclusion. -/
theorem rh_of_xiStructure_isHB (hHB : IsHB xiStructure) :
    ∀ ρ ∈ ZD.NontrivialZeros, ρ.re = 1 / 2 := by
  intro ρ hρ
  have hz : Acomp xiStructure (Complex.I * (ρ - 1 / 2)) = 0 := by
    rw [xiStructure_Acomp, chart_at_zero]
    exact ZD.ZeroCount.riemannXi_zero_of_mem_NontrivialZeros ρ hρ
  have him := Acomp_zero_im_eq_zero hHB hz
  rw [chart_im] at him
  linarith

end CriticalLinePhasor.XiStructure

section AxiomAudit
#print axioms CriticalLinePhasor.XiStructure.xiStructure_Estar
#print axioms CriticalLinePhasor.XiStructure.xiStructure_Acomp
#print axioms CriticalLinePhasor.XiStructure.xiStructure_Bcomp
#print axioms CriticalLinePhasor.XiStructure.rh_of_xiStructure_isHB
end AxiomAudit
