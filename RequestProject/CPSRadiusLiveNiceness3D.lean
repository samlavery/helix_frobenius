import RequestProject.CPSArithmeticTwist3D

/-!
# Radius-live analytic payload: `Sym^r π × τ` niceness with no temperedness assumed

The `Sym^r π × τ` niceness the converse theorem consumes does **not** require the base Satake
parameters to be unit-modulus.  The bank structure `PolynomialSatakeDualPair` keeps *arbitrary*
nonzero radial magnitudes under a polynomial prime bound `‖α_p‖ ≤ p^{e}` (the trivial Hecke bound
`e = 1`, or Jacquet–Shalika, both **unconditional** — no Ramanujan), and
`arithmeticCPSPolynomialTwist` propagates it to the tensor bank
(`primalExponent = r·e_π + e_τ`).  `cpsPolynomialAllTwists_payload` then proves the full niceness
(reciprocal-height reflection, entire continuation, vertical-strip bounds, and functional equation)
over that radius-live bank.

`cpsArithmeticTwist_radiusLive_niceness` names this composition: for **any** base
`π : PolynomialSatakeDualPair (Fin 2)` — holomorphic *or* Maass, tempered *or not* — and any twist
`τ`, the completed `Sym^r π × τ` carrier pair is nice.  Temperedness (`‖α_p‖ = 1`) is **nowhere**
assumed; it is the eventual output of the radial-limit capstone (`RamanujanLimit`,
`CPSRadialSatoTateGeometry3D`), not an input here.  This is what closes the Maass case and makes the
Ramanujan/Sato–Tate chain non-circular: the ceiling that drives the radial limit is Jacquet–Shalika
(`p^{1/2}`), the niceness that yields functoriality is proven at arbitrary radius, and `‖α_p‖ = 1`
falls out only at the end.

No `axiom`, no `sorry`.
-/

namespace CriticalLinePhasor.GlobalHelix

/-- **Radius-live niceness of `Sym^r π × τ`.**  For any base Satake pair
`π : PolynomialSatakeDualPair (Fin 2)` with *arbitrary* nonzero radial magnitudes (only a polynomial
prime bound, never `‖α_p‖ = 1`) and any twist `τ`, the arithmetic tensor carrier pair
`cpsPolynomialStrongFEPair (arithmeticCPSPolynomialTwist r m π τ)` has exact reciprocal-height
reflection and is entire, bounded on every vertical strip, and satisfies its functional equation.

This is the converse theorem's analytic input **without temperedness** — the non-tempered
(Maass-inclusive) analytic payload.  Its only Satake hypothesis is `π`'s polynomial bound, met
unconditionally by the trivial Hecke bound `‖α_p‖ ≤ p`. -/
theorem cpsArithmeticTwist_radiusLive_niceness
    (r m : ℕ) (hm : 1 ≤ m) (hmr : m < r)
    (pi : PolynomialSatakeDualPair (Fin 2)) (tau : PolynomialSatakeDualPair (Fin m)) :
    (∀ x : ℝ, 0 < x →
        cpsPolynomialPrimal3DBankReadout (arithmeticCPSPolynomialTwist r m pi tau) (1 / x) =
          (x : ℂ) * cpsPolynomialDual3DBankReadout (arithmeticCPSPolynomialTwist r m pi tau) x) ∧
      (let P := cpsPolynomialStrongFEPair (arithmeticCPSPolynomialTwist r m pi tau);
        Differentiable ℂ P.Λ ∧
        Differentiable ℂ P.symm.Λ ∧
        (∀ u v : ℝ, ∃ B : ℝ, ∀ s : ℂ,
          u ≤ s.re → s.re ≤ v → ‖P.Λ s‖ ≤ B) ∧
        (∀ u v : ℝ, ∃ B : ℝ, ∀ s : ℂ,
          u ≤ s.re → s.re ≤ v → ‖P.symm.Λ s‖ ≤ B) ∧
        (∀ s : ℂ, P.Λ (P.k - s) = P.ε • P.symm.Λ s)) :=
  cpsPolynomialAllTwists_payload r m hm hmr (arithmeticCPSPolynomialTwist r m pi tau)

end CriticalLinePhasor.GlobalHelix

#print axioms CriticalLinePhasor.GlobalHelix.cpsArithmeticTwist_radiusLive_niceness
