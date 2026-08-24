import RequestProject.DVPSeatPrimeJoin

/-!
# The seat energy IS a logarithmic-derivative difference

`hilbertPolya_resolvent_trace` evaluates the two-point resolvent DIFFERENCE
over the zero multiset.  The seat criterion is about the resolvent PRODUCT
`(t_ρ − w)⁻¹ (t_ρ − w̄)⁻¹`.  Partial fractions connect them:

  `1/((t−w)(t−w̄)) = ((t−w)⁻¹ − (t−w̄)⁻¹)/(w − w̄)`,

so taking the trace's second point to be `w̄` turns it into the seat energy.
The result expresses the seat energy — the object whose nonnegativity at
every admissible anchor is equivalent to RH — as an explicit
logarithmic-derivative difference of `ξ`.

Why this is the link that was missing rather than bookkeeping: `ξ′/ξ` is
where the arithmetic lives.  Through `bridge_pillar`
(`ζ′/ζ = ξ′/ξ − 1/s − 1/(s−1) − Γℝ′/Γℝ`) and `euler_pillar`
(`L(Λ,s) = −ζ′/ζ` on `Re s > 1`), both compiled in
`VonMangoldtEFStandalone`, a logarithmic derivative of `ξ` carries the von
Mangoldt prime sum.  The seat criterion consumes only the functional
equation, discreteness, multiplicity and the strip — all of which
Davenport–Heilbronn also satisfies while violating the conclusion — so no
argument from those inputs alone can close it.  This identity is the point
where prime data can enter.
-/

open Complex

noncomputable section

namespace CriticalLinePhasor.DVP

open CriticalLinePhasor.HilbertPolya

/-- **The seat energy as a logarithmic-derivative difference.**  For an
admissible anchor (chart images off the zero set, `w` not real), the seat
energy equals `−i·Δ(ξ′/ξ)/(w − w̄)`. -/
theorem seat_energy_eq_xi_logDeriv {w : ℂ}
    (hw : (1 / 2 + Complex.I * w) ∉ ZD.NontrivialZeros)
    (hw' : (1 / 2 + Complex.I * (starRingEnd ℂ) w) ∉ ZD.NontrivialZeros)
    (him : w - (starRingEnd ℂ) w ≠ 0) :
    ∑' ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros},
        (ZD.xiOrderNat ρ.val : ℂ) *
          ((spectralCoord ρ.val - w)⁻¹ *
            (spectralCoord ρ.val - (starRingEnd ℂ) w)⁻¹)
      = -Complex.I *
          (deriv ZD.riemannXi (1 / 2 + Complex.I * w)
              / ZD.riemannXi (1 / 2 + Complex.I * w)
            - deriv ZD.riemannXi (1 / 2 + Complex.I * (starRingEnd ℂ) w)
              / ZD.riemannXi (1 / 2 + Complex.I * (starRingEnd ℂ) w))
        / (w - (starRingEnd ℂ) w) := by
  have hterm : ∀ ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros},
      (ZD.xiOrderNat ρ.val : ℂ) *
          ((spectralCoord ρ.val - w)⁻¹ *
            (spectralCoord ρ.val - (starRingEnd ℂ) w)⁻¹)
        = ((ZD.xiOrderNat ρ.val : ℂ) *
            ((spectralCoord ρ.val - w)⁻¹
              - (spectralCoord ρ.val - (starRingEnd ℂ) w)⁻¹))
          / (w - (starRingEnd ℂ) w) := by
    intro ρ
    have h1 : spectralCoord ρ.val - w ≠ 0 := by
      rw [spectralCoord_sub]
      exact mul_ne_zero Complex.I_ne_zero (sub_ne_zero_of_not_mem hw ρ.2)
    have h2 : spectralCoord ρ.val - (starRingEnd ℂ) w ≠ 0 := by
      rw [spectralCoord_sub]
      exact mul_ne_zero Complex.I_ne_zero (sub_ne_zero_of_not_mem hw' ρ.2)
    field_simp
    ring
  rw [tsum_congr hterm, tsum_div_const,
    hilbertPolya_resolvent_trace hw hw']

end CriticalLinePhasor.DVP

section AxiomAudit
#print axioms CriticalLinePhasor.DVP.seat_energy_eq_xi_logDeriv
end AxiomAudit
