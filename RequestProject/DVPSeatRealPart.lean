import RequestProject.DVPSeatLogDeriv
import RequestProject.ZeroCountJensen

/-!
# Conjunct 2 as an explicit inequality on `Re(ξ′/ξ)`

`seat_energy_eq_xi_logDeriv` writes the seat energy as a two-point difference
of `ξ′/ξ`.  The two chart points are not independent: with `w = x + iy`,

  `s₁ = ½ + iw = ½ − y + ix`,  `s₂ = ½ + i·conj w = ½ + y + ix = 1 − conj s₁`,

so the functional equation `ξ(1−s) = ξ(s)` and reality `ξ(s̄) = conj ξ(s)`
force `ξ′/ξ(s₂) = −conj(ξ′/ξ(s₁))`, and the DIFFERENCE collapses to twice a
REAL PART.  The seat energy is therefore

  `−Re[ ξ′/ξ(½ + iw) ] / Im w`,

an explicit real quantity.  Unconditional: an identity, with no hypotheses
beyond the anchor admissibility already required by the seat criterion.

Consequence: conjunct 2 of `seat_criterion_split_iff` — hence, with conjunct 1
already discharged, RH itself — is exactly the statement

  `Re[ ξ′/ξ(σ + it) ] ≤ 0`  for  `σ < ½`

on admissible points.  That is a sign condition on a harmonic function which
vanishes identically on the critical line (by the same antisymmetry) and whose
only singularities are the zeros themselves.
-/

open Complex ComplexConjugate

noncomputable section

namespace CriticalLinePhasor.DVP

open CriticalLinePhasor.HilbertPolya

/-- `ξ′` is conjugation-equivariant. -/
theorem deriv_xi_conj (s : ℂ) :
    deriv ZD.riemannXi (conj s) = conj (deriv ZD.riemannXi s) := by
  have hfun : (conj ∘ ZD.riemannXi ∘ conj) = ZD.riemannXi := by
    funext z
    simp [Function.comp_apply, CriticalLinePhasor.ContourArgument.riemannXi_conj]
  have hd : deriv ZD.riemannXi = conj ∘ deriv ZD.riemannXi ∘ conj := by
    rw [← deriv_conj_conj, hfun]
  have h := congr_fun hd (conj s)
  simpa using h

/-- `ξ′` is antisymmetric under `s ↦ 1 − s` (differentiated functional equation). -/
theorem deriv_xi_one_sub (s : ℂ) :
    deriv ZD.riemannXi (1 - s) = -deriv ZD.riemannXi s := by
  have hfun : (fun z : ℂ ↦ ZD.riemannXi (1 - z)) = ZD.riemannXi := by
    funext z
    exact ZD.ZeroCount.riemannXi_one_sub z
  have hd := congr_fun (congrArg deriv hfun) s
  rw [deriv_comp_const_sub] at hd
  have hneg := congrArg Neg.neg hd
  simpa using hneg

/-- **The reflected log-derivative**: `ξ′/ξ(1 − s̄) = −conj(ξ′/ξ(s))`. -/
theorem xi_logDeriv_one_sub_conj (s : ℂ) :
    deriv ZD.riemannXi (1 - conj s) / ZD.riemannXi (1 - conj s)
      = -conj (deriv ZD.riemannXi s / ZD.riemannXi s) := by
  rw [deriv_xi_one_sub, ZD.ZeroCount.riemannXi_one_sub, deriv_xi_conj,
    CriticalLinePhasor.ContourArgument.riemannXi_conj, map_div₀]
  ring

/-- The second chart point is the FE-conjugate reflection of the first. -/
theorem chart_two_eq (w : ℂ) :
    (1 / 2 + Complex.I * (starRingEnd ℂ) w) = 1 - conj (1 / 2 + Complex.I * w) := by
  apply Complex.ext <;> simp [Complex.conj_re, Complex.conj_im] <;> ring

/-- **Conjunct 2 as a real-part inequality.**  The seat energy at an admissible
anchor equals `−Re[ξ′/ξ(½ + iw)] / Im w`. -/
theorem seat_energy_re_eq {w : ℂ}
    (hw : (1 / 2 + Complex.I * w) ∉ ZD.NontrivialZeros)
    (hw' : (1 / 2 + Complex.I * (starRingEnd ℂ) w) ∉ ZD.NontrivialZeros)
    (him : w - (starRingEnd ℂ) w ≠ 0) :
    (∑' ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros},
        (ZD.xiOrderNat ρ.val : ℂ) *
          ((spectralCoord ρ.val - w)⁻¹ *
            (spectralCoord ρ.val - (starRingEnd ℂ) w)⁻¹)).re
      = -(deriv ZD.riemannXi (1 / 2 + Complex.I * w)
            / ZD.riemannXi (1 / 2 + Complex.I * w)).re / w.im := by
  have hmain := seat_energy_eq_xi_logDeriv hw hw' him
  set A : ℂ := deriv ZD.riemannXi (1 / 2 + Complex.I * w)
      / ZD.riemannXi (1 / 2 + Complex.I * w) with hA
  have hB : deriv ZD.riemannXi (1 / 2 + Complex.I * (starRingEnd ℂ) w)
      / ZD.riemannXi (1 / 2 + Complex.I * (starRingEnd ℂ) w) = -conj A := by
    rw [chart_two_eq w, hA]
    exact xi_logDeriv_one_sub_conj _
  rw [hB] at hmain
  have hsub : w - (starRingEnd ℂ) w = (2 * w.im : ℝ) * Complex.I := by
    rw [Complex.sub_conj]
  have hadd : A - -conj A = ((2 * A.re : ℝ) : ℂ) := by
    rw [sub_neg_eq_add, Complex.add_conj]
  rw [hadd, hsub] at hmain
  have him' : (w.im : ℝ) ≠ 0 := by
    intro h0
    apply him
    rw [Complex.sub_conj, h0]
    simp
  rw [hmain]
  have hne : ((2 * w.im : ℝ) : ℂ) * Complex.I ≠ 0 := by
    have h2 : (2 * w.im : ℝ) ≠ 0 := mul_ne_zero two_ne_zero him'
    exact mul_ne_zero (Complex.ofReal_ne_zero.mpr h2) Complex.I_ne_zero
  have hval : -Complex.I * ((2 * A.re : ℝ) : ℂ) / (((2 * w.im : ℝ) : ℂ) * Complex.I)
      = ((-(A.re) / w.im : ℝ) : ℂ) := by
    have hw : ((w.im : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr him'
    have hI : (Complex.I : ℂ) ≠ 0 := Complex.I_ne_zero
    push_cast
    field_simp
  rw [hval, Complex.ofReal_re]

end CriticalLinePhasor.DVP

section AxiomAudit
#print axioms CriticalLinePhasor.DVP.seat_energy_re_eq
#print axioms CriticalLinePhasor.DVP.xi_logDeriv_one_sub_conj
end AxiomAudit
