import RequestProject.RepMechanism
import RequestProject.AmplitudeExchange

/-!
# The package-level standing wave: the ring closed, at every rank

The campaign's two endpoints — the mechanism (one theta identity yields the complete
package) and the rank-uniform reduction (one standing wave yields the functional
equation) — are joined: **every real-data package carries its standing wave**, so the
one identity and the one axis condition are the same condition, compiled, uniformly in
the rank and the chart.

* `GammaC_schwarz` / `GammaR_schwarz₀` — Schwarz reality of both Deligne factors;
* `LSeries_conj_real` — Schwarz reality of the Dirichlet readout of real coefficients;
* `NicePackage.lam_schwarz` / `GeneralNicePackage.lam_schwarz` — global Schwarz
  reality of the continuation of any real-data package, by the identity theorem;
* `NicePackage.standingWave` / `GeneralNicePackage.standingWave` — **the axis
  condition**: on `Re s = 1/2` the package's transform satisfies
  `Λ = ε⁻¹·conj Λ` — gate 2's exact shape, derived from the package's functional
  equation and Schwarz reality, at every rank and chart;
* `NicePackage.eps_norm_one` — **unitarity of the root number, free**: if the
  transform is nonzero at one axis point, `‖ε‖ = 1` — the root number of a real-data
  package is unitary, derived, not assumed.

No `axiom`, no `sorry`.
-/

open Complex ComplexConjugate ArithmeticFunction
open scoped Real LSeries.notation

namespace CriticalLinePhasor.PackageStandingWave

open CriticalLinePhasor.NiceClosure CriticalLinePhasor.RepMechanism
open CriticalLinePhasor.AmplitudeExchange CriticalLinePhasor.AxisReality
open CriticalLinePhasor.LatticeStandingWave

/-- Schwarz reality of the complex-place Deligne factor. -/
theorem GammaC_schwarz (w : ℂ) :
    conj (Complex.Gammaℂ (conj w)) = Complex.Gammaℂ w := by
  rw [Complex.Gammaℂ_def, Complex.Gammaℂ_def, map_mul, map_mul, map_ofNat,
    Complex.Gamma_conj, Complex.conj_conj]
  congr 1
  rw [show -(conj w) = conj (-w) from (map_neg (starRingEnd ℂ) w).symm,
    show (2 * (Real.pi : ℂ)) = (((2 * Real.pi : ℝ)) : ℂ) by push_cast; ring,
    conj_ofReal_cpow (by positivity : (0:ℝ) ≤ 2 * Real.pi), Complex.conj_conj]

/-- Schwarz reality of the real-place Deligne factor. -/
theorem GammaR_schwarz₀ (w : ℂ) :
    conj (Complex.Gammaℝ (conj w)) = Complex.Gammaℝ w := by
  simpa using GammaR_schwarz 0 w

/-- Schwarz reality of the Dirichlet readout of real coefficients. -/
theorem LSeries_conj_real {a : ℕ → ℂ} (ha : ∀ n, conj (a n) = a n) (z : ℂ) :
    conj (LSeries a (conj z)) = LSeries a z := by
  unfold LSeries
  have hterm : ∀ n : ℕ, LSeries.term a z n = conj (LSeries.term a (conj z) n) := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [LSeries.term_zero]
    · rw [LSeries.term_of_ne_zero hn.ne', LSeries.term_of_ne_zero hn.ne']
      rw [show conj (a n / (n : ℂ) ^ (conj z)) = a n / (n : ℂ) ^ z by
        rw [map_div₀, ha, conj_natCast_cpow]]
  rw [tsum_congr hterm]
  show star (∑' n : ℕ, LSeries.term a (conj z) n)
      = ∑' n : ℕ, star (LSeries.term a (conj z) n)
  exact tsum_star

/-! ## Schwarz reality of the continuations -/

/-- Global Schwarz reality of the continuation of a real-data complex-chart package. -/
theorem NicePackage.lam_schwarz {a : ArithmeticFunction ℂ} {μs : List ℂ} {B : ℝ}
    {ε : ℂ} (P : NicePackage a μs B ε)
    (ha : ∀ n, conj (a n) = a n) (hμ : ∀ μ ∈ μs, conj μ = μ) (s : ℂ) :
    P.lam (conj s) = conj (P.lam s) := by
  have hglob : (fun z => conj (P.lam (conj z))) = P.lam := by
    refine CriticalLinePhasor.CarrierTargetIdentification.entire_eq_of_eqOn_isOpen
      (differentiable_conj_conj P.entire) P.entire
      (U := {z : ℂ | B < z.re})
      (IsOpen.preimage Complex.continuous_re isOpen_Ioi)
      (z₀ := ((B + 1 : ℝ) : ℂ))
      (by simp only [Set.mem_setOf_eq, Complex.ofReal_re]; linarith)
      ?_
    intro z hz
    simp only [Set.mem_setOf_eq] at hz
    have hz' : B < (conj z).re := by rwa [Complex.conj_re]
    show conj (P.lam (conj z)) = P.lam z
    rw [P.chart (conj z) hz', P.chart z hz, map_mul]
    congr 1
    · rw [map_list_prod, List.map_map]
      congr 1
      refine List.map_congr_left fun μ hmem => ?_
      show conj (Complex.Gammaℂ (conj z + μ)) = Complex.Gammaℂ (z + μ)
      rw [show conj z + μ = conj (z + μ) by rw [map_add, hμ μ hmem]]
      exact GammaC_schwarz (z + μ)
    · exact LSeries_conj_real ha z
  have h := congrFun hglob (conj s)
  simp only [Complex.conj_conj] at h
  calc P.lam (conj s) = conj (conj (P.lam (conj s))) := (Complex.conj_conj _).symm
    _ = conj (P.lam s) := by rw [h, Complex.conj_conj]

/-- Global Schwarz reality of the continuation of a real-data general-chart package. -/
theorem GeneralNicePackage.lam_schwarz {a : ArithmeticFunction ℂ} {dlts μs : List ℂ}
    {B : ℝ} {ε : ℂ} (P : GeneralNicePackage a dlts μs B ε)
    (ha : ∀ n, conj (a n) = a n)
    (hd : ∀ d ∈ dlts, conj d = d) (hμ : ∀ μ ∈ μs, conj μ = μ) (s : ℂ) :
    P.lam (conj s) = conj (P.lam s) := by
  have hglob : (fun z => conj (P.lam (conj z))) = P.lam := by
    refine CriticalLinePhasor.CarrierTargetIdentification.entire_eq_of_eqOn_isOpen
      (differentiable_conj_conj P.entire) P.entire
      (U := {z : ℂ | B < z.re})
      (IsOpen.preimage Complex.continuous_re isOpen_Ioi)
      (z₀ := ((B + 1 : ℝ) : ℂ))
      (by simp only [Set.mem_setOf_eq, Complex.ofReal_re]; linarith)
      ?_
    intro z hz
    simp only [Set.mem_setOf_eq] at hz
    have hz' : B < (conj z).re := by rwa [Complex.conj_re]
    show conj (P.lam (conj z)) = P.lam z
    rw [P.chart (conj z) hz', P.chart z hz, map_mul, map_mul]
    congr 1
    · congr 1
      · rw [map_list_prod, List.map_map]
        congr 1
        refine List.map_congr_left fun d hmem => ?_
        show conj (Complex.Gammaℝ (conj z + d)) = Complex.Gammaℝ (z + d)
        rw [show conj z + d = conj (z + d) by rw [map_add, hd d hmem]]
        exact GammaR_schwarz₀ (z + d)
      · rw [map_list_prod, List.map_map]
        congr 1
        refine List.map_congr_left fun μ hmem => ?_
        show conj (Complex.Gammaℂ (conj z + μ)) = Complex.Gammaℂ (z + μ)
        rw [show conj z + μ = conj (z + μ) by rw [map_add, hμ μ hmem]]
        exact GammaC_schwarz (z + μ)
    · exact LSeries_conj_real ha z
  have h := congrFun hglob (conj s)
  simp only [Complex.conj_conj] at h
  calc P.lam (conj s) = conj (conj (P.lam (conj s))) := (Complex.conj_conj _).symm
    _ = conj (P.lam s) := by rw [h, Complex.conj_conj]

/-! ## The standing wave and unitarity -/

/-- On the axis, conjugation is the completed reflection. -/
theorem axis_conj (t : ℝ) :
    conj ((1 : ℂ) / 2 + (t : ℂ) * I) = 1 - ((1 : ℂ) / 2 + (t : ℂ) * I) := by
  rw [map_add, map_mul, Complex.conj_I, map_div₀, map_one, map_ofNat,
    Complex.conj_ofReal]
  ring

/-- **The standing wave of every real-data package** — the mechanism's endpoint meets
the reduction's endpoint: the package's transform satisfies gate 2's axis condition
`Λ = ε⁻¹·conj Λ` on `Re s = 1/2`, at every rank and chart. -/
theorem NicePackage.standingWave {a : ArithmeticFunction ℂ} {μs : List ℂ} {B : ℝ}
    {ε : ℂ} (P : NicePackage a μs B ε)
    (ha : ∀ n, conj (a n) = a n) (hμ : ∀ μ ∈ μs, conj μ = μ) (hε : ε ≠ 0) (t : ℝ) :
    P.lam ((1 : ℂ) / 2 + (t : ℂ) * I)
      = ε⁻¹ * conj (P.lam ((1 : ℂ) / 2 + (t : ℂ) * I)) := by
  set s : ℂ := (1 : ℂ) / 2 + (t : ℂ) * I with hsdef
  have h1 : conj (P.lam s) = P.lam (1 - s) := by
    rw [← NicePackage.lam_schwarz P ha hμ s, hsdef, axis_conj]
  rw [h1, P.FE s, ← mul_assoc, inv_mul_cancel₀ hε, one_mul]

/-- The general-chart version of the standing wave. -/
theorem GeneralNicePackage.standingWave {a : ArithmeticFunction ℂ} {dlts μs : List ℂ}
    {B : ℝ} {ε : ℂ} (P : GeneralNicePackage a dlts μs B ε)
    (ha : ∀ n, conj (a n) = a n)
    (hd : ∀ d ∈ dlts, conj d = d) (hμ : ∀ μ ∈ μs, conj μ = μ) (hε : ε ≠ 0) (t : ℝ) :
    P.lam ((1 : ℂ) / 2 + (t : ℂ) * I)
      = ε⁻¹ * conj (P.lam ((1 : ℂ) / 2 + (t : ℂ) * I)) := by
  set s : ℂ := (1 : ℂ) / 2 + (t : ℂ) * I with hsdef
  have h1 : conj (P.lam s) = P.lam (1 - s) := by
    rw [← GeneralNicePackage.lam_schwarz P ha hd hμ s, hsdef, axis_conj]
  rw [h1, P.FE s, ← mul_assoc, inv_mul_cancel₀ hε, one_mul]

/-- **Unitarity of the root number, free**: a real-data package whose transform is
nonzero at one axis point has `‖ε‖ = 1` — derived, not assumed. -/
theorem NicePackage.eps_norm_one {a : ArithmeticFunction ℂ} {μs : List ℂ} {B : ℝ}
    {ε : ℂ} (P : NicePackage a μs B ε)
    (ha : ∀ n, conj (a n) = a n) (hμ : ∀ μ ∈ μs, conj μ = μ) (hε : ε ≠ 0) {t : ℝ}
    (h0 : P.lam ((1 : ℂ) / 2 + (t : ℂ) * I) ≠ 0) : ‖ε‖ = 1 := by
  have h := NicePackage.standingWave P ha hμ hε t
  have hn := congrArg norm h
  rw [norm_mul, norm_inv, RCLike.norm_conj] at hn
  have hL : ‖P.lam ((1 : ℂ) / 2 + (t : ℂ) * I)‖ ≠ 0 := norm_ne_zero_iff.mpr h0
  have h1 : ‖ε‖⁻¹ * ‖P.lam ((1 : ℂ) / 2 + (t : ℂ) * I)‖
      = 1 * ‖P.lam ((1 : ℂ) / 2 + (t : ℂ) * I)‖ := by
    rw [one_mul, ← hn]
  have h2 : ‖ε‖⁻¹ = 1 := mul_right_cancel₀ hL h1
  rw [← inv_inv ‖ε‖, h2, inv_one]

end CriticalLinePhasor.PackageStandingWave

#print axioms CriticalLinePhasor.PackageStandingWave.GammaC_schwarz
#print axioms CriticalLinePhasor.PackageStandingWave.LSeries_conj_real
#print axioms CriticalLinePhasor.PackageStandingWave.NicePackage.lam_schwarz
#print axioms CriticalLinePhasor.PackageStandingWave.NicePackage.standingWave
#print axioms CriticalLinePhasor.PackageStandingWave.GeneralNicePackage.standingWave
#print axioms CriticalLinePhasor.PackageStandingWave.NicePackage.eps_norm_one
