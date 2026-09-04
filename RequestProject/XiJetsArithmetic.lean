import Mathlib
import RequestProject.HermFormJetsFold
import RequestProject.ZetaScrewArithmetic

/-!
# The jets of `ξ′/ξ` in the prime chart `Re s > 1` (ledger 595)

On `Re s > 1` the house has `ξ′/ξ(s) = 1/s + 1/(s−1) − (log π)/2 + ½·Γ′/Γ(s/2) − Σ Λ(n) n^{−s}`
(`logDeriv_riemannXi_arith`). Every piece is analytic there, so the `m`-th jet splits
(`xi_jet_arith`, `m ≥ 1`):

  `(ξ′/ξ)^{(m)}(s) = (−1)^m m! (s^{−m−1} + (s−1)^{−m−1}) + (½ Γ′/Γ(·/2))^{(m)}(s) − (−1)^m Σ Λ(n) (log n)^m n^{−s}`

(`iter_deriv_inv`, `LSeries_iteratedDeriv`). Combined with `rh_iff_jets_s_nonneg` this puts the
door's hypothesis entirely in the prime chart: pole jets, the Archimedean jet, and the log-weighted
von Mangoldt series at `s = σ₀ + iγ`.
-/

open Complex Filter Topology
open scoped LSeries.notation
open LSeries

noncomputable section

namespace CriticalLinePhasor.ContourArgument

/-- The abscissa of absolute convergence of the von Mangoldt series is at most `1`. -/
theorem abscissa_vonMangoldt_le_one :
    abscissaOfAbsConv (fun n => ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)) ≤ ((1 : ℝ) : EReal) := by
  apply LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable
  intro y hy
  exact ArithmeticFunction.LSeriesSummable_vonMangoldt (by simpa using hy)

theorem analyticAt_Gamma_of_re_pos {z : ℂ} (hz : 0 < z.re) : AnalyticAt ℂ Complex.Gamma z := by
  have hopen : IsOpen {w : ℂ | 0 < w.re} := isOpen_lt continuous_const Complex.continuous_re
  refine DifferentiableOn.analyticAt (s := {w : ℂ | 0 < w.re}) ?_ (hopen.mem_nhds hz)
  intro w hw
  refine (Complex.differentiableAt_Gamma w ?_).differentiableWithinAt
  intro m hm
  have h1 : w.re = -(m : ℝ) := by rw [hm]; simp
  have h2 : 0 < w.re := hw
  have h3 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  linarith

/-- The Archimedean term `½ Γ′/Γ(z/2)` is analytic on `Re z > 0`. -/
theorem analyticAt_gammaTerm {s : ℂ} (hs : 0 < s.re) :
    AnalyticAt ℂ (fun z : ℂ => logDeriv Complex.Gamma (z / 2) / 2) s := by
  have hhalf : AnalyticAt ℂ (fun z : ℂ => z / 2) s := analyticAt_id.div_const
  have hre : 0 < (s / 2).re := by
    simp only [Complex.div_ofNat_re]
    linarith
  have hΓ : AnalyticAt ℂ Complex.Gamma (s / 2) := analyticAt_Gamma_of_re_pos hre
  have hΓ' : AnalyticAt ℂ (deriv Complex.Gamma) (s / 2) := hΓ.deriv
  have hne : Complex.Gamma (s / 2) ≠ 0 := Complex.Gamma_ne_zero_of_re_pos hre
  have h1 : AnalyticAt ℂ (deriv Complex.Gamma ∘ fun z : ℂ => z / 2) s :=
    AnalyticAt.comp (f := fun z : ℂ => z / 2) (x := s) hΓ' hhalf
  have h2 : AnalyticAt ℂ (Complex.Gamma ∘ fun z : ℂ => z / 2) s :=
    AnalyticAt.comp (f := fun z : ℂ => z / 2) (x := s) hΓ hhalf
  have h3 : AnalyticAt ℂ (fun z : ℂ => deriv Complex.Gamma (z / 2) / Complex.Gamma (z / 2)) s :=
    h1.div h2 hne
  have h4 : (fun z : ℂ => logDeriv Complex.Gamma (z / 2) / 2)
      = fun z => (deriv Complex.Gamma (z / 2) / Complex.Gamma (z / 2)) / 2 := by
    funext z
    rw [logDeriv_apply]
  rw [h4]
  exact h3.div_const

/-- **The jets of `ξ′/ξ` in the prime chart.** For `Re s > 1` and `m ≥ 1`. -/
theorem xi_jet_arith {s : ℂ} (hs : 1 < s.re) {m : ℕ} (hm : 1 ≤ m) :
    iteratedDeriv m (logDeriv ZD.riemannXi) s
      = (-1) ^ m * (m.factorial : ℂ) * (s ^ (-1 - m : ℤ) + (s - 1) ^ (-1 - m : ℤ))
        + iteratedDeriv m (fun z : ℂ => logDeriv Complex.Gamma (z / 2) / 2) s
        - (-1) ^ m * LSeries (logMul^[m] (fun n => ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ))) s := by
  have hopen : IsOpen {z : ℂ | 1 < z.re} := isOpen_lt continuous_const Complex.continuous_re
  have hEq : logDeriv ZD.riemannXi =ᶠ[𝓝 s]
      (fun z => 1 / z + 1 / (z - 1) - ((Real.log Real.pi : ℝ) : ℂ) / 2
        + logDeriv Complex.Gamma (z / 2) / 2
        - LSeries (fun n => ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)) z) :=
    Filter.eventually_of_mem (hopen.mem_nhds hs)
      (fun z hz => CriticalLinePhasor.HilbertPolya.logDeriv_riemannXi_arith hz)
  rw [(hEq.iteratedDeriv m).eq_of_nhds]
  have hs0 : s ≠ 0 := by
    intro h
    rw [h, Complex.zero_re] at hs
    linarith
  have hs1 : s - 1 ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  have habs : abscissaOfAbsConv (fun n => ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)) < (s.re : EReal) :=
    lt_of_le_of_lt abscissa_vonMangoldt_le_one (by exact_mod_cast hs)
  -- analyticity of the pieces
  have hA : AnalyticAt ℂ (fun z : ℂ => 1 / z) s := analyticAt_const.div analyticAt_id hs0
  have hB : AnalyticAt ℂ (fun z : ℂ => 1 / (z - 1)) s :=
    analyticAt_const.div (analyticAt_id.sub analyticAt_const) hs1
  have hC : AnalyticAt ℂ (fun _ : ℂ => ((Real.log Real.pi : ℝ) : ℂ) / 2) s := analyticAt_const
  have hD := analyticAt_gammaTerm (by linarith : 0 < s.re)
  have hE : AnalyticAt ℂ (LSeries (fun n => ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ))) s :=
    LSeries_analyticOnNhd _ s habs
  have hAB : ContDiffAt ℂ m (fun z : ℂ => 1 / z + 1 / (z - 1)) s := (hA.add hB).contDiffAt
  have hABC : ContDiffAt ℂ m (fun z : ℂ => 1 / z + 1 / (z - 1) - ((Real.log Real.pi : ℝ) : ℂ) / 2) s :=
    ((hA.add hB).sub hC).contDiffAt
  have hABCD : ContDiffAt ℂ m (fun z : ℂ => 1 / z + 1 / (z - 1) - ((Real.log Real.pi : ℝ) : ℂ) / 2
      + logDeriv Complex.Gamma (z / 2) / 2) s := (((hA.add hB).sub hC).add hD).contDiffAt
  rw [iteratedDeriv_fun_sub hABCD hE.contDiffAt, iteratedDeriv_fun_add hABC hD.contDiffAt,
    iteratedDeriv_fun_sub hAB hC.contDiffAt, iteratedDeriv_fun_add hA.contDiffAt hB.contDiffAt]
  -- evaluate the explicit pieces
  have eA : iteratedDeriv m (fun z : ℂ => 1 / z) s = (-1) ^ m * (m.factorial : ℂ) * s ^ (-1 - m : ℤ) := by
    have : (fun z : ℂ => 1 / z) = Inv.inv := funext (fun z => one_div z)
    rw [this, iteratedDeriv_eq_iterate, iter_deriv_inv]
  have eB : iteratedDeriv m (fun z : ℂ => 1 / (z - 1)) s
      = (-1) ^ m * (m.factorial : ℂ) * (s - 1) ^ (-1 - m : ℤ) := by
    have : (fun z : ℂ => 1 / (z - 1)) = fun z => Inv.inv (z - 1) := funext (fun z => one_div _)
    rw [this, iteratedDeriv_comp_sub_const]
    dsimp only
    rw [iteratedDeriv_eq_iterate, iter_deriv_inv]
  have eC : iteratedDeriv m (fun _ : ℂ => ((Real.log Real.pi : ℝ) : ℂ) / 2) s = 0 := by
    rw [iteratedDeriv_const, if_neg (by omega)]
  have eE := LSeries_iteratedDeriv m habs
  rw [eA, eB, eC, eE]
  ring

/-! ## The door in the prime chart -/

/-- The prime-chart value of the `m`-th jet of `ξ′/ξ` (`m ≥ 1`): pole jets + Archimedean jet −
log-weighted von Mangoldt series. -/
def primeJet (s : ℂ) (m : ℕ) : ℂ :=
  (-1) ^ m * (m.factorial : ℂ) * (s ^ (-1 - m : ℤ) + (s - 1) ^ (-1 - m : ℤ))
    + iteratedDeriv m (fun z : ℂ => logDeriv Complex.Gamma (z / 2) / 2) s
    - (-1) ^ m * LSeries (logMul^[m] (fun n => ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ))) s

/-- The prime-chart value of `ξ′/ξ` itself. -/
def primeLogDeriv (s : ℂ) : ℂ :=
  1 / s + 1 / (s - 1) - ((Real.log Real.pi : ℝ) : ℂ) / 2 + logDeriv Complex.Gamma (s / 2) / 2
    - LSeries (fun n => ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)) s

/-- The jet functional of one monomial pair, written in the prime chart. -/
def jetValueP (s d : ℂ) (M : ℕ) (j k : ℕ) : ℂ :=
  (pf d j k).1 1 * (2 * ((primeLogDeriv s).re : ℂ))
    + ∑ i ∈ Finset.range (M - 1), (pf d j k).1 (i + 2)
        * (primeJet s (i + 1) / ((-1) ^ (i + 1) * ((i + 1).factorial : ℂ)))
    + ∑ l ∈ Finset.range (M - 1), (pf d j k).2 (l + 2)
        * ((-1) ^ (l + 1) * (starRingEnd ℂ) (primeJet s (l + 1)) / ((l + 1).factorial : ℂ))

theorem jetValueS_eq_jetValueP {s : ℂ} (hs : 1 < s.re) (d : ℂ) (M j k : ℕ) :
    jetValueS s d M j k = jetValueP s d M j k := by
  unfold jetValueS jetValueP
  congr 1
  · congr 1
    · rw [CriticalLinePhasor.HilbertPolya.logDeriv_riemannXi_arith hs]
      rfl
    · exact Finset.sum_congr rfl (fun i _ => by
        rw [xi_jet_arith hs (by omega : 1 ≤ i + 1)]
        rfl)
  · exact Finset.sum_congr rfl (fun l _ => by
      rw [xi_jet_arith hs (by omega : 1 ≤ l + 1)]
      rfl)

/-- **The door in the prime chart.** RH ⟺ for all `γ`, all `1 < σ₀ < 3/2`, all `R` with `R(0) = 0`:
`Re Σ_{j,k} conj(r_j) r_k · jetValueP(σ₀+iγ, 2σ₀−1) j k ≥ 0`. The hypothesis side is built from
`1/s`, `1/(s−1)`, `log π`, the jets of `½Γ′/Γ(·/2)`, and `Σ Λ(n)(log n)^m n^{−s}` at `s = σ₀ + iγ` —
no zero of `ζ` appears in it. -/
theorem rh_iff_prime_jets_nonneg :
    (∀ ρ ∈ ZD.NontrivialZeros, ρ.re = 1 / 2) ↔
    (∀ γ σ₀ : ℝ, 1 < σ₀ → σ₀ < 3 / 2 → ∀ R : Polynomial ℂ, R.coeff 0 = 0 →
      0 ≤ (∑ j ∈ Finset.range (R.natDegree + 1), ∑ k ∈ Finset.range (R.natDegree + 1),
          ((starRingEnd ℂ) (R.coeff j) * R.coeff k)
            * jetValueP ((σ₀ : ℂ) + (γ : ℂ) * I) ((2 * σ₀ - 1 : ℝ) : ℂ)
                (2 * R.natDegree + 2) j k).re) := by
  rw [rh_iff_jets_s_nonneg]
  have hre : ∀ γ σ₀ : ℝ, 1 < σ₀ → 1 < ((σ₀ : ℂ) + (γ : ℂ) * I).re := by
    intro γ σ₀ h
    simpa using h
  have key : ∀ (γ σ₀ : ℝ), 1 < σ₀ → ∀ R : Polynomial ℂ,
      (∑ j ∈ Finset.range (R.natDegree + 1), ∑ k ∈ Finset.range (R.natDegree + 1),
          ((starRingEnd ℂ) (R.coeff j) * R.coeff k)
            * jetValueS ((σ₀ : ℂ) + (γ : ℂ) * I) ((2 * σ₀ - 1 : ℝ) : ℂ) (2 * R.natDegree + 2) j k)
      = ∑ j ∈ Finset.range (R.natDegree + 1), ∑ k ∈ Finset.range (R.natDegree + 1),
          ((starRingEnd ℂ) (R.coeff j) * R.coeff k)
            * jetValueP ((σ₀ : ℂ) + (γ : ℂ) * I) ((2 * σ₀ - 1 : ℝ) : ℂ) (2 * R.natDegree + 2) j k := by
    intro γ σ₀ h R
    refine Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun k _ => ?_))
    rw [jetValueS_eq_jetValueP (hre γ σ₀ h)]
  constructor
  · intro H γ σ₀ h1 h2 R hR
    rw [← key γ σ₀ h1 R]
    exact H γ σ₀ h1 h2 R hR
  · intro H γ σ₀ h1 h2 R hR
    rw [key γ σ₀ h1 R]
    exact H γ σ₀ h1 h2 R hR

#print axioms xi_jet_arith
#print axioms rh_iff_prime_jets_nonneg

end CriticalLinePhasor.ContourArgument
