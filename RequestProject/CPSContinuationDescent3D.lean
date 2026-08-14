import RequestProject.CPSTemperedLogDerivative3D
import RequestProject.CPSUncompletedContinuation3D

/-!
# Descending the entire continuation to the readout half-plane

The tower's entire `uncompletedContinuation` is identified with the bank Dirichlet series only at
`CPSCompletionPoint`s, i.e. far out in the chart: the point structure asks for positivity of every
shifted Gamma argument and for the two polynomial-growth abscissas, so it carves out a half-plane
`{Re s > R}` with `R` of size `card ι + exponent`.  The Wiener--Ikehara consumer needs the
identification on `{Re s > 1}`.

The gap closes by the identity theorem, and the missing ingredient was analyticity of the series
side on `{Re s > 1}`: that is exactly what `CPSTemperedBankAbscissa3D` now supplies.  Both sides
are analytic on the convex — hence preconnected — half-plane, they agree on the far open subset,
so they agree throughout.

The descent needs temperedness and nothing else; the far-half-plane identification itself is the
compiled `uncompletedContinuation_initialIdentification`, used once at a constructed point.
-/

open Complex Set

namespace CriticalLinePhasor.GlobalHelix
namespace ConventionalCompletedRankinSelbergSource3D

variable {r m : ℕ} {pi : PolynomialSatakeDualPair (Fin 2)}
  {tau : PolynomialSatakeDualPair (Fin m)}
  {D : ArithmeticCPSCompletionData r m}

/-- A finite shift list admits a strict bound on the negated real parts, so the Gamma-positivity
condition of a completion point is itself a half-plane condition. -/
theorem exists_shift_bound (l : List ℂ) : ∃ R : ℝ, ∀ μ ∈ l, -μ.re < R := by
  induction l with
  | nil => exact ⟨0, by simp⟩
  | cons a t ih =>
      obtain ⟨R, hR⟩ := ih
      refine ⟨max R (-a.re + 1), fun μ hμ => ?_⟩
      rcases List.mem_cons.mp hμ with rfl | h
      · exact lt_of_lt_of_le (by linarith) (le_max_right _ _)
      · exact lt_of_lt_of_le (hR μ h) (le_max_left _ _)

/-- The completion points contain a full right half-plane, on which the entire continuation is
literally the bank Dirichlet series. -/
theorem exists_far_halfPlane_uncompletedContinuation_eq_LSeries
    (L : ConventionalCompletedRankinSelbergSource3D r m pi tau D) (hm : 0 < m) :
    ∃ R : ℝ, ∀ s : ℂ, R < s.re →
      L.uncompletedContinuation s = LSeries (⇑L.arithmeticCoefficient) s := by
  obtain ⟨R₀, hR₀⟩ := exists_shift_bound (D.clock hm).shifts
  refine ⟨max R₀ (max
      (((Fintype.card (CPSTensorIndex r m) +
        (arithmeticCPSPolynomialTwist r m pi tau).primalExponent : ℕ) : ℝ) + 1)
      (((Fintype.card (CPSTensorIndex r m) +
        (arithmeticCPSPolynomialTwist r m pi tau).dualExponent : ℕ) : ℝ) + 1)), ?_⟩
  intro s hs
  have h1 : R₀ < s.re := lt_of_le_of_lt (le_max_left _ _) hs
  have h2 : ((Fintype.card (CPSTensorIndex r m) +
      (arithmeticCPSPolynomialTwist r m pi tau).primalExponent : ℕ) : ℝ) + 1 < s.re :=
    lt_of_le_of_lt (le_trans (le_max_left _ _) (le_max_right _ _)) hs
  have h3 : ((Fintype.card (CPSTensorIndex r m) +
      (arithmeticCPSPolynomialTwist r m pi tau).dualExponent : ℕ) : ℝ) + 1 < s.re :=
    lt_of_le_of_lt (le_trans (le_max_right _ _) (le_max_right _ _)) hs
  let point : CPSCompletionPoint (arithmeticCPSPolynomialTwist r m pi tau) (D.clock hm) :=
    { s := s
      shifts_pos := by
        intro μ hμ
        have hμ' := hR₀ μ hμ
        simp only [Complex.add_re]
        linarith
      primal_dirichlet := h2
      dual_dirichlet := h3 }
  have hpoint := L.uncompletedContinuation_initialIdentification hm point
  have hs' : L.eulerConvergenceThreshold < s.re := by
    simpa [eulerConvergenceThreshold] using h2
  exact hpoint.trans (L.uncompletedEuler_eq_LSeries hs')

/-- **The descent.**  Under temperedness the entire continuation equals the bank Dirichlet series
on the whole readout half-plane, not merely on the far chart where the completion points live. -/
theorem uncompletedContinuation_eqOn_LSeries
    (L : ConventionalCompletedRankinSelbergSource3D r m pi tau D) (hm : 0 < m)
    (htemp : ∀ (p : Nat.Primes) (i : CPSTensorIndex r m),
      ‖(arithmeticCPSPolynomialTwist r m pi tau).primal p i‖ = 1) :
    Set.EqOn L.uncompletedContinuation (LSeries (⇑L.arithmeticCoefficient))
      {s : ℂ | 1 < s.re} := by
  obtain ⟨R, hR⟩ := exists_far_halfPlane_uncompletedContinuation_eq_LSeries L hm
  have hUopen : IsOpen {s : ℂ | 1 < s.re} :=
    isOpen_lt continuous_const Complex.continuous_re
  have hUconn : IsPreconnected {s : ℂ | 1 < s.re} :=
    (convex_halfSpace_re_gt 1).isPreconnected
  have hf : AnalyticOnNhd ℂ L.uncompletedContinuation {s : ℂ | 1 < s.re} :=
    (L.uncompletedContinuation_entire.differentiableOn).analyticOnNhd hUopen
  have hg : AnalyticOnNhd ℂ (LSeries (⇑L.arithmeticCoefficient)) {s : ℂ | 1 < s.re} := by
    refine DifferentiableOn.analyticOnNhd (fun z hz => ?_) hUopen
    have habs : LSeries.abscissaOfAbsConv (⇑L.arithmeticCoefficient) < (z.re : EReal) :=
      lt_of_le_of_lt (arithmeticCoefficient_abscissaOfAbsConv_le_one L htemp)
        (by exact_mod_cast hz)
    exact (LSeries_hasDerivAt habs).differentiableAt.differentiableWithinAt
  have hVopen : IsOpen {s : ℂ | R < s.re} :=
    isOpen_lt continuous_const Complex.continuous_re
  set z₀ : ℂ := ((max R 1 + 1 : ℝ) : ℂ) with hz₀
  have hz₀re : z₀.re = max R 1 + 1 := by simp [hz₀]
  have hz₀U : z₀ ∈ {s : ℂ | 1 < s.re} := by
    show 1 < z₀.re
    rw [hz₀re]
    have : (1 : ℝ) ≤ max R 1 := le_max_right _ _
    linarith
  have hz₀V : z₀ ∈ {s : ℂ | R < s.re} := by
    show R < z₀.re
    rw [hz₀re]
    have : R ≤ max R 1 := le_max_left _ _
    linarith
  have hev : L.uncompletedContinuation =ᶠ[nhds z₀] LSeries (⇑L.arithmeticCoefficient) :=
    Filter.eventuallyEq_of_mem (hVopen.mem_nhds hz₀V) (fun z hz => hR z hz)
  exact hf.eqOn_of_preconnected_of_eventuallyEq hg hUconn hz₀U hev

/-- With the descent, the tempered logarithmic-derivative identity is stated directly on the
entire continuation supplied by the tower. -/
theorem LSeries_logarithmicCoefficient_eq_neg_logDeriv_uncompletedContinuation
    (L : ConventionalCompletedRankinSelbergSource3D r m pi tau D) (hm : 0 < m)
    (htemp : ∀ (p : Nat.Primes) (i : CPSTensorIndex r m),
      ‖(arithmeticCPSPolynomialTwist r m pi tau).primal p i‖ = 1)
    {s : ℂ} (hs : 1 < s.re)
    (hne : L.uncompletedContinuation s ≠ 0) :
    LSeries (⇑L.logarithmicCoefficient) s =
      -logDeriv (LSeries (⇑L.arithmeticCoefficient)) s := by
  refine LSeries_logarithmicCoefficient_eq_neg_logDeriv_of_tempered L htemp hs ?_
  rw [← uncompletedContinuation_eqOn_LSeries L hm htemp (Set.mem_setOf.mpr hs)]
  exact hne

end ConventionalCompletedRankinSelbergSource3D
end CriticalLinePhasor.GlobalHelix

#print axioms CriticalLinePhasor.GlobalHelix.ConventionalCompletedRankinSelbergSource3D.exists_far_halfPlane_uncompletedContinuation_eq_LSeries
#print axioms CriticalLinePhasor.GlobalHelix.ConventionalCompletedRankinSelbergSource3D.uncompletedContinuation_eqOn_LSeries
#print axioms CriticalLinePhasor.GlobalHelix.ConventionalCompletedRankinSelbergSource3D.LSeries_logarithmicCoefficient_eq_neg_logDeriv_uncompletedContinuation
