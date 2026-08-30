import RequestProject.SeatingLadderFold
import PrimeNumberTheoremAnd.ZetaBounds

/-!
# The residual shell: where any counterexample must live

Folding the compiled classical zero-free region (`ZetaZeroFree`, PNT+) and its
FE-mirror into the ledger: an off-line zero at ordinate `γ` has depth strictly
inside `1/2 − A/log⁹|γ|`, and by the ladder its ordinate exceeds `1269/2`.
The residual of every register is one shrinking shell.

No `sorry`, no `axiom`.
-/

open Complex ComplexConjugate Set

noncomputable section

namespace CriticalLinePhasor.SeatingLedger

/-- **The depth bound**: an off-line zero hides strictly inside the classical
zero-free depth on both sides of the line. -/
theorem offline_depth_bound :
    ∃ A : ℝ, 0 < A ∧ A ≤ 1/2 ∧ ∀ ρ ∈ ZD.NontrivialZeros, 3 < |ρ.im| →
      |ρ.re - 1/2| < 1/2 - A / (Real.log |ρ.im|)^9 := by
  obtain ⟨A, hA, hfree⟩ := ZetaZeroFree
  refine ⟨A, hA.1, hA.2, ?_⟩
  -- the one-sided bound: any strip zero has re < 1 − A/log⁹|im|
  have hside : ∀ ρ ∈ ZD.NontrivialZeros, 3 < |ρ.im| →
      ρ.re < 1 - A / (Real.log |ρ.im|)^9 := by
    intro ρ hρ ht
    by_contra hge
    push_neg at hge
    have hzero : riemannZeta ((ρ.re : ℂ) + (ρ.im : ℝ) * I) = 0 := by
      rw [Complex.re_add_im]
      exact hρ.2.2
    exact hfree ρ.re ρ.im ht ⟨hge, hρ.2.1⟩ hzero
  intro ρ hρ ht
  rcases le_or_gt ρ.re (1/2) with hle | hgt
  · -- reflect: the mirror has re = 1 − ρ.re ≥ 1/2, same |im|
    have hmir := mirror_mem hρ
    have hmim : |(1 - conj ρ).im| = |ρ.im| := by
      rw [mirror_im]
    have hside' := hside _ hmir (by rw [hmim]; exact ht)
    rw [mirror_re, hmim] at hside'
    have : A / (Real.log |ρ.im|)^9 < ρ.re := by linarith
    rw [abs_of_nonpos (by linarith)]
    linarith
  · have hside' := hside ρ hρ ht
    rw [abs_of_pos (by linarith)]
    linarith

/-- **The residual shell**: any off-line zero has ordinate above the compiled
ladder AND depth inside the classical shell — the single region every
register's residual now occupies. -/
theorem residual_shell :
    ∃ A : ℝ, 0 < A ∧ ∀ ρ ∈ ZD.NontrivialZeros, ρ.re ≠ 1/2 →
      1269/2 < |ρ.im| ∧ |ρ.re - 1/2| < 1/2 - A / (Real.log |ρ.im|)^9 := by
  obtain ⟨A, hA0, _, hdepth⟩ := offline_depth_bound
  refine ⟨A, hA0, fun ρ hρ hre => ?_⟩
  have hladder : 1269/2 < |ρ.im| := by
    by_contra hle
    push_neg at hle
    exact hre (CriticalLinePhasor.DVP.online_below_1269o2 ρ hρ hle)
  exact ⟨hladder, hdepth ρ hρ (by linarith)⟩

end CriticalLinePhasor.SeatingLedger

#print axioms CriticalLinePhasor.SeatingLedger.offline_depth_bound
#print axioms CriticalLinePhasor.SeatingLedger.residual_shell
