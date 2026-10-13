import RequestProject.ExhaustiveCovariance
import RequestProject.SymmetricPairing
import RequestProject.ZetaZeroDefs

/-!
# Audit of the exhaustive realization and of the (a)/(b) identification (ledger 1226)

**The exhaustive object, stated exactly.** Space: linear functionals on Mellin-convergent test functions on
`(0, ∞)`. Group: the transposed area-measure dilations `φ ↦ φ ∘ V_t`. Zero-state at an arbitrary complex `ρ`:
the Mellin evaluation `φ_ρ(f) = 𝓜f(ρ)`. Eigen-equation (group form, no domain issue): `φ_ρ ∘ V_t = e^{t(½ − ρ)}·φ_ρ`
(`Exhaustive.mellin_dilW`), for EVERY complex `ρ`. Zero-subspace at a finite head: the annihilator of the
range of the integer-dilation sum `P`. It is invariant under the transposed dilations (`dilationSum_dilW_comm`), and
`φ_ρ` lies in it iff `S_N(ρ) = 0` (`Exhaustive.annihilates_iff`).

**What a complete HP realization gives.** `hp_realization_implies_re_half`: a symmetric operator with a NONZERO
eigenvector for `i(ρ − ½)` at every nontrivial zero forces every nontrivial zero onto `Re = ½`. A complete HP
construction is sufficient by itself.

**The (a)/(b) audit.** (b-weak), "every zero's height also carries a drift-free cancellation", is
`SourceAtSameHeight`. `rh_implies_sourceAtSameHeight`: RH implies it. It does NOT imply RH: an off-line zero at a
height that also carries an on-line zero satisfies it (by hand). So it is necessary for HP, not sufficient, and
1225's "(a) and (b) are the same statement" is CORRECTED: definiteness ⟺ (b-strong) ⟺ RH; (b-weak) is strictly weaker.
-/

open Complex

noncomputable section

namespace CriticalLinePhasor.HPAudit

open CriticalLinePhasor.AreaDilation CriticalLinePhasor.Exhaustive

/-- **The integer-dilation sum commutes with the native dilations.** The zero-subspace (its annihilator) is
therefore invariant under the transposed dilation group. -/
theorem dilationSum_dilW_comm (w : ℕ → ℂ) (N : ℕ) (t : ℝ) (f : ℝ → ℂ) :
    dilationSum w N (dilW (1 / 2) t f) = dilW (1 / 2) t (dilationSum w N f) := by
  funext x
  unfold dilationSum dilW
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [show Real.exp t * ((n : ℝ) * x) = (n : ℝ) * (Real.exp t * x) by ring]
  ring

/-- **A complete HP realization forces the line.** -/
theorem hp_realization_implies_re_half {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (T : E →ₗ[ℂ] E) (hT : T.IsSymmetric) (v : ℂ → E)
    (hv : ∀ ρ ∈ ZD.NontrivialZeros, v ρ ≠ 0 ∧ T (v ρ) = (I * (ρ - 1 / 2)) • v ρ) :
    ∀ ρ ∈ ZD.NontrivialZeros, ρ.re = 1 / 2 := fun ρ hρ =>
  SymPair.re_eq_half_of_symmetric T hT (hv ρ hρ).1 (hv ρ hρ).2

/-- (b-weak): every nontrivial zero's height also carries a zero on the drift-free line. -/
def SourceAtSameHeight : Prop :=
  ∀ ρ ∈ ZD.NontrivialZeros, riemannZeta ((1 / 2 : ℂ) + (ρ.im : ℂ) * I) = 0

/-- RH implies (b-weak). The converse fails in principle: (b-weak) allows an off-line zero at a height that
also carries an on-line zero. -/
theorem rh_implies_sourceAtSameHeight (hRH : ∀ ρ ∈ ZD.NontrivialZeros, ρ.re = 1 / 2) :
    SourceAtSameHeight := by
  intro ρ hρ
  have hre := hRH ρ hρ
  have hρeq : (1 / 2 : ℂ) + (ρ.im : ℂ) * I = ρ := by
    apply Complex.ext <;> simp [hre]
  rw [hρeq]
  exact hρ.2.2

end CriticalLinePhasor.HPAudit

end

#print axioms CriticalLinePhasor.HPAudit.dilationSum_dilW_comm
#print axioms CriticalLinePhasor.HPAudit.hp_realization_implies_re_half
#print axioms CriticalLinePhasor.HPAudit.rh_implies_sourceAtSameHeight
