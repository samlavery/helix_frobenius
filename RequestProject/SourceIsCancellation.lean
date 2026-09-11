import RequestProject.CarrierHeadFiniteFiber
import RequestProject.ZetaZeroDefs

/-!
# A source is a cancellation of two nonzero banks (ledger 693)

Sam's definition (2026-09-09): "the number 0 isn't a natural number, it only exists when its parents cancel each
other exactly, in focal cancellation of phasor banks … every vanishing that leads to a zeta zero happens only when
the banks are non-zero, they need some real absolute value, and that is the source."

Formalised on the head-adapted fiber of `CarrierHeadFiniteFiber`: the P-bank (odd sites) and the M-bank (even sites)
at head `Z`; the fiber is their difference (`finiteFiber_eq_bankP_sub_bankM`, exact at every head); a **source** at
`s` is: both banks nonzero at every large head, and their difference tending to zero as the head grows.
Nothing in the definition mentions an axis; confinement to the axis is a separate statement.
-/

open Complex Filter Topology
open scoped BigOperators
open CriticalLinePhasor.CarrierHeadFiniteFiber

namespace CriticalLinePhasor.Source

/-- The site term `w(n/Z) n^{−s}` at index `k` (site `n = k + 1`). -/
noncomputable def siteTerm (Z : ℝ) (s : ℂ) (k : ℕ) : ℂ :=
  (smoothEntry (((k + 1 : ℕ) : ℝ) / Z) : ℂ) * Complex.exp (-s * (Real.log ((k + 1 : ℕ) : ℝ) : ℂ))

/-- The P-bank: odd sites (`k` even). -/
noncomputable def bankP (Z : ℝ) (s : ℂ) : ℂ :=
  ∑ k ∈ Finset.range ⌈Z⌉₊, if Even k then siteTerm Z s k else 0

/-- The M-bank: even sites (`k` odd). -/
noncomputable def bankM (Z : ℝ) (s : ℂ) : ℂ :=
  ∑ k ∈ Finset.range ⌈Z⌉₊, if Even k then 0 else siteTerm Z s k

/-- The unsigned full bank. -/
noncomputable def fullBank (Z : ℝ) (s : ℂ) : ℂ :=
  ∑ k ∈ Finset.range ⌈Z⌉₊, siteTerm Z s k

/-- **The fiber is the difference of the two banks**, exactly, at every head. -/
theorem finiteFiber_eq_bankP_sub_bankM (Z : ℝ) (s : ℂ) :
    finiteFiber Z s = bankP Z s - bankM Z s := by
  unfold finiteFiber bankP bankM
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k _
  unfold siteTerm
  rcases Nat.even_or_odd k with hk | hk
  · simp [hk, hk.neg_one_pow]
  · have hne : ¬ Even k := Nat.not_even_iff_odd.mpr hk
    simp [hne, hk.neg_one_pow]

/-- The full bank is the sum of the two banks. -/
theorem fullBank_eq_bankP_add_bankM (Z : ℝ) (s : ℂ) :
    fullBank Z s = bankP Z s + bankM Z s := by
  unfold fullBank bankP bankM
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  split_ifs <;> simp

/-- **A source at `s`:** both banks are nonzero at every sufficiently large head, and they cancel exactly in the
limit.  No axis appears in the definition. -/
def HasSource (s : ℂ) : Prop :=
  (∀ᶠ Z in atTop, bankP Z s ≠ 0 ∧ bankM Z s ≠ 0) ∧
    Tendsto (fun Z : ℝ => bankP Z s - bankM Z s) atTop (𝓝 0)

/-- A source is a limit vanishing of the fiber. -/
theorem tendsto_finiteFiber_of_hasSource {s : ℂ} (h : HasSource s) :
    Tendsto (fun Z : ℝ => finiteFiber Z s) atTop (𝓝 0) := by
  refine h.2.congr' (Eventually.of_forall fun Z => ?_)
  exact (finiteFiber_eq_bankP_sub_bankM Z s).symm

/-- **Every zero has a source** (Sam's form): the target statement, stated, not asserted. -/
def EveryZeroHasSource : Prop := ∀ ρ ∈ ZD.NontrivialZeros, HasSource ρ

/-- **Sources lie on the axis**: the separate statement Sam says is proven by other means; stated here so the two
are never conflated. -/
def SourcesOnAxis : Prop := ∀ s : ℂ, HasSource s → s.re = 1 / 2

end CriticalLinePhasor.Source

#print axioms CriticalLinePhasor.Source.finiteFiber_eq_bankP_sub_bankM
#print axioms CriticalLinePhasor.Source.tendsto_finiteFiber_of_hasSource
