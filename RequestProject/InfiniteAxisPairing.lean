import RequestProject.AxisPairing
import Mathlib.Analysis.Complex.Basic

/-!
# Infinite axis pairing

The finite odd lane-mode criterion extends to absolutely convergent coefficient banks.  Extinction
of every range truncation passes to extinction of the infinite odd mode.
-/

open Complex Filter Topology
open scoped BigOperators

namespace AxisPairing

/-- The odd lane-mode of a convergent infinite coefficient bank. -/
noncomputable def oddModeInfinite (ε : ℂ) (K K' : ℕ → ℂ) : ℂ :=
  ∑' n, (K n - ε * (starRingEnd ℂ) (K' n))

/-- The infinite axis functional equation is exactly extinction of the infinite odd lane-mode. -/
theorem infinite_fe_iff_oddModeInfinite_eq_zero
    (ε : ℂ) (K K' : ℕ → ℂ) (hK : Summable K) (hK' : Summable K') :
    (∑' n, K n) = ε * (starRingEnd ℂ) (∑' n, K' n) ↔
      oddModeInfinite ε K K' = 0 := by
  have hconj : Summable (fun n => (starRingEnd ℂ) (K' n)) :=
    Complex.summable_conj.mpr hK'
  have hdual : Summable (fun n => ε * (starRingEnd ℂ) (K' n)) := hconj.mul_left ε
  have hodd : oddModeInfinite ε K K' =
      (∑' n, K n) - ε * (starRingEnd ℂ) (∑' n, K' n) := by
    unfold oddModeInfinite
    rw [hK.tsum_sub hdual, hconj.tsum_mul_left, ← Complex.conj_tsum]
  rw [hodd, sub_eq_zero]

/-- If every finite range truncation has zero odd mode, the convergent infinite odd mode is zero. -/
theorem oddModeInfinite_eq_zero_of_range
    (ε : ℂ) (K K' : ℕ → ℂ) (hK : Summable K) (hK' : Summable K')
    (hrange : ∀ N, oddMode ε K K' (Finset.range N) = 0) :
    oddModeInfinite ε K K' = 0 := by
  let h : ℕ → ℂ := fun n => K n - ε * (starRingEnd ℂ) (K' n)
  have hconj : Summable (fun n => (starRingEnd ℂ) (K' n)) :=
    Complex.summable_conj.mpr hK'
  have hs : Summable h := hK.sub (hconj.mul_left ε)
  have hpartial : (fun N => ∑ n ∈ Finset.range N, h n) = fun _ => 0 := by
    funext N
    simpa [h, oddMode] using hrange N
  have ht := hs.hasSum.tendsto_sum_nat
  rw [hpartial] at ht
  have hzero : (∑' n, h n) = 0 := tendsto_nhds_unique ht tendsto_const_nhds
  simpa [oddModeInfinite, h] using hzero

end AxisPairing

#print axioms AxisPairing.infinite_fe_iff_oddModeInfinite_eq_zero
#print axioms AxisPairing.oddModeInfinite_eq_zero_of_range
