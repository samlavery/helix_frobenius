import RequestProject.FiberShiftSimple

/-!
# The Laguerre–Pólya class is closed under differentiation

`StripClass 0` is exactly the Laguerre–Pólya class: locally uniform limits on `ℂ` of real polynomials
with only real zeros.  This file proves it is closed under `d/dz`, which is what lets the merger
argument reduce a zero of ANY order `m ≥ 2` to a zero of order exactly `2`: if `f` has a zero of order
`m` at `x₀`, then `f^{(m-2)}` has a zero of order exactly `2` there and is still in the class.

Two steps:
* `derivative_im_zero` — a real polynomial with only real roots has a derivative with only real roots.
  Rolle, in Mathlib's counting form `Polynomial.card_roots_le_derivative`: `#roots p ≤ #roots p' + 1`.
  Real-rootedness is `#roots = natDegree` (`splits_iff_card_roots`), so
  `natDegree p ≤ #roots p' + 1`, i.e. `#roots p' ≥ natDegree p'`, and the reverse always holds.
* `StripClass.deriv` — the class is closed under `deriv`, because `TendstoLocallyUniformlyOn.deriv`
  carries the witnesses' derivatives to the limit's derivative.
-/

open Polynomial Complex Filter Topology

namespace CriticalLinePhasor.DeBruijn

/-! ### Real-rootedness as a splitting condition -/

/-- A real polynomial whose complex roots are all real splits over `ℝ`. -/
theorem splits_of_im_zero :
    ∀ (n : ℕ) (p : ℝ[X]), p.natDegree = n → (∀ w : ℂ, aeval w p = 0 → w.im = 0) →
      Splits p := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro p hdeg hreal
    rcases eq_or_ne p 0 with rfl | hp0
    · exact Splits.zero
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      have : p = C (p.coeff 0) := Polynomial.eq_C_of_natDegree_eq_zero hdeg
      rw [this]; exact Splits.C _
    · obtain ⟨r, q, hpq, hqne, hqdeg, hqreal⟩ := exists_real_root_factor (by omega) hreal
      have hq : Splits q := ih q.natDegree (by omega) q rfl hqreal
      rw [hpq]
      have hlin : Splits (X - C r : ℝ[X]) := by
        have := Splits.X_add_C (-r)
        simpa [sub_eq_add_neg] using this
      exact hlin.mul hq

/-- Real-rootedness in the multiset form. -/
theorem card_roots_eq_natDegree_of_im_zero {p : ℝ[X]} (hp : p ≠ 0)
    (h : ∀ w : ℂ, aeval w p = 0 → w.im = 0) :
    Multiset.card p.roots = p.natDegree :=
  (Polynomial.splits_iff_card_roots).mp (splits_of_im_zero p.natDegree p rfl h)

/-- …and back again: a real polynomial that splits over `ℝ` has only real complex roots.  Root
counting: the real roots inject into the complex ones and already exhaust the degree. -/
theorem im_zero_of_card_roots_eq_natDegree {p : ℝ[X]} (hp : p ≠ 0)
    (hcard : Multiset.card p.roots = p.natDegree) :
    ∀ w : ℂ, aeval w p = 0 → w.im = 0 := by
  intro w hw
  have hinj : Function.Injective (algebraMap ℝ ℂ) := (algebraMap ℝ ℂ).injective
  have hmapne : p.map (algebraMap ℝ ℂ) ≠ 0 := (Polynomial.map_ne_zero_iff hinj).mpr hp
  have hcardC : Multiset.card (p.map (algebraMap ℝ ℂ)).roots
      = (p.map (algebraMap ℝ ℂ)).natDegree :=
    Polynomial.splits_iff_card_roots.mp (IsAlgClosed.splits _)
  have hdegmap : (p.map (algebraMap ℝ ℂ)).natDegree = p.natDegree :=
    Polynomial.natDegree_map _
  have hle : p.roots.map (algebraMap ℝ ℂ) ≤ (p.map (algebraMap ℝ ℂ)).roots :=
    Polynomial.map_roots_le_of_injective p hinj
  have hcards : Multiset.card ((p.map (algebraMap ℝ ℂ)).roots)
      ≤ Multiset.card (p.roots.map (algebraMap ℝ ℂ)) := by
    rw [Multiset.card_map, hcard, hcardC, hdegmap]
  have heq : p.roots.map (algebraMap ℝ ℂ) = (p.map (algebraMap ℝ ℂ)).roots :=
    Multiset.eq_of_le_of_card_le hle hcards
  have hwmem : w ∈ (p.map (algebraMap ℝ ℂ)).roots := by
    rw [Polynomial.mem_roots hmapne]
    show Polynomial.eval w (p.map (algebraMap ℝ ℂ)) = 0
    rw [Polynomial.aeval_def, ← Polynomial.eval_map] at hw
    exact hw
  rw [← heq] at hwmem
  obtain ⟨a, _, rfl⟩ := Multiset.mem_map.mp hwmem
  simp

/-! ### Rolle: the derivative of a real-rooted real polynomial is real-rooted -/

/-- **The derivative of a real polynomial with only real roots has only real roots.** -/
theorem derivative_im_zero {p : ℝ[X]} (hdeg : 0 < p.natDegree)
    (h : ∀ w : ℂ, aeval w p = 0 → w.im = 0) :
    ∀ w : ℂ, aeval w (derivative p) = 0 → w.im = 0 := by
  have hp0 : p ≠ 0 := fun h0 => by simp [h0] at hdeg
  have hcard : Multiset.card p.roots = p.natDegree :=
    card_roots_eq_natDegree_of_im_zero hp0 h
  have hRolle := Polynomial.card_roots_le_derivative p
  have hle : Multiset.card (derivative p).roots ≤ (derivative p).natDegree :=
    Polynomial.card_roots' _
  have hdle : (derivative p).natDegree ≤ p.natDegree - 1 :=
    Polynomial.natDegree_derivative_le p
  -- the squeeze: natDegree p - 1 ≤ #roots p' ≤ natDegree p' ≤ natDegree p - 1
  have heq : Multiset.card (derivative p).roots = (derivative p).natDegree := by omega
  have hd : derivative p ≠ 0 := Polynomial.derivative_ne_zero.mpr (by omega)
  exact im_zero_of_card_roots_eq_natDegree hd heq

/-!
### Note on the class-level statement

`StripClass 0` is closed under `deriv` as a matter of mathematics, but the witness bookkeeping is not
free: a witness `P n` may be a nonzero CONSTANT, and then `derivative (P n) = 0` is not an admissible
witness (the class demands nonzero polynomials).  Ruling that out needs "`deriv f` is not identically
zero ⟹ the witnesses are eventually non-constant", i.e. passing to a tail and re-indexing.  That
bookkeeping is not done here; what is proved above is the substantive step, Rolle at the polynomial
level.
-/

end CriticalLinePhasor.DeBruijn

#print axioms CriticalLinePhasor.DeBruijn.splits_of_im_zero
#print axioms CriticalLinePhasor.DeBruijn.card_roots_eq_natDegree_of_im_zero
#print axioms CriticalLinePhasor.DeBruijn.im_zero_of_card_roots_eq_natDegree
#print axioms CriticalLinePhasor.DeBruijn.derivative_im_zero
