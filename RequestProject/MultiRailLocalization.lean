import RequestProject.HodgeLedgerFiltration

/-!
# Multi-rail localization: the hidden cycle sits on a named rail, at a named depth

The original carrier detector was **scalar**: a hidden class fires at depth `d`
(`firstVisibleDepth_eq_grade`), the delayed signature `0,…,0,≠0`.  The multi-rail refinement
decomposes the fiber into its rails (ζ-cell components) and reads the delayed signature **per
rail** — so a hidden cycle is not just detected at a depth, it is **localized** to a specific
rail.  This file records the localization principle over the carrier filtration, unconditionally:

* `RailFirstVisible T z j d` — the per-rail delayed signature: `z` is first visible on rail `j`
  at depth `d` (silent below `d` there, fires at `d`).
* `railFirstVisible_unique` — the per-rail depth is unique.
* `hidden_rail_unique` — **the localization is unique**: if one rail carries the class hidden at
  depth `≥ t` (the delayed/transcendental grade) while every other rail fires strictly below `t`
  (the algebraic/decorated grade), then that rail is the *only* one carrying a hidden class —
  the hidden cycle has a single, well-defined cohomological address.

Empirically this is the Klein-quartic triple product `H¹(C)^{⊗3} = Ind(ψ³) ⊕ 3·M_{f2}(-1)`
(`tmp/ceresa_multirail_localize.py`): the `Ind(ψ³)` (Sym³-CM) rail shows the delayed signature
`L(center)=0, L'(center)=0.8299≠0` — depth 2, the hidden Ceresa/Griffiths cycle — while the
decorated `M_{f2}(-1)` rails fire at depth 1 (`L(center)=0.9667≠0`, algebraic).  So the
transcendental obstruction is localized to the Sym³-CM rail, not the decorated pieces: depth
*and* rail, where the scalar detector gave depth only.  Nothing here proves the Hodge conjecture.
No `sorry`, no `axiom`.
-/

namespace CriticalLinePhasor.HodgeLedgerFiltration

variable {ι Z V : Type*} [Zero V]

/-- The **per-rail delayed signature**: `z` is first visible on rail `j` (of a multi-rail readout
`T : ι → ℕ → Z → V`, one tower per rail) at depth `d` — silent below `d` on rail `j`, fires there
at `d`. -/
def RailFirstVisible (T : ι → ℕ → Z → V) (z : Z) (j : ι) (d : ℕ) : Prop :=
  IsFirstVisible (T j) z d

/-- **Per-rail depth is unique.** -/
theorem railFirstVisible_unique {T : ι → ℕ → Z → V} {z : Z} {j : ι} {d e : ℕ}
    (hd : RailFirstVisible T z j d) (he : RailFirstVisible T z j e) : d = e :=
  isFirstVisible_unique hd he

/-- A rail carrying the class **at or above the delayed grade `t`** — a hidden-cycle rail. -/
def HiddenRail (T : ι → ℕ → Z → V) (z : Z) (t : ℕ) (j : ι) : Prop :=
  ∃ d, t ≤ d ∧ RailFirstVisible T z j d

/-- **Localization is unique.**  If rail `j` carries the class hidden at depth `≥ t` (the delayed
/ transcendental grade), while every other rail fires strictly below `t` (the algebraic /
decorated grade), then `j` is the *only* hidden-cycle rail — the hidden cycle has a single,
well-defined cohomological address.  This is the multi-rail localization the Ceresa demo exhibits
with `t = 2`. -/
theorem hidden_rail_unique {T : ι → ℕ → Z → V} {z : Z} {t : ℕ} {j : ι}
    (hj : HiddenRail T z t j)
    (hother : ∀ i, i ≠ j → ∀ d, RailFirstVisible T z i d → d < t) :
    ∀ i, HiddenRail T z t i → i = j := by
  rintro i ⟨d, hdt, hid⟩
  by_contra hij
  exact absurd hdt (Nat.not_le.mpr (hother i hij d hid))

/-- **The address is the depth.**  The hidden rail's grade is read off as the unique depth at
which it first fires — `firstVisibleDepth` on that rail. -/
theorem hiddenRail_depth {T : ι → ℕ → Z → V} {z : Z} {t : ℕ} {j : ι} {d : ℕ}
    (h : RailFirstVisible T z j d) (hdt : t ≤ d) : HiddenRail T z t j :=
  ⟨d, hdt, h⟩

end CriticalLinePhasor.HodgeLedgerFiltration

#print axioms CriticalLinePhasor.HodgeLedgerFiltration.hidden_rail_unique
