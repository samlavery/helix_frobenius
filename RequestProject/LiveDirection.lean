import RequestProject.ChannelConstancy

/-!
# The live-direction law — a lock freezes every balanced direction but its own partition

The grade-4 recognition loop measured a sharp pointer law (`GRADE4_PROGRESS.md` item 14): an
isogeny lock `θᵢ = θⱼ, θₖ = θₗ` on a product of elliptic curves freezes the two folded
pair-directions that carry `(+, −)` on each locked pair, while the **one** direction whose own
balanced bipartition *equals* the locked partition stays **live**.  Read as a pointer: the
single live direction *names* the lock, so distinct locks give distinct live directions.

This file proves that law inside `ChannelConstancy`'s finite-group model, where "freeze" is
annihilation `ε ∈ H^⊥` of the equidistribution subgroup `H` (`ChannelConstancy.AlgFrozen`).  The
`g = 4` locks are the three two-pair partitions of `{0,1,2,3}`, each a subgroup
`H = {x : xᵢ = xⱼ ∧ xₖ = xₗ}` presented as the range of the lock hom `(a, b) ↦` (vector with `a`
on the first pair, `b` on the second).  The three balanced pair-directions are the `±1` sign
vectors `dir` of the three partitions.

* `mkLock`, `selOf`, `lockSub` — the lock hom and the three lock subgroups (`Pairing`-indexed).
* `algFrozen_lockSub_iff` — **the freeze characterization**: `ε` annihilates the lock iff its
  two pair-sums vanish (`Σ_{first pair} εₜ = 0` and `Σ_{second pair} εₜ = 0`) — the pairing is a
  DC condition per locked pair.  Instantiated: `algFrozen_oneTwo_iff` etc.
* `dirOf` — the balanced sign direction of each partition.
* `algFrozen_dirOf_iff` — **the live-direction law**: `dirOf p'` is frozen by lock `p` **iff
  `p ≠ p'`**.  So of the three balanced directions, exactly the two with `p' ≠ p` freeze, and the
  one whose partition equals the lock (`p' = p`) is live — requires only that the reading resolves
  the sign, `(2 : ZMod N) ≠ 0`.
* `oneTwo_freeze_pattern` — the representative `{12|34}` instance: `dir₁` live, `dir₂`, `dir₃`
  frozen.
* `live_names_lock` — the pointer read: `dirOf p'` is the (unique) live direction of lock `p` iff
  `p' = p`.
* `pointer_injective` — **the pointer property**: `dirOf` is injective — distinct lock-partitions
  give distinct live directions.

**Scope.**  This is the finite-group model of the pointer law: the annihilator characterization
and the freeze/live bookkeeping of the three grade-4 partitions.  It carries no arithmetic — that
the equidistribution subgroup `H` of a degenerate motive *is* the isogeny partition (so the
measured freeze pattern realises this model) is Sato–Tate / Hodge–Tate territory, cited in the
atlas and neither assumed nor proven here.  Nothing here assumes or proves RH/GRH.  No `axiom`,
no `sorry`.
-/

open ChannelConstancy Finset
open scoped BigOperators

namespace LiveDirection

variable {N : ℕ}

/-- The three two-pair partitions of `{0,1,2,3}` — the grade-4 lock/direction index. -/
inductive Pairing
  | oneTwo    -- {0,1 | 2,3}
  | oneThree  -- {0,2 | 1,3}
  | oneFour   -- {0,3 | 1,2}
  deriving DecidableEq

/-- The **lock hom** of a pair-assignment `sel : Fin 4 → Bool` (`false` = first pair, `true` =
second): `(a, b) ↦` the vector carrying `a` on the first pair and `b` on the second.  Its range is
the equidistribution subgroup `{x : x constant on each pair}`. -/
def mkLock (sel : Fin 4 → Bool) : (ZMod N × ZMod N) →+ (Fin 4 → ZMod N) where
  toFun q := fun t => if sel t then q.2 else q.1
  map_zero' := by funext t; by_cases h : sel t <;> simp [h]
  map_add' q r := by
    funext t; by_cases h : sel t <;> simp [h, Pi.add_apply, Prod.fst_add, Prod.snd_add]

/-- The pair-assignment of each partition. -/
def selOf : Pairing → (Fin 4 → Bool)
  | .oneTwo   => ![false, false, true, true]
  | .oneThree => ![false, true, false, true]
  | .oneFour  => ![false, true, true, false]

/-- The **lock subgroup** of a partition: the equidistribution subgroup fixed by the two-pair
relation. -/
def lockSub (p : Pairing) : AddSubgroup (Fin 4 → ZMod N) := (mkLock (selOf p)).range

/-- The lock hom evaluated inside `dot`: `dot ε (mkLock sel q) = Σₜ εₜ·(sel-picked qᵢ)`. -/
lemma dot_mkLock (sel : Fin 4 → Bool) (ε : Fin 4 → ZMod N) (q : ZMod N × ZMod N) :
    dot ε (mkLock sel q) = ∑ t, ε t * (if sel t then q.2 else q.1) := rfl

/-- **The freeze characterization**: `ε` annihilates the lock iff each locked pair is a DC lane —
the pair-sum `Σ_{first pair} εₜ` and `Σ_{second pair} εₜ` both vanish.  A generic form; the three
partitions specialise below. -/
lemma algFrozen_lockSub_iff (sel : Fin 4 → Bool) (ε : Fin 4 → ZMod N) :
    AlgFrozen (mkLock sel).range ε ↔
      ((∑ t, if sel t then (0 : ZMod N) else ε t) = 0 ∧
       (∑ t, if sel t then ε t else 0) = 0) := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · have key := h (mkLock sel (1, 0)) (AddMonoidHom.mem_range.2 ⟨(1, 0), rfl⟩)
      rw [dot_mkLock] at key
      simpa [mul_ite] using key
    · have key := h (mkLock sel (0, 1)) (AddMonoidHom.mem_range.2 ⟨(0, 1), rfl⟩)
      rw [dot_mkLock] at key
      simpa [mul_ite] using key
  · rintro ⟨h1, h2⟩ x ⟨q, rfl⟩
    rw [dot_mkLock]
    have hsplit : ∀ t, ε t * (if sel t then q.2 else q.1)
        = (if sel t then ε t else 0) * q.2 + (if sel t then (0 : ZMod N) else ε t) * q.1 := by
      intro t; by_cases h : sel t <;> simp [h]
    simp_rw [hsplit]
    rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul, h1, h2]
    ring

/-- `{12|34}` freeze characterization: `ε₀ + ε₁ = 0 ∧ ε₂ + ε₃ = 0`. -/
lemma algFrozen_oneTwo_iff (ε : Fin 4 → ZMod N) :
    AlgFrozen (lockSub .oneTwo) ε ↔ (ε 0 + ε 1 = 0 ∧ ε 2 + ε 3 = 0) := by
  simp only [lockSub]
  rw [algFrozen_lockSub_iff]
  simp [selOf, Fin.sum_univ_four]

/-- `{13|24}` freeze characterization: `ε₀ + ε₂ = 0 ∧ ε₁ + ε₃ = 0`. -/
lemma algFrozen_oneThree_iff (ε : Fin 4 → ZMod N) :
    AlgFrozen (lockSub .oneThree) ε ↔ (ε 0 + ε 2 = 0 ∧ ε 1 + ε 3 = 0) := by
  simp only [lockSub]
  rw [algFrozen_lockSub_iff]
  simp [selOf, Fin.sum_univ_four]

/-- `{14|23}` freeze characterization: `ε₀ + ε₃ = 0 ∧ ε₁ + ε₂ = 0`. -/
lemma algFrozen_oneFour_iff (ε : Fin 4 → ZMod N) :
    AlgFrozen (lockSub .oneFour) ε ↔ (ε 0 + ε 3 = 0 ∧ ε 1 + ε 2 = 0) := by
  simp only [lockSub]
  rw [algFrozen_lockSub_iff]
  simp [selOf, Fin.sum_univ_four]

/-- The **balanced sign direction** of each partition: `+1` on the first pair, `−1` on the
second — the folded pair-direction whose bipartition *is* that partition. -/
def dirOf : Pairing → (Fin 4 → ZMod N)
  | .oneTwo   => ![1, 1, -1, -1]
  | .oneThree => ![1, -1, 1, -1]
  | .oneFour  => ![1, -1, -1, 1]

/-- **The live-direction law**: the balanced direction `dirOf p'` is frozen by lock `p` **iff
`p ≠ p'`**.  So exactly two of the three directions freeze under any lock, and the survivor —
the one whose partition equals the lock — is the live pointer.  Needs only that the reading
resolves the sign, `(2 : ZMod N) ≠ 0`. -/
theorem algFrozen_dirOf_iff (h2 : (2 : ZMod N) ≠ 0) (p p' : Pairing) :
    AlgFrozen (lockSub (N := N) p) (dirOf (N := N) p') ↔ p ≠ p' := by
  have hne : (1 : ZMod N) + 1 ≠ 0 := fun h => h2 (by rwa [one_add_one_eq_two] at h)
  have h0 : (1 : ZMod N) + (-1) = 0 := by ring
  have h0' : (-1 : ZMod N) + 1 = 0 := by ring
  cases p <;> cases p' <;>
    simp only [algFrozen_oneTwo_iff, algFrozen_oneThree_iff, algFrozen_oneFour_iff, dirOf,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
      Matrix.tail_cons, Matrix.cons_val_three, h0, h0', and_self, ne_eq,
      reduceCtorEq, not_false_eq_true, not_true_eq_false, iff_false]
  all_goals (rintro ⟨ha, _⟩; exact hne ha)

/-- **The representative `{12|34}` freeze pattern**: `dir₁` (partition `{12|34}`, equal to the
lock) is live; `dir₂`, `dir₃` freeze — exactly two of the three balanced directions freeze. -/
theorem oneTwo_freeze_pattern (h2 : (2 : ZMod N) ≠ 0) :
    ¬ AlgFrozen (lockSub (N := N) .oneTwo) (dirOf .oneTwo)
      ∧ AlgFrozen (lockSub (N := N) .oneTwo) (dirOf .oneThree)
      ∧ AlgFrozen (lockSub (N := N) .oneTwo) (dirOf .oneFour) :=
  ⟨fun hfr => (algFrozen_dirOf_iff h2 .oneTwo .oneTwo).1 hfr rfl,
   (algFrozen_dirOf_iff h2 .oneTwo .oneThree).2 (by decide),
   (algFrozen_dirOf_iff h2 .oneTwo .oneFour).2 (by decide)⟩

/-- **The pointer read**: `dirOf p'` is the (unique) live direction of lock `p` iff `p' = p` —
the live direction *names* the locked partition. -/
theorem live_names_lock (h2 : (2 : ZMod N) ≠ 0) (p p' : Pairing) :
    (¬ AlgFrozen (lockSub (N := N) p) (dirOf p')) ↔ p' = p := by
  simp only [algFrozen_dirOf_iff h2, ne_eq, not_not, eq_comm]

/-- **The pointer property**: distinct lock-partitions give distinct live directions —
`dirOf` is injective (once the reading resolves the sign). -/
theorem pointer_injective (h2 : (2 : ZMod N) ≠ 0) :
    Function.Injective (dirOf (N := N)) := by
  intro p p' heq
  by_contra hne
  have hfr : AlgFrozen (lockSub (N := N) p) (dirOf p') := (algFrozen_dirOf_iff h2 p p').2 hne
  have hlv : ¬ AlgFrozen (lockSub (N := N) p) (dirOf p) := fun h =>
    (algFrozen_dirOf_iff h2 p p).1 h rfl
  rw [heq] at hlv
  exact hlv hfr

end LiveDirection

#print axioms LiveDirection.algFrozen_lockSub_iff
#print axioms LiveDirection.algFrozen_dirOf_iff
#print axioms LiveDirection.oneTwo_freeze_pattern
#print axioms LiveDirection.live_names_lock
#print axioms LiveDirection.pointer_injective
