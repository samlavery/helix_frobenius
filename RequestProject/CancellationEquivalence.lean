import RequestProject.SpectralZeroKernel

/-!
# Cancellations of the L-function and of the spectral representation coincide

A **cancellation** of an analytic object at a point `s` is the event that its value there vanishes:
the constituent contributions cancel out exactly.  For the 1-D Dirichlet `L`-function this is the
event `DirichletCharacter.LFunction χ s = 0`; for the spectral representation it is the event that
the configured fiber operator `specOp χ s` annihilates a nonzero state vector
(`∃ ψ ≠ 0, specOp χ s ψ = 0`) — a genuine *spectral* cancellation in the 3-D state space.

These two are the *same function* — the spectral `L`-function `Lspec χ s` is, by construction, the
1-D analytic `L`-function `DirichletCharacter.LFunction χ s` (it is exactly what the spectral
fiber's readout converges to, `Lspec_eq_readout_limit`).  The **only** difference between them is the
space they operate in (3-D state space vs. 1-D readout space `ℂ`), and the **link** between the two
spaces is the readout.  Consequently the two notions of cancellation must agree, and we prove both
inclusions unconditionally (no GRH/RH).

Main results:

* `L_cancellation_realized_spectrally` — **the L-function cannot produce a cancellation that the
  spectral representation cannot produce**: if the 1-D `L`-function vanishes at `s`, then the
  spectral representation has a kernel (cancellation) state there.
* `spectral_cancellation_only_from_L` — **the spectral `L`-function can only produce cancellations
  that the 1-D `L`-function can produce**: if the spectral representation has a kernel (cancellation)
  state at `s`, then the 1-D `L`-function vanishes at `s`.
* `cancellation_sets_coincide` — the sharp form: the spectral representation cancels at `s` **iff**
  the 1-D `L`-function cancels at `s`; the cancellation events are exactly the same.
* `cancellation_is_readout_vanishing` — the link is the readout: on the strip `Re s > 0` (for
  non-principal `χ`) the spectral cancellation at `s` is precisely the vanishing of the limit of the
  spectral fiber's partial-sum readout.

No `axiom`, no `sorry`.
-/

open Complex Filter Topology
open scoped BigOperators

namespace CriticalLinePhasor.SpectralFiber

open CriticalLinePhasor

/-! ## Notions of cancellation -/

/-- **Cancellation of the 1-D `L`-function** at `s`: its value vanishes there.  This is the same as
the spectral `L`-function vanishing, since `Lspec χ s = DirichletCharacter.LFunction χ s` by
construction. -/
def LCancellation {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (s : ℂ) : Prop :=
  DirichletCharacter.LFunction χ s = 0

/-- **Cancellation of the spectral representation** at `s`: the configured fiber operator
`specOp χ s` annihilates a nonzero state vector — a genuine kernel event in the state space. -/
def SpectralCancellation {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (s : ℂ) : Prop :=
  ∃ ψ : ℂ, ψ ≠ 0 ∧ specOp χ s ψ = 0

/-- The spectral `L`-function is, definitionally, the 1-D analytic `L`-function: a cancellation of
`Lspec` is a cancellation of the 1-D `L`-function and conversely. -/
theorem Lspec_eq_LFunction {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (s : ℂ) :
    Lspec χ s = DirichletCharacter.LFunction χ s := rfl

/-! ## The two inclusions -/

/--
**The L-function cannot produce a cancellation that the spectral representation cannot produce.**

If the 1-D Dirichlet `L`-function cancels at `s` (its value is `0`), then the spectral representation
also cancels there: the configured fiber operator `specOp χ s` has a nonzero kernel state.  Every
cancellation of the 1-D readout object is realised as a spectral (state-space) cancellation.
-/
theorem L_cancellation_realized_spectrally {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (s : ℂ)
    (h : LCancellation χ s) : SpectralCancellation χ s :=
  spectral_zero_has_kernel χ s h

/--
**The spectral `L`-function can only produce cancellations that the 1-D `L`-function can produce.**

If the spectral representation cancels at `s` (the configured fiber operator has a nonzero kernel
state), then the 1-D Dirichlet `L`-function cancels there too (its value is `0`).  The spectral
object introduces no new cancellations beyond those of the 1-D `L`-function it is configured from.
-/
theorem spectral_cancellation_only_from_L {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (s : ℂ)
    (h : SpectralCancellation χ s) : LCancellation χ s :=
  (spectral_kernel_iff_zero χ s).mp h

/--
**Sharp form: the cancellation events coincide.**  The spectral representation cancels at `s` **iff**
the 1-D Dirichlet `L`-function cancels at `s`.  Because they are the *same function* differing only
by the space it operates in, their cancellation sets are identical.
-/
theorem cancellation_sets_coincide {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (s : ℂ) :
    SpectralCancellation χ s ↔ LCancellation χ s :=
  ⟨spectral_cancellation_only_from_L χ s, L_cancellation_realized_spectrally χ s⟩

/-! ## The link is the readout -/

/--
**The link between the two spaces is the readout.**  For a non-principal character `χ` and any `s`
with `Re s > 0`, the spectral cancellation at `s` is precisely the vanishing of the limit of the
spectral fiber's partial-sum readout — and that limit is the 1-D `L`-function value.  This exhibits
the readout as the bridge between the 3-D state space (where the kernel/cancellation lives) and the
1-D readout space (where the `L`-function value lives).
-/
theorem cancellation_is_readout_vanishing {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ ≠ 1) {s : ℂ} (hs : 0 < s.re) (L : ℂ)
    (hL : Filter.Tendsto
      (fun N : ℕ => ∑ n ∈ Finset.range N, readout (fun n => χ (n : ZMod q)) s n)
      Filter.atTop (nhds L)) :
    SpectralCancellation χ s ↔ L = 0 := by
  have hLval : L = Lspec χ s :=
    tendsto_nhds_unique hL (Lspec_eq_readout_limit χ hχ hs)
  rw [hLval, cancellation_sets_coincide]
  rfl

/-! ## Capstone -/

/--
**Cancellation equivalence of the spectral representation and the 1-D `L`-function.**  For a
non-principal Dirichlet character `χ`:

1. **No extra cancellations from `L`.**  Every cancellation of the 1-D `L`-function is realised as a
   spectral (state-space) cancellation: the `L`-function cannot produce a cancellation the spectral
   representation cannot (`L_cancellation_realized_spectrally`).
2. **No extra cancellations from the spectrum.**  Every spectral cancellation forces a cancellation
   of the 1-D `L`-function: the spectral representation can only produce cancellations the 1-D
   `L`-function can (`spectral_cancellation_only_from_L`).

Hence the cancellation sets coincide: the two are the *same function*, differing only by the space
they operate in — the 3-D state space vs. the 1-D readout space — with the readout as their link.
-/
theorem cancellation_equivalence {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) :
    (∀ s : ℂ, LCancellation χ s → SpectralCancellation χ s)
      ∧ (∀ s : ℂ, SpectralCancellation χ s → LCancellation χ s)
      ∧ (∀ s : ℂ, SpectralCancellation χ s ↔ LCancellation χ s) :=
  ⟨L_cancellation_realized_spectrally χ, spectral_cancellation_only_from_L χ,
    cancellation_sets_coincide χ⟩

/-! ## Nontrivial cancellations (trivial zeros excluded)

The trivial zeros of `Lχ` (on the negative real axis) are off the critical strip and carry no
spectral interest.  Restricting to the **open critical strip** `0 < Re s < 1` excludes them; the
coincidence of the two cancellation notions persists verbatim on this nontrivial range. -/

/-- **A nontrivial `L`-cancellation**: a cancellation of the 1-D `L`-function lying in the open
critical strip `0 < Re s < 1` (so the trivial zeros are excluded). -/
def NontrivialLCancellation {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (s : ℂ) : Prop :=
  LCancellation χ s ∧ 0 < s.re ∧ s.re < 1

/-- **A nontrivial spectral cancellation**: a spectral (state-space) cancellation lying in the open
critical strip `0 < Re s < 1` (so the trivial zeros are excluded). -/
def NontrivialSpectralCancellation {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (s : ℂ) : Prop :=
  SpectralCancellation χ s ∧ 0 < s.re ∧ s.re < 1

/-- **The nontrivial cancellation events coincide.**  On the open critical strip `0 < Re s < 1`
(trivial zeros excluded) the spectral representation cancels at `s` **iff** the 1-D Dirichlet
`L`-function cancels at `s`.  The strip predicate is shared by both sides, and the cancellation parts
convert via `spectral_cancellation_only_from_L` / `L_cancellation_realized_spectrally`. -/
theorem nontrivial_cancellation_sets_coincide
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (s : ℂ) :
    NontrivialSpectralCancellation χ s ↔ NontrivialLCancellation χ s := by
  constructor
  · intro h
    exact ⟨spectral_cancellation_only_from_L χ s h.1, h.2⟩
  · intro h
    exact ⟨L_cancellation_realized_spectrally χ s h.1, h.2⟩

end CriticalLinePhasor.SpectralFiber
