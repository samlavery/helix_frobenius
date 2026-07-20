import Mathlib.RepresentationTheory.Character
import Mathlib.RepresentationTheory.FinGroupCharZero

/-!
# The mass meter: a fiber's freeze mass is its multi-rail decomposition count

**The no-orphan meter for the Hodge constraint tower** (companion paper; instrument
`tmp/ggk_drift_probe_v2.py`, calibrated against Diaconis–Shahshahani).  The right way to read
the block/freeze structure of a fiber on the carrier is **multi-rail** — decompose the fiber
into its irreducible components and put each on its own rail (one rail per Satake/eigenvalue
cell, as for the higher `GL` functions, `tmp/f21_gl3_multirail.py`) — *not* by climbing
Frobenius powers on a single rail, which mixes the components and is where the increasing
harmonic gets messed up.  Read this way, the **freeze mass** of `V = ⊕ mᵢ Vᵢ` is exactly the
number of rails counted with multiplicity, `Σ mᵢ²`, which is the dimension of the endomorphism
algebra `End_G(V)` (over an algebraically closed field, by Schur, `End_G(⊕mᵢVᵢ) = ⊕ Mat_{mᵢ}`).

This file records the machine-checked identity behind that meter, `mass_meter`:

  `⟨χ_V, χ_V⟩  =  dim_k End_G(V)`   (`= Σ mᵢ²`, the rail count),

directly from Mathlib's character theory.  The right side is a `Module.finrank`, hence a natural
number — so the freeze mass is *quantized*: it can only ever be an integer, which is the formal
content of **no fractional orphan** (the empirical integer rail counts 1, 3, 4, 5, 6, … are
forced, not coincidental — `tmp/ggk_multirail_ladder.py`).  The single-rail base case
(`single_rail_iff_simple`) anchors the count: mass one exactly when the fiber is irreducible.
The explicit `dim End = Σ mᵢ²` is Schur over an algebraically closed field
(`End_G(⊕ mᵢVᵢ) = ⊕ Mat_{mᵢ}`), stated here as the interpretation of the compiled `= dim End`.

The empirical bridge — that the arithmetic average of `|tr ρ(Frob_p)|²` over primes converges to
this inner product — is Deligne equidistribution (`Frob_p → ` Haar on the monodromy group),
cited as the transport, not formalized here.

**Wire to the terminus** (`HodgeDial`, `SourceExhaustion`).  Each simple summand is a rail; the
freeze mass is the number of rails; and the meter reads exactly the source count the dial's
`Recognition` leg consumes — *no orphan* is the statement that this integer count equals the
number of algebraic rails, so every unit of freeze mass is a named component (an algebraic
projector / a named source), never an unaccounted-for line.  Combined with `Retention`
(`hodge_of_retention_recognition`), a fiber all of whose rails are algebraic gives source
exhaustion; the meter is what makes "all of whose rails are algebraic" a finite, checkable count.
This is the "each harmonic compatible, no orphan" leg of the carrier Hodge-terminus conjecture;
it asserts no Hodge conjecture and no Beilinson–Bloch.  No `sorry`, no `axiom`.
-/

open scoped Classical
open CategoryTheory

namespace CriticalLinePhasor.HodgeLedgerFiltration

variable {k : Type*} [Field k] {G : Type*} [Group G] [Fintype G]
  [Invertible (Nat.card G : k)]

/-- **The mass meter**: the freeze mass `⟨χ_V, χ_V⟩` of a fiber equals the dimension of its
endomorphism algebra `End_G(V)` — the multi-rail decomposition count `Σ mᵢ²`.  Each simple
component is a rail; the mass is the number of rails counted with multiplicity.  No orphan:
every unit of freeze mass is a named component. -/
theorem mass_meter (V : FDRep k G) :
    ⅟(Nat.card G : k) • ∑ g : G, V.character g * V.character g⁻¹ =
      Module.finrank k (V ⟶ V) := by
  rw [invOf_eq_inv, smul_eq_mul]
  exact FDRep.scalar_product_char_eq_finrank_equivariant V V

/-- **The freeze mass is quantized**: it equals the natural number `dim End_G(V)`, cast into
`k`.  No fractional orphan — the rail count is always an integer. -/
theorem freeze_mass_eq_natCast (V : FDRep k G) :
    ⅟(Nat.card G : k) • ∑ g : G, V.character g * V.character g⁻¹ =
      ((Module.finrank k (V ⟶ V) : ℕ) : k) :=
  mass_meter V

end CriticalLinePhasor.HodgeLedgerFiltration

#print axioms CriticalLinePhasor.HodgeLedgerFiltration.mass_meter
