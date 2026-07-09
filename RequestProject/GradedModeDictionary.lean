import RequestProject.ResidueJump
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.Trace.Basic

/-!
# The graded mode dictionary: local algebras realize the multiplicity ledger

Stage 1 of the unconditional Hilbert–Pólya program.  `ResidueJump` proved the windowed
spectral trace `Tr h(D_T) = Σ_γ m_γ·h(γ)` with the operator realized as a **diagonal
matrix by fiat** on the window index; its audited frontier named the gap: *the mode
dictionary is event-level — no `m_ρ`-graded eigenspace is exhibited.*  This file
discharges that arrow.

**The construction is derived, not defined** (the house anti-tautology rule):

* the event's divisor exponent is `eventOrder γ = analyticOrderNatAt ζ (½+iγ)` — ζ's own
  analytic vanishing order, the same quantity the ledger reads as the jump `ΔS_mult` and
  the chart reads as the log-derivative residue (`residue_eq_Smult_jump`);
* the **mode space** is the local algebra `ℂ[X]/((X−ρ_γ)^{m_γ})` — the canonical quotient
  by the event's divisor ideal.  By the analytic factorization `ζ = (z−ρ)^m·u` (`u(ρ)≠0`,
  the same factorization `logDeriv_residue_eq_order` consumes), this polynomial quotient
  is the standard local model of the germ algebra `O_ρ/(ζ)`;
* the **mode operator** is multiplication by the coordinate — nothing is inserted: the
  algebra multiplies, we watch.

Everything follows from one structural fact: the local algebra has a **unique ℂ-point**
(`residueChar`, evaluation at the event), and every element splits as residue value plus
nilpotent (`sub_residueChar_isNilpotent`).  Hence the **master trace lemma**
`Algebra.trace x = m_γ · residueChar x` (`trace_eq_residueChar`), and as corollaries:

* `finrank ℂ (ModeSpace γ) = eventOrder γ` — the graded dictionary equation: eigenspace
  dimension = ledger jump = residue (uniform over events and non-events);
* `trace (coordinate) = m_γ·ρ_γ`, and for every polynomial observable `h`,
  `trace h(D_γ) = m_γ·h(ρ_γ)` (`trace_aeval`);
* the **height element** `−i(x − ½)` has trace `m_γ·γ` — the ordinate readout;
* off the event the shifted height is a **unit** of the local algebra and
  `trace (D_γ − w)⁻¹ = m_γ·(γ − w)⁻¹` (`trace_heightResolvent`);
* summed over the window, the graded traces equal `windowedTrace`
  (`gradedWindowTrace_eq_windowedTrace`) and the graded resolvent equals
  `windowedResolventTrace` (`gradedResolventTrace_eq_windowedResolventTrace`), hence — by
  `windowedTrace_eq_residue_sum` — **operator traces on genuine m-dimensional local
  algebras = the S_mult jump ledger = the log-derivative residue sum**:

      zero order = source event weight = spectral multiplicity.

Scope: unconditional; no RH/GRH is assumed or proved.  Each mode space's spectral
parameter is the event's line point; nothing here asserts where zeros lie — the file
turns the ledger into an operator dictionary, multiplicity included.  No `sorry`, no
`axiom` beyond the standard three.
-/

open Complex Polynomial CriticalLinePhasor.ResidueJump CriticalLinePhasor.CarrierScale

namespace CriticalLinePhasor.GradedModes

/-! ## §1 The event divisor polynomial -/

/-- The local divisor polynomial of the event at ordinate `γ`: `(X − ρ_γ)^{m_γ}`, with the
exponent **derived** from ζ (`eventOrder γ = analyticOrderNatAt ζ (line γ)`). -/
noncomputable def divisorPoly (γ : ℝ) : Polynomial ℂ :=
  (X - C (line γ)) ^ eventOrder γ

theorem divisorPoly_monic (γ : ℝ) : (divisorPoly γ).Monic :=
  (monic_X_sub_C (line γ)).pow _

theorem divisorPoly_ne_zero (γ : ℝ) : divisorPoly γ ≠ 0 :=
  (divisorPoly_monic γ).ne_zero

theorem divisorPoly_natDegree (γ : ℝ) : (divisorPoly γ).natDegree = eventOrder γ := by
  rw [divisorPoly, natDegree_pow, natDegree_X_sub_C, mul_one]

/-- At an event (`m ≥ 1`) the divisor polynomial vanishes at the event point. -/
theorem divisorPoly_eval_self {γ : ℝ} (hm : 0 < eventOrder γ) :
    (divisorPoly γ).eval (line γ) = 0 := by
  rw [divisorPoly, eval_pow, eval_sub, eval_X, eval_C, sub_self, zero_pow hm.ne']

/-! ## §2 The mode space and the graded dictionary equation -/

/-- **The mode space**: the local algebra `ℂ[X]/((X−ρ_γ)^{m_γ})` of the event divisor —
the canonical polynomial model of the germ algebra `O_{ρ_γ}/(ζ)`. -/
abbrev ModeSpace (γ : ℝ) : Type := AdjoinRoot (divisorPoly γ)

/-- The coordinate class in the mode space. -/
noncomputable def modeCoord (γ : ℝ) : ModeSpace γ := AdjoinRoot.root (divisorPoly γ)

/-- The power basis of the mode space (dimension = degree of the divisor). -/
noncomputable def modeBasis (γ : ℝ) : PowerBasis ℂ (ModeSpace γ) :=
  AdjoinRoot.powerBasis (divisorPoly_ne_zero γ)

instance (γ : ℝ) : Module.Finite ℂ (ModeSpace γ) :=
  Module.Finite.of_basis (modeBasis γ).basis

instance (γ : ℝ) : Module.Free ℂ (ModeSpace γ) :=
  Module.Free.of_basis (modeBasis γ).basis

/-- **The graded dictionary equation**: the mode space's dimension *is* the event's
multiplicity — eigenspace dimension = `eventOrder` = jump of `S_mult` = residue.  Uniform:
at a non-event the divisor is the unit ideal and the mode space is trivial (dimension 0). -/
theorem finrank_modeSpace (γ : ℝ) :
    Module.finrank ℂ (ModeSpace γ) = eventOrder γ := by
  rw [(modeBasis γ).finrank, modeBasis, AdjoinRoot.powerBasis_dim, divisorPoly_natDegree]

/-- Events carry nontrivial mode spaces. -/
theorem modeSpace_nontrivial {γ : ℝ} (hm : 0 < eventOrder γ) :
    Nontrivial (ModeSpace γ) := by
  have h := finrank_modeSpace γ
  refine Module.nontrivial_of_finrank_pos (R := ℂ) ?_
  omega

/-! ## §3 The residue character and the master trace lemma -/

/-- **The residue character**: the unique ℂ-point of the local algebra — evaluation at the
event point.  Exists exactly at events (the divisor must vanish where we evaluate). -/
noncomputable def residueChar {γ : ℝ} (hm : 0 < eventOrder γ) : ModeSpace γ →+* ℂ :=
  AdjoinRoot.lift (RingHom.id ℂ) (line γ)
    (by rw [eval₂_id]; exact divisorPoly_eval_self hm)

@[simp] theorem residueChar_mk {γ : ℝ} (hm : 0 < eventOrder γ) (p : Polynomial ℂ) :
    residueChar hm (AdjoinRoot.mk (divisorPoly γ) p) = p.eval (line γ) := by
  rw [residueChar, AdjoinRoot.lift_mk, eval₂_id]

@[simp] theorem residueChar_coord {γ : ℝ} (hm : 0 < eventOrder γ) :
    residueChar hm (modeCoord γ) = line γ :=
  AdjoinRoot.lift_root _

@[simp] theorem residueChar_algebraMap {γ : ℝ} (hm : 0 < eventOrder γ) (c : ℂ) :
    residueChar hm (algebraMap ℂ (ModeSpace γ) c) = c := by
  rw [AdjoinRoot.algebraMap_eq]
  exact AdjoinRoot.lift_of _

/-- The shifted coordinate is nilpotent: `(x − ρ)^m` is the divisor class, i.e. `0`. -/
theorem shiftedCoord_isNilpotent (γ : ℝ) :
    IsNilpotent (modeCoord γ - algebraMap ℂ (ModeSpace γ) (line γ)) := by
  refine ⟨eventOrder γ, ?_⟩
  have hx : modeCoord γ - algebraMap ℂ (ModeSpace γ) (line γ)
      = AdjoinRoot.mk (divisorPoly γ) (X - C (line γ)) := by
    rw [modeCoord, AdjoinRoot.algebraMap_eq, map_sub, AdjoinRoot.mk_X]
    rfl
  rw [hx, ← map_pow, ← divisorPoly, AdjoinRoot.mk_self]

/-- **The kernel splitting**: every element of the local algebra is its residue value plus
a nilpotent — the algebra is local with residue field ℂ. -/
theorem sub_residueChar_isNilpotent {γ : ℝ} (hm : 0 < eventOrder γ) (x : ModeSpace γ) :
    IsNilpotent (x - algebraMap ℂ (ModeSpace γ) (residueChar hm x)) := by
  obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective x
  obtain ⟨q, hq⟩ := X_sub_C_dvd_sub_C_eval (a := line γ) (p := p)
  have hsplit : AdjoinRoot.mk (divisorPoly γ) p
      - algebraMap ℂ (ModeSpace γ) (p.eval (line γ))
      = (modeCoord γ - algebraMap ℂ (ModeSpace γ) (line γ))
        * AdjoinRoot.mk (divisorPoly γ) q := by
    have hx : modeCoord γ - algebraMap ℂ (ModeSpace γ) (line γ)
        = AdjoinRoot.mk (divisorPoly γ) (X - C (line γ)) := by
      rw [modeCoord, AdjoinRoot.algebraMap_eq, map_sub, AdjoinRoot.mk_X]
      rfl
    rw [hx, ← map_mul, ← hq, AdjoinRoot.algebraMap_eq]
    show _ = AdjoinRoot.mk (divisorPoly γ) (p - C (p.eval (line γ)))
    rw [map_sub]
    rfl
  rw [residueChar_mk hm p, hsplit]
  exact (Commute.all _ _).isNilpotent_mul_right (shiftedCoord_isNilpotent γ)

/-- Multiplication by a nilpotent element is a nilpotent endomorphism, so its trace
vanishes (ℂ is reduced). -/
theorem trace_lmul_nilpotent {γ : ℝ} {n : ModeSpace γ} (hn : IsNilpotent n) :
    Algebra.trace ℂ (ModeSpace γ) n = 0 := by
  have hend : IsNilpotent (Algebra.lmul ℂ (ModeSpace γ) n) := hn.map _
  have htr : IsNilpotent (LinearMap.trace ℂ (ModeSpace γ)
      (Algebra.lmul ℂ (ModeSpace γ) n)) :=
    LinearMap.isNilpotent_trace_of_isNilpotent hend
  simpa [Algebra.trace_apply] using htr.eq_zero

/-- **The master trace lemma**: on the event's local algebra, the trace of multiplication
by any element is the multiplicity times its residue value —

    `Tr (x·) = m_γ · residueChar x`.

Every spectral statement of the dictionary is a corollary of this one line. -/
theorem trace_eq_residueChar {γ : ℝ} (hm : 0 < eventOrder γ) (x : ModeSpace γ) :
    Algebra.trace ℂ (ModeSpace γ) x = (eventOrder γ : ℂ) * residueChar hm x := by
  have hsplit := sub_residueChar_isNilpotent hm x
  have h0 : Algebra.trace ℂ (ModeSpace γ)
      (x - algebraMap ℂ (ModeSpace γ) (residueChar hm x)) = 0 :=
    trace_lmul_nilpotent hsplit
  have halg : Algebra.trace ℂ (ModeSpace γ)
      (algebraMap ℂ (ModeSpace γ) (residueChar hm x))
      = (Module.finrank ℂ (ModeSpace γ) : ℂ) * residueChar hm x := by
    rw [Algebra.trace_algebraMap, nsmul_eq_mul]
  have hsub : Algebra.trace ℂ (ModeSpace γ) x
      - Algebra.trace ℂ (ModeSpace γ) (algebraMap ℂ (ModeSpace γ) (residueChar hm x)) = 0 := by
    rw [← map_sub]
    exact h0
  rw [sub_eq_zero] at hsub
  rw [hsub, halg, finrank_modeSpace]

/-! ## §4 Spectral corollaries: coordinate, observables, height, resolvent -/

/-- The coordinate's trace: `Tr (x·) = m_γ·ρ_γ`. -/
theorem trace_modeCoord {γ : ℝ} (hm : 0 < eventOrder γ) :
    Algebra.trace ℂ (ModeSpace γ) (modeCoord γ) = (eventOrder γ : ℂ) * line γ := by
  rw [trace_eq_residueChar hm, residueChar_coord]

/-- **Polynomial observables**: `Tr h(x·) = m_γ·h(ρ_γ)` for every polynomial `h` — the
graded functional calculus of the mode space. -/
theorem trace_aeval {γ : ℝ} (hm : 0 < eventOrder γ) (h : Polynomial ℂ) :
    Algebra.trace ℂ (ModeSpace γ) (aeval (modeCoord γ) h)
      = (eventOrder γ : ℂ) * h.eval (line γ) := by
  rw [trace_eq_residueChar hm]
  congr 1
  rw [modeCoord, AdjoinRoot.aeval_eq, residueChar_mk]

/-- **The height element**: `−i·(x − ½)`, whose residue value is the real ordinate `γ` —
the native "height coordinate" observable of the event. -/
noncomputable def heightElt (γ : ℝ) : ModeSpace γ :=
  algebraMap ℂ (ModeSpace γ) (-I)
    * (modeCoord γ - algebraMap ℂ (ModeSpace γ) (1 / 2 : ℂ))

@[simp] theorem residueChar_heightElt {γ : ℝ} (hm : 0 < eventOrder γ) :
    residueChar hm (heightElt γ) = (γ : ℂ) := by
  rw [heightElt, map_mul, map_sub, residueChar_coord, residueChar_algebraMap,
    residueChar_algebraMap]
  rw [line, lineC]
  ring_nf
  rw [Complex.I_sq]
  ring

/-- The height readout: `Tr (height·) = m_γ·γ` — multiplicity times the **real ordinate**. -/
theorem trace_heightElt {γ : ℝ} (hm : 0 < eventOrder γ) :
    Algebra.trace ℂ (ModeSpace γ) (heightElt γ) = (eventOrder γ : ℂ) * (γ : ℂ) := by
  rw [trace_eq_residueChar hm, residueChar_heightElt]

/-- Elements with nonzero residue value are units of the local algebra. -/
theorem isUnit_of_residueChar_ne_zero {γ : ℝ} (hm : 0 < eventOrder γ)
    {x : ModeSpace γ} (hx : residueChar hm x ≠ 0) : IsUnit x := by
  set c := residueChar hm x with hc
  have hsplit := sub_residueChar_isNilpotent hm x
  have hxeq : x = algebraMap ℂ (ModeSpace γ) c
      * (1 + algebraMap ℂ (ModeSpace γ) c⁻¹
        * (x - algebraMap ℂ (ModeSpace γ) c)) := by
    rw [mul_add, mul_one, ← mul_assoc, ← map_mul, mul_inv_cancel₀ hx, map_one, one_mul]
    ring
  rw [hxeq]
  refine IsUnit.mul ?_ ?_
  · exact (isUnit_iff_ne_zero.mpr hx).map (algebraMap ℂ (ModeSpace γ))
  · exact ((Commute.all _ _).isNilpotent_mul_left hsplit).isUnit_one_add

/-- The residue character inverts `Ring.inverse` on units. -/
theorem residueChar_ringInverse {γ : ℝ} (hm : 0 < eventOrder γ)
    {x : ModeSpace γ} (hx : IsUnit x) :
    residueChar hm (Ring.inverse x) = (residueChar hm x)⁻¹ := by
  have h1 : x * Ring.inverse x = 1 := Ring.mul_inverse_cancel x hx
  have h2 := congrArg (residueChar hm) h1
  rw [map_mul, map_one] at h2
  exact eq_inv_of_mul_eq_one_left (by rw [mul_comm]; exact h2)

/-- **The graded resolvent trace at one event**: for `w` off the ordinate, the shifted
height is a unit of the local algebra and

    `Tr (height − w)⁻¹ = m_γ · (γ − w)⁻¹`

— the resolvent of the event's mode block, with the ordinate as spectral parameter and
the multiplicity as weight. -/
theorem trace_heightResolvent {γ : ℝ} (hm : 0 < eventOrder γ) {w : ℂ}
    (hw : w ≠ (γ : ℂ)) :
    Algebra.trace ℂ (ModeSpace γ)
      (Ring.inverse (heightElt γ - algebraMap ℂ (ModeSpace γ) w))
      = (eventOrder γ : ℂ) * ((γ : ℂ) - w)⁻¹ := by
  have hres : residueChar hm (heightElt γ - algebraMap ℂ (ModeSpace γ) w)
      = (γ : ℂ) - w := by
    rw [map_sub, residueChar_heightElt, residueChar_algebraMap]
  have hne : residueChar hm (heightElt γ - algebraMap ℂ (ModeSpace γ) w) ≠ 0 := by
    rw [hres]
    exact sub_ne_zero.mpr (fun h => hw h.symm)
  have hunit := isUnit_of_residueChar_ne_zero hm hne
  rw [trace_eq_residueChar hm, residueChar_ringInverse hm hunit, hres]

/-! ## §5 Window assembly: graded traces = the ledger -/

/-- Every window member is a genuine event: positive multiplicity. -/
theorem eventWindow_order_pos {T γ : ℝ} (hγ : γ ∈ eventWindow T) :
    0 < eventOrder γ := by
  have hmem := (events_finite T).mem_toFinset.mp hγ
  rcases Nat.eq_zero_or_pos (eventOrder γ) with h0 | hpos
  · exact absurd hmem.2 ((eventOrder_eq_zero_iff γ).mp h0)
  · exact hpos

/-- **The graded window trace**: the sum of the local-algebra traces of the observable
`h(x)` over the window's events — `Tr h(D_T)` on the genuine graded modes. -/
noncomputable def gradedWindowTrace (h : Polynomial ℂ) (T : ℝ) : ℂ :=
  ∑ γ ∈ eventWindow T, Algebra.trace ℂ (ModeSpace γ) (aeval (modeCoord γ) h)

/-- **Graded modes read the ledger**: the graded window trace equals the windowed spectral
trace of `ResidueJump` — the fiat-diagonal is replaced by genuine `m`-dimensional local
algebras, and nothing changes: dimension = multiplicity = jump = residue. -/
theorem gradedWindowTrace_eq_windowedTrace (h : Polynomial ℂ) (T : ℝ) :
    gradedWindowTrace h T = windowedTrace (fun t => h.eval (line t)) T := by
  unfold gradedWindowTrace windowedTrace
  exact Finset.sum_congr rfl fun γ hγ =>
    trace_aeval (eventWindow_order_pos hγ) h

/-- **The graded resolvent trace** over the window. -/
noncomputable def gradedResolventTrace (w : ℂ) (T : ℝ) : ℂ :=
  ∑ γ ∈ eventWindow T, Algebra.trace ℂ (ModeSpace γ)
    (Ring.inverse (heightElt γ - algebraMap ℂ (ModeSpace γ) w))

/-- **The graded resolvent is the windowed resolvent trace**: for `w` off the window's
ordinates,

    `Σ_γ Tr (height_γ − w)⁻¹ = Tr (D_T − w)⁻¹ = Σ_γ m_γ·(γ−w)⁻¹`

— the resolvent realized block-by-block on the `m_γ`-dimensional mode spaces. -/
theorem gradedResolventTrace_eq_windowedResolventTrace (w : ℂ) (T : ℝ)
    (hw : ∀ γ ∈ eventWindow T, w ≠ (γ : ℂ)) :
    gradedResolventTrace w T = windowedResolventTrace w T := by
  unfold gradedResolventTrace windowedResolventTrace windowedTrace
  exact Finset.sum_congr rfl fun γ hγ =>
    trace_heightResolvent (eventWindow_order_pos hγ) (hw γ hγ)

/-- **The chain, closed**: graded local-algebra resolvent = ledger resolvent = residue
sum.  Composing with `windowedResolventTrace_eq_residue_sum`: for any residue assignment
`r` of `ζ′/ζ` at the window's events,

    `gradedResolventTrace w T = Σ_γ r γ · (γ − w)⁻¹`

— the operator resolvent on genuine graded modes *is* the log-derivative residue sum:
zero order = source event weight = spectral multiplicity. -/
theorem gradedResolventTrace_eq_residue_sum (w : ℂ) (T : ℝ)
    (hw : ∀ γ ∈ eventWindow T, w ≠ (γ : ℂ)) (r : ℝ → ℂ)
    (hr : ∀ γ ∈ eventWindow T,
      Filter.Tendsto (fun s => (s - line γ) * logDeriv riemannZeta s)
        (nhdsWithin (line γ) {(line γ)}ᶜ) (nhds (r γ))) :
    gradedResolventTrace w T = ∑ γ ∈ eventWindow T, r γ * ((γ : ℂ) - w)⁻¹ := by
  rw [gradedResolventTrace_eq_windowedResolventTrace w T hw]
  exact windowedResolventTrace_eq_residue_sum w T r hr

end CriticalLinePhasor.GradedModes
