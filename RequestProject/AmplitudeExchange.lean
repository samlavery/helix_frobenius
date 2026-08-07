import RequestProject.RankUniformReduction
import RequestProject.LatticeStandingWave

/-!
# The amplitude exchange: the wall as a type, and its first gated rung

The rank-uniform reduction leaves ONE input per rung: the standing wave of a
cancellation-gated amplitude.  This file types that wall and inhabits its gate half on
the first genuine arithmetic amplitude.

* `ExchangedRung` — **the wall, typed**: a rung carrying the cancellation gate together
  with its standing wave; `ExchangedRung.fe` runs the compiled reduction, so inhabiting
  this structure at a profile IS that profile's functional equation on the strip.
* `sum_range_zmod` / `chiSeq_window_sum` / `chiSeq_primitive_bound` — the partial sums
  of a nontrivial Dirichlet character are bounded by its modulus: full windows vanish
  exactly (the period sum is zero), the remainder is at most `q` terms of norm at most
  one.  **Genuine sub-axis cancellation, compiled** — exponent `0 < κ/2`.
* `chiGate` — the character amplitude carries `TransferGate` at weight `1` with
  exponent `0`: the first non-degenerate inhabitant of the gate.
* `differentiableAt_GammaR` / `GammaR_schwarz` — the real chart factor `Γℝ(s+δ)` is
  analytic on the gate's strip and Schwarz-real.
* `chiRung` — **the first cancellation-gated arithmetic rung**: coefficients `χ`,
  gate `chiGate`, chart factor `Γℝ(s+δ)`, arbitrary root-number datum.
* `chi_fe_of_standingWave` — the pipeline applied: the χ-rung's standing wave yields
  Dirichlet's completed functional equation shape on the strip `0 < Re s < 1`.

Register: the remaining input for the χ-rung is its standing wave, whose geometric
source is the weighted strand transformation law at rational shifts (the compiled odd
Hurwitz pair) — the `GL(1)` prototype of the amplitude exchange.  The `Sym^r` rungs
above it need the same two ingredients at their own weights; their gates are the
classical square-root-cancellation inputs, cited not compiled.  No `axiom`, no `sorry`.
-/

open Finset Complex ComplexConjugate

namespace CriticalLinePhasor.AmplitudeExchange

open TransferContinuation CriticalLinePhasor.GateInterface
open CriticalLinePhasor.RankUniformReduction
open CriticalLinePhasor.LatticeStandingWave

/-! ## The wall, typed -/

variable {κ : ℝ}

/-- **The amplitude exchange, typed**: a cancellation-gated rung together with its
standing wave.  Inhabiting this structure at a given arithmetic profile is exactly the
campaign's per-rung wall; the functional equation follows by the compiled reduction. -/
structure ExchangedRung (κ : ℝ) where
  rung : RungData κ
  wave : rung.standingWave

/-- Running the compiled reduction: an exchanged rung carries its functional equation
on the gate's strip. -/
theorem ExchangedRung.fe (E : ExchangedRung κ) :
    ∀ s ∈ transferStrip E.rung.gate.θ κ,
      E.rung.gamma ((κ : ℂ) - s) * abelContinuation E.rung.a ((κ : ℂ) - s) =
        E.rung.eps * (E.rung.gamma s *
          abelContinuation (fun n => conj (E.rung.a n)) s) :=
  E.rung.fe_of_standingWave E.wave

/-! ## The character amplitude and its gate -/

/-- A range-`q` sum over cast representatives is a `ZMod q` sum. -/
theorem sum_range_zmod {q : ℕ} [NeZero q] (g : ZMod q → ℂ) :
    ∑ k ∈ Finset.range q, g (k : ZMod q) = ∑ a : ZMod q, g a := by
  refine Finset.sum_nbij' (fun k => (k : ZMod q)) (fun a => a.val)
    ?_ ?_ ?_ ?_ ?_
  · intro k _
    exact Finset.mem_univ _
  · intro a _
    exact Finset.mem_range.mpr (ZMod.val_lt a)
  · intro k hk
    exact ZMod.val_cast_of_lt (Finset.mem_range.mp hk)
  · intro a _
    exact ZMod.natCast_rightInverse a
  · intro k _
    rfl

/-- The coefficients of a Dirichlet character, read on the carrier: the amplitude at
index `n` sits at height `n+1`, so the induced Dirichlet series is `L(s, χ)`. -/
noncomputable def chiSeq {q : ℕ} (χ : DirichletCharacter ℂ q) : ℕ → ℂ :=
  fun n => χ ((n + 1 : ℕ) : ZMod q)

/-- Every window of `q` consecutive coefficients of a nontrivial character sums to
zero, exactly. -/
theorem chiSeq_window_sum {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ ≠ 1) (m : ℕ) :
    ∑ k ∈ Finset.range q, chiSeq χ (m + k) = 0 := by
  have hcast : ∀ k : ℕ,
      chiSeq χ (m + k) = χ (((m + 1 : ℕ) : ZMod q) + (k : ZMod q)) := by
    intro k
    unfold chiSeq
    push_cast
    ring_nf
  rw [Finset.sum_congr rfl fun k _ => hcast k,
    sum_range_zmod (fun a => χ (((m + 1 : ℕ) : ZMod q) + a))]
  exact (Equiv.sum_comp (Equiv.addLeft ((m + 1 : ℕ) : ZMod q)) (fun a => χ a)).trans
    (MulChar.sum_eq_zero_of_ne_one hχ)

/-- **The primitive bound of a nontrivial character**: every partial sum is bounded by
the modulus — full windows vanish, the remainder has at most `q` unit terms. -/
theorem chiSeq_primitive_bound {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ ≠ 1) (n : ℕ) :
    ‖∑ k ∈ Finset.range n, chiSeq χ k‖ ≤ (q : ℝ) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases lt_or_ge n q with hn | hn
    · calc ‖∑ k ∈ Finset.range n, chiSeq χ k‖
          ≤ ∑ k ∈ Finset.range n, ‖chiSeq χ k‖ := norm_sum_le _ _
        _ ≤ ∑ _k ∈ Finset.range n, (1 : ℝ) := by
            refine Finset.sum_le_sum fun k _ => ?_
            exact DirichletCharacter.norm_le_one χ _
        _ = n := by simp
        _ ≤ (q : ℝ) := by exact_mod_cast hn.le
    · obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
      rw [Finset.sum_range_add]
      have hwin : ∑ k ∈ Finset.range q, chiSeq χ k = 0 := by
        have h := chiSeq_window_sum χ hχ 0
        simpa only [Nat.zero_add] using h
      rw [hwin, zero_add]
      have hshift : ∀ k : ℕ, chiSeq χ (q + k) = chiSeq χ k := by
        intro k
        unfold chiSeq
        push_cast
        simp
      rw [Finset.sum_congr rfl fun k _ => hshift k]
      rcases Nat.eq_zero_or_pos q with hq | hq
      · exact absurd hq (NeZero.ne q)
      · exact ih m (by omega)

/-- **The character gate**: a nontrivial Dirichlet character inhabits the cancellation
gate at weight `1` with exponent `0` — genuine sub-axis cancellation, compiled. -/
noncomputable def chiGate {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ ≠ 1) : TransferGate (chiSeq χ) 1 where
  C := q
  θ := 0
  θ_nonneg := le_refl 0
  θ_lt := by norm_num
  primitive_bound := fun n => by
    rw [Real.rpow_zero, mul_one]
    exact chiSeq_primitive_bound χ hχ n

/-! ## The real chart factor -/

/-- `Γℝ` is analytic at every point of positive real part. -/
theorem differentiableAt_GammaR {w : ℂ} (hw : 0 < w.re) :
    DifferentiableAt ℂ Complex.Gammaℝ w := by
  have hfun : Complex.Gammaℝ = fun z : ℂ =>
      (Real.pi : ℂ) ^ (-z / 2) * Complex.Gamma (z / 2) :=
    funext fun z => Complex.Gammaℝ_def z
  rw [hfun]
  refine DifferentiableAt.mul ?_ ?_
  · refine (differentiableAt_id.neg.div_const (2 : ℂ)).const_cpow ?_
    exact Or.inl (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
  · have hg : DifferentiableAt ℂ Complex.Gamma (w / 2) := by
      refine Complex.differentiableAt_Gamma _ fun m => ?_
      intro hcontra
      have : (w / 2).re = (-(m : ℂ)).re := by rw [hcontra]
      simp only [Complex.div_re, Complex.neg_re, Complex.natCast_re] at this
      have hre : 0 < (w / 2).re := by
        rw [Complex.div_re]
        simp [Complex.normSq]
        positivity
      rw [hcontra] at hre
      simp only [Complex.neg_re, Complex.natCast_re] at hre
      have : (0:ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
      linarith
    exact hg.comp w (differentiableAt_id.div_const 2)

/-- `Γℝ` at a real shift is Schwarz-real. -/
theorem GammaR_schwarz (δ : ℝ) (s : ℂ) :
    conj (Complex.Gammaℝ (conj s + δ)) = Complex.Gammaℝ (s + δ) := by
  rw [Complex.Gammaℝ_def, Complex.Gammaℝ_def, map_mul]
  congr 1
  · rw [show -(conj s + (δ : ℂ)) / 2 = conj (-(s + δ) / 2) by
      rw [map_div₀, map_neg, map_add, Complex.conj_ofReal, map_ofNat]]
    rw [conj_ofReal_cpow Real.pi_pos.le, Complex.conj_conj]
  · rw [show (conj s + (δ : ℂ)) / 2 = conj ((s + δ) / 2) by
      rw [map_div₀, map_add, Complex.conj_ofReal, map_ofNat]]
    rw [Complex.Gamma_conj, Complex.conj_conj]

/-! ## The first cancellation-gated arithmetic rung -/

/-- **The χ-rung**: a nontrivial Dirichlet character with its compiled gate, the real
chart factor `Γℝ(s+δ)`, and a root-number datum — the first non-degenerate inhabitant
of `RungData`. -/
noncomputable def chiRung {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ ≠ 1) (δ : ℝ) (hδ : 0 ≤ δ) (ε : ℂ) : RungData 1 where
  a := chiSeq χ
  gate := chiGate χ hχ
  gamma := fun s => Complex.Gammaℝ (s + δ)
  gamma_differentiableOn := by
    intro s hs
    refine (differentiableAt_GammaR ?_).comp s
      ((differentiableAt_id).add_const _) |>.differentiableWithinAt
    have h1 : (0 : ℝ) < s.re := hs.1
    simp only [id_eq, Complex.add_re, Complex.ofReal_re]
    linarith
  gamma_schwarz := fun s => GammaR_schwarz δ s
  eps := ε

/-- **The pipeline at `GL(1)`**: the χ-rung's standing wave yields the completed
Dirichlet functional-equation shape on the critical strip `0 < Re s < 1`.  The
remaining input is the standing wave itself; its geometric source is the weighted
strand transformation law at the rational shifts of the character. -/
theorem chi_fe_of_standingWave {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ ≠ 1) (δ : ℝ) (hδ : 0 ≤ δ) (ε : ℂ)
    (h : (chiRung χ hχ δ hδ ε).standingWave) :
    ∀ s ∈ transferStrip 0 1,
      Complex.Gammaℝ (((1 : ℝ) : ℂ) - s + δ) *
          abelContinuation (chiSeq χ) (((1 : ℝ) : ℂ) - s) =
        ε * (Complex.Gammaℝ (s + δ) *
          abelContinuation (fun n => conj (chiSeq χ n)) s) := by
  have hfe := (chiRung χ hχ δ hδ ε).fe_of_standingWave h
  intro s hs
  exact hfe s hs

/-! ## The continuation is the Dirichlet L-function -/

theorem chiL_summable {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {s : ℂ}
    (hs : 1 < s.re) :
    LSeriesSummable (fun n : ℕ => χ (n : ZMod q)) s := by
  refine LSeriesSummable_of_le_const_mul_rpow (x := 1) hs ⟨1, fun m _hm => ?_⟩
  rw [show (1 : ℝ) - 1 = 0 by ring, Real.rpow_zero, mul_one]
  exact DirichletCharacter.norm_le_one χ _

theorem abel_eq_L_of_one_lt {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ1 : χ ≠ 1) {z : ℂ} (hz : 1 < z.re) :
    abelContinuation (chiSeq χ) z = DirichletCharacter.LFunction χ z := by
  have hz0 : (0 : ℝ) < z.re := by linarith
  have hA : ∀ n : ℕ, ‖∑ k ∈ Finset.range n, chiSeq χ k‖ ≤ (q : ℝ) * (n : ℝ) ^ (0 : ℝ) := by
    intro n
    rw [Real.rpow_zero, mul_one]
    exact chiSeq_primitive_bound χ hχ1 n
  have h1 : Filter.Tendsto
      (fun N => ∑ n ∈ Finset.range N, chiSeq χ n * ((n + 1 : ℕ) : ℂ) ^ (-z)) Filter.atTop
      (nhds (abelContinuation (chiSeq χ) z)) :=
    tendsto_abelContinuation _ q 0 le_rfl hA z hz0
  have h2 : Filter.Tendsto
      (fun M => ∑ m ∈ Finset.range M, LSeries.term (fun n : ℕ => χ (n : ZMod q)) z m)
      Filter.atTop (nhds (DirichletCharacter.LFunction χ z)) := by
    rw [DirichletCharacter.LFunction_eq_LSeries χ hz]
    exact (chiL_summable χ hz).hasSum.tendsto_sum_nat
  have h2' : Filter.Tendsto
      (fun N => ∑ m ∈ Finset.range (N + 1), LSeries.term (fun n : ℕ => χ (n : ZMod q)) z m)
      Filter.atTop (nhds (DirichletCharacter.LFunction χ z)) :=
    h2.comp (Filter.tendsto_add_atTop_nat 1)
  have heq : ∀ N : ℕ,
      ∑ n ∈ Finset.range N, chiSeq χ n * ((n + 1 : ℕ) : ℂ) ^ (-z)
        = ∑ m ∈ Finset.range (N + 1), LSeries.term (fun n : ℕ => χ (n : ZMod q)) z m := by
    intro N
    rw [Finset.sum_range_succ' (fun m => LSeries.term (fun n : ℕ => χ (n : ZMod q)) z m) N,
      LSeries.term_zero, add_zero]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [LSeries.term_of_ne_zero (Nat.succ_ne_zero n)]
    unfold chiSeq
    rw [Complex.cpow_neg, div_eq_mul_inv]
  exact tendsto_nhds_unique ((Filter.tendsto_congr heq).mp h1) h2'

/-- **The gate's continuation is the entire Dirichlet L-function** on the connected
half-plane `Re s > 0`, by the identity theorem from the convergence region. -/
theorem abelContinuation_eq_LFunction {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ1 : χ ≠ 1) {s : ℂ} (hs : 0 < s.re) :
    abelContinuation (chiSeq χ) s = DirichletCharacter.LFunction χ s := by
  have hopen : IsOpen {z : ℂ | 0 < z.re} :=
    IsOpen.preimage Complex.continuous_re isOpen_Ioi
  have h1 : AnalyticOnNhd ℂ (abelContinuation (chiSeq χ)) {z : ℂ | 0 < z.re} := by
    have hd : DifferentiableOn ℂ (abelContinuation (chiSeq χ)) {z : ℂ | 0 < z.re} :=
      (chiGate χ hχ1).primal_differentiableOn
    exact hd.analyticOnNhd hopen
  have h2 : AnalyticOnNhd ℂ (DirichletCharacter.LFunction χ) {z : ℂ | 0 < z.re} :=
    ((DirichletCharacter.differentiable_LFunction hχ1).differentiableOn).analyticOnNhd hopen
  have hEqOn : Set.EqOn (abelContinuation (chiSeq χ)) (DirichletCharacter.LFunction χ)
      {z : ℂ | 0 < z.re} := by
    refine h1.eqOn_of_preconnected_of_eventuallyEq h2
      ((convex_halfSpace_re_gt 0).isPreconnected)
      (show (2 : ℂ) ∈ {z : ℂ | 0 < z.re} by norm_num [Set.mem_setOf_eq])
      ?_
    have hopen1 : IsOpen {z : ℂ | 1 < z.re} :=
      IsOpen.preimage Complex.continuous_re isOpen_Ioi
    have hmem : {z : ℂ | 1 < z.re} ∈ nhds (2 : ℂ) :=
      hopen1.mem_nhds (by norm_num [Set.mem_setOf_eq])
    filter_upwards [hmem] with z hz
    exact abel_eq_L_of_one_lt χ hχ1 hz
  exact hEqOn hs

/-! ## The conjugate pairing -/

theorem conj_chi_apply {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (a : ZMod q) :
    conj (χ a) = χ⁻¹ a := by
  by_cases h : IsUnit a
  · rw [MulChar.inv_apply_eq_inv']
    have h1 : ‖χ a‖ = 1 := χ.unit_norm_eq_one h.unit
    have h2 : χ a * conj (χ a) = 1 := by
      rw [Complex.mul_conj]
      norm_cast
      rw [Complex.normSq_eq_norm_sq, h1, one_pow]
    exact eq_inv_of_mul_eq_one_right h2
  · rw [χ.map_nonunit h, (χ⁻¹).map_nonunit h, map_zero]

theorem chiSeq_conj {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) :
    (fun n => conj (chiSeq χ n)) = chiSeq χ⁻¹ :=
  funext fun _ => conj_chi_apply χ _

theorem inv_ne_one_of_ne_one {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ1 : χ ≠ 1) : χ⁻¹ ≠ 1 :=
  fun h => hχ1 (inv_eq_one.mp h)

/-! ## Parity and the Gamma chart -/

theorem even_inv_iff {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) :
    (χ⁻¹).Even ↔ χ.Even := by
  unfold DirichletCharacter.Even
  rw [MulChar.inv_apply_eq_inv', inv_eq_one]

theorem gammaFactor_inv {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (s : ℂ) :
    DirichletCharacter.gammaFactor χ⁻¹ s = DirichletCharacter.gammaFactor χ s := by
  by_cases h : χ.Even
  · rw [DirichletCharacter.Even.gammaFactor_def h,
      DirichletCharacter.Even.gammaFactor_def ((even_inv_iff χ).mpr h)]
  · have ho : χ.Odd := (DirichletCharacter.even_or_odd χ).resolve_left h
    have ho' : (χ⁻¹).Odd := by
      unfold DirichletCharacter.Odd at ho ⊢
      rw [MulChar.inv_apply_eq_inv', ho]
      norm_num
    rw [DirichletCharacter.Odd.gammaFactor_def ho,
      DirichletCharacter.Odd.gammaFactor_def ho']

theorem GammaR_ne_zero {w : ℂ} (hw : 0 < w.re) : Complex.Gammaℝ w ≠ 0 := by
  rw [Complex.Gammaℝ_def]
  refine mul_ne_zero ?_ ?_
  · intro hc
    rcases (Complex.cpow_eq_zero_iff _ _).mp hc with ⟨hπ, _⟩
    exact Complex.ofReal_ne_zero.mpr Real.pi_ne_zero hπ
  · refine Complex.Gamma_ne_zero_of_re_pos ?_
    rw [show (w / 2).re = w.re / 2 by
      rw [Complex.div_re]
      simp [Complex.normSq]
      ring]
    positivity

theorem gammaFactor_ne_zero {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {s : ℂ}
    (hs : 0 < s.re) : DirichletCharacter.gammaFactor χ s ≠ 0 := by
  by_cases h : χ.Even
  · rw [DirichletCharacter.Even.gammaFactor_def h]
    exact GammaR_ne_zero hs
  · have ho : χ.Odd := (DirichletCharacter.even_or_odd χ).resolve_left h
    rw [DirichletCharacter.Odd.gammaFactor_def ho]
    refine GammaR_ne_zero ?_
    simp only [Complex.add_re, Complex.one_re]
    linarith

theorem gamma_mul_LFunction {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (_hχ1 : χ ≠ 1) {s : ℂ} (hs : 0 < s.re) :
    DirichletCharacter.gammaFactor χ s * DirichletCharacter.LFunction χ s
      = DirichletCharacter.completedLFunction χ s := by
  rw [DirichletCharacter.LFunction_eq_completed_div_gammaFactor χ s
      (Or.inl (fun h0 => by rw [h0] at hs; simp at hs)),
    mul_comm, div_mul_cancel₀ _ (gammaFactor_ne_zero χ hs)]

theorem conj_natCast_cpow (q : ℕ) (w : ℂ) :
    conj ((q : ℂ) ^ (conj w)) = (q : ℂ) ^ w := by
  rw [show ((q : ℕ) : ℂ) = (((q : ℕ) : ℝ) : ℂ) by push_cast; rfl,
    conj_ofReal_cpow (Nat.cast_nonneg q), Complex.conj_conj]

theorem gammaFactor_schwarz {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (z : ℂ) :
    conj (DirichletCharacter.gammaFactor χ (conj z))
      = DirichletCharacter.gammaFactor χ z := by
  by_cases h : χ.Even
  · rw [DirichletCharacter.Even.gammaFactor_def h,
      DirichletCharacter.Even.gammaFactor_def h]
    have := GammaR_schwarz 0 z
    simpa using this
  · have ho : χ.Odd := (DirichletCharacter.even_or_odd χ).resolve_left h
    rw [DirichletCharacter.Odd.gammaFactor_def ho,
      DirichletCharacter.Odd.gammaFactor_def ho]
    have := GammaR_schwarz 1 z
    simpa using this

/-! ## The conductor-completed rung -/

/-- **The conductor-completed χ-rung**: coefficients `χ`, the compiled cancellation
gate, chart factor `q^{s/2}·γ(χ, s)` — the full completed chart, so the root number is
constant — and root-number datum `(rootNumber χ⁻¹)⁻¹`. -/
noncomputable def chiRungC {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ1 : χ ≠ 1) : RungData 1 where
  a := chiSeq χ
  gate := chiGate χ hχ1
  gamma := fun s => (q : ℂ) ^ (s / 2) * DirichletCharacter.gammaFactor χ s
  gamma_differentiableOn := by
    intro s hs
    have h1 : (0 : ℝ) < s.re := hs.1
    refine DifferentiableAt.differentiableWithinAt ?_
    refine DifferentiableAt.mul ?_ ?_
    · exact (differentiableAt_id.div_const 2).const_cpow
        (Or.inl (Nat.cast_ne_zero.mpr (NeZero.ne q)))
    · by_cases h : χ.Even
      · rw [show DirichletCharacter.gammaFactor χ
            = fun s => Complex.Gammaℝ s from funext fun s =>
              DirichletCharacter.Even.gammaFactor_def h s]
        exact differentiableAt_GammaR h1
      · have ho : χ.Odd := (DirichletCharacter.even_or_odd χ).resolve_left h
        rw [show DirichletCharacter.gammaFactor χ
            = fun s => Complex.Gammaℝ (s + 1) from funext fun s =>
              DirichletCharacter.Odd.gammaFactor_def ho s]
        refine (differentiableAt_GammaR ?_).comp s
          ((differentiableAt_id).add_const _)
        simp only [Complex.add_re, Complex.one_re]
        linarith
  gamma_schwarz := by
    intro z
    rw [map_mul, gammaFactor_schwarz χ z,
      show conj ((q : ℂ) ^ ((conj z) / 2)) = (q : ℂ) ^ (z / 2) by
        rw [show (conj z) / 2 = conj (z / 2) by rw [map_div₀, map_ofNat]]
        exact conj_natCast_cpow q (z / 2)]
  eps := (DirichletCharacter.rootNumber χ⁻¹)⁻¹

/-! ## The standing wave, from the compiled functional equation -/

/-- **The standing wave of the conductor-completed χ-rung** — from Mathlib's completed
functional equation for primitive characters, the compiled Schwarz pairing of the
continuation, and the compiled identifications; the only datum consumed is the
nonvanishing of the root number (the primitive Gauss sum). -/
theorem chiRungC_standingWave {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ1 : χ ≠ 1) (hprim' : DirichletCharacter.IsPrimitive χ⁻¹)
    (hW : DirichletCharacter.rootNumber χ⁻¹ ≠ 0) :
    (chiRungC χ hχ1).standingWave := by
  intro t
  set s : ℂ := (((1 : ℝ) : ℂ)) / 2 + (t : ℂ) * Complex.I with hsdef
  have hsre : s.re = 1 / 2 := by
    rw [hsdef]
    simp
  have hs0 : 0 < s.re := by rw [hsre]; norm_num
  have hs0' : 0 < (1 - s).re := by
    simp only [Complex.sub_re, Complex.one_re, hsre]
    norm_num
  have hconj : conj s = 1 - s := by
    rw [hsdef, map_add, map_mul, Complex.conj_I, map_div₀, Complex.conj_ofReal,
      map_ofNat, Complex.conj_ofReal]
    push_cast
    ring
  -- the completed readout at s
  have hG : (chiRungC χ hχ1).gamma s * abelContinuation ((chiRungC χ hχ1).a) s
      = (q : ℂ) ^ (s / 2) * DirichletCharacter.completedLFunction χ s := by
    show ((q : ℂ) ^ (s / 2) * DirichletCharacter.gammaFactor χ s) *
        abelContinuation (chiSeq χ) s = _
    rw [abelContinuation_eq_LFunction χ hχ1 hs0, mul_assoc,
      gamma_mul_LFunction χ hχ1 hs0]
  -- the conjugated readout at s
  have hGc : conj ((chiRungC χ hχ1).gamma s * abelContinuation ((chiRungC χ hχ1).a) s)
      = DirichletCharacter.rootNumber χ⁻¹ *
        ((q : ℂ) ^ (s / 2) * DirichletCharacter.completedLFunction χ s) := by
    rw [map_mul]
    -- conj γ(s) = γ(conj s)
    have hγ : conj ((chiRungC χ hχ1).gamma s) = (chiRungC χ hχ1).gamma (conj s) := by
      have h := (chiRungC χ hχ1).gamma_schwarz (conj s)
      rw [Complex.conj_conj] at h
      exact h
    -- conj F(s) = L(χ⁻¹, conj s)
    have hF : conj (abelContinuation ((chiRungC χ hχ1).a) s)
        = DirichletCharacter.LFunction χ⁻¹ (conj s) := by
      show conj (abelContinuation (chiSeq χ) s) = _
      have h := abelContinuation_conj (chiSeq χ) (conj s)
      rw [Complex.conj_conj] at h
      rw [show conj (abelContinuation (chiSeq χ) s)
          = abelContinuation (fun n => conj (chiSeq χ n)) (conj s) from by
        rw [h]]
      rw [chiSeq_conj χ]
      exact abelContinuation_eq_LFunction χ⁻¹ (inv_ne_one_of_ne_one hχ1)
        (by rw [hconj]; exact hs0')
    rw [hγ, hF, hconj]
    -- assemble at 1 − s and apply the functional equation for χ⁻¹
    show ((q : ℂ) ^ ((1 - s) / 2) * DirichletCharacter.gammaFactor χ (1 - s)) *
        DirichletCharacter.LFunction χ⁻¹ (1 - s) = _
    rw [← gammaFactor_inv χ (1 - s), mul_assoc,
      gamma_mul_LFunction χ⁻¹ (inv_ne_one_of_ne_one hχ1) hs0',
      DirichletCharacter.IsPrimitive.completedLFunction_one_sub hprim' s, inv_inv]
    rw [show ((q : ℂ) ^ ((1 - s) / 2)) * ((q : ℂ) ^ (s - 1 / 2) *
        DirichletCharacter.rootNumber χ⁻¹ * DirichletCharacter.completedLFunction χ s)
      = ((q : ℂ) ^ ((1 - s) / 2) * (q : ℂ) ^ (s - 1 / 2)) *
        (DirichletCharacter.rootNumber χ⁻¹ *
          DirichletCharacter.completedLFunction χ s) by ring]
    rw [← Complex.cpow_add _ _ (Nat.cast_ne_zero.mpr (NeZero.ne q)),
      show (1 - s) / 2 + (s - 1 / 2) = s / 2 by ring]
    ring
  -- close: G = W⁻¹ · conj G
  show (chiRungC χ hχ1).gamma s * abelContinuation ((chiRungC χ hχ1).a) s
      = (DirichletCharacter.rootNumber χ⁻¹)⁻¹ *
        conj ((chiRungC χ hχ1).gamma s * abelContinuation ((chiRungC χ hχ1).a) s)
  rw [hGc, hG, ← mul_assoc, inv_mul_cancel₀ hW, one_mul]

/-- **The first full inhabitant of the amplitude exchange**: the conductor-completed
χ-rung with its standing wave — gate, chart, and wave all compiled, one datum
(the nonvanishing primitive root number) consumed. -/
noncomputable def chiExchangedRung {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ1 : χ ≠ 1) (hprim' : DirichletCharacter.IsPrimitive χ⁻¹)
    (hW : DirichletCharacter.rootNumber χ⁻¹ ≠ 0) : ExchangedRung 1 where
  rung := chiRungC χ hχ1
  wave := chiRungC_standingWave χ hχ1 hprim' hW

/-- **The functional equation of the Dirichlet rung on the critical strip**, delivered
by the exchange: one application of `ExchangedRung.fe`. -/
theorem chi_fe {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ1 : χ ≠ 1) (hprim' : DirichletCharacter.IsPrimitive χ⁻¹)
    (hW : DirichletCharacter.rootNumber χ⁻¹ ≠ 0) :
    ∀ s ∈ transferStrip (chiGate χ hχ1).θ 1,
      (chiRungC χ hχ1).gamma (((1 : ℝ) : ℂ) - s) *
          abelContinuation (chiSeq χ) (((1 : ℝ) : ℂ) - s) =
        (DirichletCharacter.rootNumber χ⁻¹)⁻¹ *
          ((chiRungC χ hχ1).gamma s *
            abelContinuation (fun n => conj (chiSeq χ n)) s) :=
  (chiExchangedRung χ hχ1 hprim' hW).fe

end CriticalLinePhasor.AmplitudeExchange

#print axioms CriticalLinePhasor.AmplitudeExchange.ExchangedRung.fe
#print axioms CriticalLinePhasor.AmplitudeExchange.chiSeq_window_sum
#print axioms CriticalLinePhasor.AmplitudeExchange.chiSeq_primitive_bound
#print axioms CriticalLinePhasor.AmplitudeExchange.chiGate
#print axioms CriticalLinePhasor.AmplitudeExchange.differentiableAt_GammaR
#print axioms CriticalLinePhasor.AmplitudeExchange.GammaR_schwarz
#print axioms CriticalLinePhasor.AmplitudeExchange.chiRung
#print axioms CriticalLinePhasor.AmplitudeExchange.chi_fe_of_standingWave
#print axioms CriticalLinePhasor.AmplitudeExchange.abelContinuation_eq_LFunction
#print axioms CriticalLinePhasor.AmplitudeExchange.conj_chi_apply
#print axioms CriticalLinePhasor.AmplitudeExchange.chiRungC
#print axioms CriticalLinePhasor.AmplitudeExchange.chiRungC_standingWave
#print axioms CriticalLinePhasor.AmplitudeExchange.chiExchangedRung
#print axioms CriticalLinePhasor.AmplitudeExchange.chi_fe
