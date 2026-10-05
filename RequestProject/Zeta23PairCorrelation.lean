import Zeta23.Main
import Zeta23.Assembly

/-!
# Beyond band-width one: pair correlation ⇒ proportion `1 − 1/(3λ²)` (ledger R114)

The Zeta23 artifact (anthropics/zeta-23-lean; "More than two thirds of the zeros of the Riemann zeta
function lie on the critical line") certifies `N₀*(T,2T) ≥ (H(λ) − o(1)) N(T,2T)`, `H(λ) = 2 − 1/λ − λ/3`,
from two trace moments of the Gabor-compressed Weil form at band-width `λ ≤ 1`: `tr Ĝ = N(1+o(1))` and
`‖Ĝ‖²_F = (1/λ₁ + λ₁/3) N (1+o(1))` (its [thm:traces]).  The second moment carries the prime-side
off-diagonal term `O₁`, which the artifact bounds by `L²X` (Prop. 5.6) and drops — the step that restricts
it to `λ ≤ 1` (its §7.5(a): "for `X ≫ Tl` the off-diagonal terms `O₁` are no longer dominated by the
diagonal, and their evaluation would require information on prime pairs").

The house measured that term (`PROOF_CAMPAIGN.md` R113; `tmp/zeta23_o1.py`, `tmp/O1_NOTE_lambda.txt`):
`O₁ = −(TL²/6π)(L − l₁)₊³ (1 + o(1))`, i.e. the diagonal weight `L²/3` in [eq:tr2] becomes
`L² · J(λ₁)`, `J(x) = (1 − ((1 − 1/x)₊)³)/3`, and the Frobenius law becomes `1/λ₁ + λ₁ J(λ₁) = 1 + 1/(3λ₁²)`
for `λ₁ ≥ 1`.  Making that main term rigorous is Montgomery's pair-correlation conjecture on Fourier
support `(1, λ]` (artifact, l.1580–83 and Remark 1.1).

This file compiles the payoff of that hypothesis on the artifact's own assembly:

* `PairCorrelationTraces P Err Z` — the artifact's [thm:traces] with the corrected second moment
  (`mainTr2PCC`) in place of `Params.mainTr2`; this is the ONE hypothesis, stated on the prime side
  (`P.trGtilde`, `P.trGtildeSq` are the artifact's prime-side traces computed entrywise).
* `thmA_abstract_err_PCC` — the artifact's `Assembly.thmA_abstract_err` with `λ < 2` in place of `λ < 1`
  and `HPCC(λ) = 2 − cPCC(λ)` in place of `Hfun λ`: under the hypothesis and the artifact's zero-side
  inputs, `N₀*(T,2T) ≥ (HPCC(λ) − ε) N(T,2T)`.
* `HPCC_eq_of_one_le` — `HPCC λ = 1 − 1/(3λ²)` for `λ ≥ 1`.
* `N0star_zeta_of_pairCorrelation` — the ζ-level reading, `λ ∈ (1, 2)`.

The zero-side inputs (`BlockInputs`, `TailInputs`, `θ₀`, `NII`, `Gz = Gp`, the taper constant) are the
artifact's; it proves them for every `P.Valid`, whose field `lam_le_one` forces `λ ≤ 1`.  At `λ ∈ (1,2)`
they are therefore taken here as explicit hypotheses (the assembly below uses `λ < 2` only through
`T^{λ/2−1} → 0`, exactly as the artifact's docstrings note: "indeed for `λ < 2`").

No `sorry`, no `axiom`.
-/

open Filter Topology Asymptotics
open Zeta23 Zeta23.Assembly

noncomputable section

namespace Zeta23PC

/-! ## 1. The corrected diagonal weight and the certificate function -/

/-- `J(x) = (1 − ((1 − 1/x)₊)³)/3`: the diagonal weight `L²/3` of [eq:tr2] corrected by the `O₁` main term. -/
def J (x : ℝ) : ℝ := (1 - (max (1 - 1 / x) 0) ^ 3) / 3

/-- The Frobenius law with the `O₁` main term: `cPCC(x) = 1/x + x·J(x)`. -/
def cPCC (x : ℝ) : ℝ := 1 / x + x * J x

/-- The certificate: `HPCC = 2 − cPCC`. -/
def HPCC (x : ℝ) : ℝ := 2 - cPCC x

lemma J_nonneg {x : ℝ} (hx : 0 < x) : 0 ≤ J x := by
  unfold J
  have h1 : max (1 - 1 / x) 0 ≤ 1 := by
    apply max_le _ zero_le_one
    have : 0 < 1 / x := by positivity
    linarith
  have h0 : 0 ≤ max (1 - 1 / x) 0 := le_max_right _ _
  have : (max (1 - 1 / x) 0) ^ 3 ≤ 1 := by
    calc (max (1 - 1 / x) 0) ^ 3 ≤ 1 ^ 3 := by gcongr
      _ = 1 := by norm_num
  linarith

lemma J_le_third (x : ℝ) : J x ≤ 1 / 3 := by
  unfold J
  have h0 : 0 ≤ (max (1 - 1 / x) 0) ^ 3 := by positivity
  linarith

/-- For `x ≥ 1`, `J(x) = (1 − (1 − 1/x)³)/3`. -/
lemma J_eq_of_one_le {x : ℝ} (hx : 1 ≤ x) : J x = (1 - (1 - 1 / x) ^ 3) / 3 := by
  unfold J
  have hx0 : 0 < x := by linarith
  have : (0 : ℝ) ≤ 1 - 1 / x := by
    rw [sub_nonneg, div_le_one hx0]; exact hx
  rw [max_eq_left this]

/-- For `x ≥ 1`, `cPCC(x) = 1 + 1/(3x²)`. -/
lemma cPCC_eq_of_one_le {x : ℝ} (hx : 1 ≤ x) : cPCC x = 1 + 1 / (3 * x ^ 2) := by
  unfold cPCC
  rw [J_eq_of_one_le hx]
  have hx0 : x ≠ 0 := by linarith
  field_simp
  ring

/-- For `x ≥ 1`, `HPCC(x) = 1 − 1/(3x²)`; `HPCC(1) = 2/3` (continuity with the artifact's `H(1)`). -/
lemma HPCC_eq_of_one_le {x : ℝ} (hx : 1 ≤ x) : HPCC x = 1 - 1 / (3 * x ^ 2) := by
  unfold HPCC
  rw [cPCC_eq_of_one_le hx]
  ring

lemma continuousAt_J {x : ℝ} (hx : x ≠ 0) : ContinuousAt J x := by
  unfold J
  have h1 : ContinuousAt (fun y : ℝ => 1 / y) x := continuousAt_const.div continuousAt_id hx
  have h2 : ContinuousAt (fun y : ℝ => max (1 - 1 / y) 0) x :=
    (continuousAt_const.sub h1).max continuousAt_const
  exact (continuousAt_const.sub (h2.pow 3)).div_const 3

lemma continuousAt_HPCC {x : ℝ} (hx : x ≠ 0) : ContinuousAt HPCC x := by
  unfold HPCC cPCC
  exact continuousAt_const.sub
    ((continuousAt_const.div continuousAt_id hx).add (continuousAt_id.mul (continuousAt_J hx)))

/-! ## 2. The hypothesis: [thm:traces] with the `O₁` main term -/

/-- The corrected second-moment main term `(TL/2π)(ℓ₁² + L²·J(λ₁))` (the artifact's `Params.mainTr2` has
`L²/3`, i.e. `J ≡ 1/3`). -/
def mainTr2PCC (P : Params) (T : ℝ) : ℝ :=
  T * P.L T / (2 * Real.pi) * (ell1 T ^ 2 + P.L T ^ 2 * J (P.lam1 T))

/-- **The pair-correlation trace package** — the ONE hypothesis.  [eq:tr1] (first form) exactly as in the
artifact's `TracesBoundsE`, and [eq:tr2] with `mainTr2PCC`: the prime-side second moment carries the `O₁`
main term.  For `λ ≤ 1` this is the artifact's theorem (`J(λ₁) = 1/3` once `λ₁ ≤ 1`); for `λ > 1` it is
what Montgomery's pair correlation on Fourier support `(1, λ]` delivers (R113). -/
structure PairCorrelationTraces (P : Params) (Err : ℝ → ℝ) (Z : ZeroConfig) : Prop where
  tr1 : EvBound (fun T => P.trGtilde T - P.a T * P.L T * (Z.N T (2 * T) : ℝ))
    (fun T => P.L T * Real.sqrt (P.X T))
  tr2 : EvBound (fun T => P.trGtildeSq T - mainTr2PCC P T) (fun T => Err T * mainTr2PCC P T)

/-! ### Consistency with the artifact at `λ ≤ 1` (the hypothesis is inhabited there by its theorem) -/

lemma J_eq_third_of_le_one {x : ℝ} (h0 : 0 < x) (h1 : x ≤ 1) : J x = 1 / 3 := by
  unfold J
  have hx : 1 ≤ 1 / x := by rw [le_div_iff₀ h0]; linarith
  have : max (1 - 1 / x) 0 = 0 := max_eq_right (by linarith)
  rw [this]
  norm_num

/-- For `0 < x ≤ 1`, `HPCC x = Hfun x`: the certificate agrees with the artifact's `H(λ) = 2 − 1/λ − λ/3`. -/
lemma HPCC_eq_Hfun_of_le_one {x : ℝ} (h0 : 0 < x) (h1 : x ≤ 1) : HPCC x = Hfun x := by
  unfold HPCC cPCC Hfun
  rw [J_eq_third_of_le_one h0 h1]
  ring

lemma mainTr2PCC_eq_mainTr2 (P : Params) {T : ℝ} (h0 : 0 < P.lam1 T) (h1 : P.lam1 T ≤ 1) :
    mainTr2PCC P T = P.mainTr2 T := by
  unfold mainTr2PCC Params.mainTr2
  rw [J_eq_third_of_le_one h0 h1]
  ring

/-- **At `λ ≤ 1` the hypothesis is the artifact's theorem** ([thm:traces] = `Zeta23.PrimeSide.thm_traces`):
`ThmTracesHyp P Z → PairCorrelationTraces P P.calE Z`. -/
theorem pairCorrelationTraces_of_thmTraces {P : Params} {Z : ZeroConfig} (hlam : 0 < P.lam)
    (hlam1 : P.lam ≤ 1) (h : ThmTracesHyp P Z) : PairCorrelationTraces P P.calE Z := by
  refine ⟨h.tr1, ?_⟩
  obtain ⟨C, hC, T₀, hT⟩ := h.tr2
  refine ⟨C, hC, max T₀ (2 * Real.pi + 1), fun T hT' => ?_⟩
  have hT2 : 2 * Real.pi + 1 ≤ T := le_trans (le_max_right _ _) hT'
  have hl : 0 < l T := by
    unfold l
    apply Real.log_pos
    rw [lt_div_iff₀ (by positivity)]
    linarith
  have h0 := lam1_pos P T hlam hl
  have h1 : P.lam1 T ≤ 1 := (lam1_le P T hlam.le hl).trans hlam1
  have := hT T (le_trans (le_max_left _ _) hT')
  simp only at this ⊢
  rw [mainTr2PCC_eq_mainTr2 P h0 h1]
  exact this

/-! ## 3. The assembly with a general Frobenius law -/

/-- `N0star_lower_H` with a general Frobenius coefficient `c` in place of `1/λ₁ + λ₁/3`. -/
theorem N0star_lower_general
    {N0star N NII trGh frGh B c R₁ R₂ : ℝ} (hB : 0 ≤ B)
    (h0 : 4 * trGh - frGh - 2 * N - 3 * NII - B * (4 + 2 * Real.sqrt frGh + B) ≤ N0star)
    (htr : |trGh - N| ≤ R₁) (hfr : frGh ≤ c * N + R₂) :
    (2 - c) * N - (4 * R₁ + R₂ + 3 * NII + B * (4 + 2 * Real.sqrt (c * N + R₂) + B)) ≤ N0star := by
  have h1 : N - R₁ ≤ trGh := by have := (abs_le.mp htr).1; linarith
  have h2 : Real.sqrt frGh ≤ Real.sqrt (c * N + R₂) := Real.sqrt_le_sqrt hfr
  nlinarith [h0, h1, h2, hB, mul_le_mul_of_nonneg_left h2 hB]

/-- The hat-unit identity with a general diagonal weight `Jv`:
`(aL)⁻² · (TL/2π)(ℓ₁² + L² Jv) = a⁻² · (1/(L/ℓ₁) + (L/ℓ₁) Jv) · (Tℓ₁/2π)`. -/
lemma mainTr2PCC_hat_identity {a L T ℓ₁ Jv : ℝ} (ha : a ≠ 0) (hL : L ≠ 0) (hℓ₁ : ℓ₁ ≠ 0) :
    ((a * L)⁻¹) ^ 2 * (T * L / (2 * Real.pi) * (ℓ₁ ^ 2 + L ^ 2 * Jv))
      = (a ^ 2)⁻¹ * (1 / (L / ℓ₁) + (L / ℓ₁) * Jv) * (T * ℓ₁ / (2 * Real.pi)) := by
  field_simp

/-- `frobGhat_le` with a general diagonal weight `Jv ≥ 0`. -/
theorem frobGhat_le_PCC {a L T ℓ₁ trG2 C calE N RN Jv : ℝ} (ha : 0 < a) (hL : 0 < L) (hℓ₁ : 0 < ℓ₁)
    (hJ : 0 ≤ Jv) (hK : 0 ≤ 1 + C * calE)
    (htr2 : trG2 - T * L / (2 * Real.pi) * (ℓ₁ ^ 2 + L ^ 2 * Jv)
              ≤ C * calE * (T * L / (2 * Real.pi) * (ℓ₁ ^ 2 + L ^ 2 * Jv)))
    (hRvM : T * ℓ₁ / (2 * Real.pi) ≤ N + RN) :
    ((a * L)⁻¹) ^ 2 * trG2
      ≤ (1 / (L / ℓ₁) + (L / ℓ₁) * Jv) * N
        + (1 / (L / ℓ₁) + (L / ℓ₁) * Jv) * (((1 + C * calE) / a ^ 2 - 1) * N
            + (1 + C * calE) / a ^ 2 * RN) := by
  set M := T * L / (2 * Real.pi) * (ℓ₁ ^ 2 + L ^ 2 * Jv) with hM
  set cl := 1 / (L / ℓ₁) + (L / ℓ₁) * Jv with hcl
  have hcl0 : 0 ≤ cl := by rw [hcl]; positivity
  have h1 : trG2 ≤ (1 + C * calE) * M := by linarith
  have h2 : ((a * L)⁻¹) ^ 2 * trG2 ≤ ((a * L)⁻¹) ^ 2 * ((1 + C * calE) * M) :=
    mul_le_mul_of_nonneg_left h1 (sq_nonneg _)
  have h3 : ((a * L)⁻¹) ^ 2 * ((1 + C * calE) * M)
      = (1 + C * calE) / a ^ 2 * cl * (T * ℓ₁ / (2 * Real.pi)) := by
    have := mainTr2PCC_hat_identity (T := T) (Jv := Jv) ha.ne' hL.ne' hℓ₁.ne'
    rw [← hM, ← hcl] at this
    calc ((a * L)⁻¹) ^ 2 * ((1 + C * calE) * M) = (1 + C * calE) * (((a * L)⁻¹) ^ 2 * M) := by ring
      _ = (1 + C * calE) * ((a ^ 2)⁻¹ * cl * (T * ℓ₁ / (2 * Real.pi))) := by rw [this]
      _ = _ := by ring
  have hKa : 0 ≤ (1 + C * calE) / a ^ 2 := by positivity
  have h4 : (1 + C * calE) / a ^ 2 * cl * (T * ℓ₁ / (2 * Real.pi))
      ≤ (1 + C * calE) / a ^ 2 * cl * (N + RN) :=
    mul_le_mul_of_nonneg_left hRvM (mul_nonneg hKa hcl0)
  calc ((a * L)⁻¹) ^ 2 * trG2 ≤ (1 + C * calE) / a ^ 2 * cl * (N + RN) := by linarith
    _ = cl * N + cl * (((1 + C * calE) / a ^ 2 - 1) * N + (1 + C * calE) / a ^ 2 * RN) := by ring

/-- **Seam B with the corrected second moment** (the artifact's `seamB` with `mainTr2PCC`, `cPCC`). -/
theorem seamB_PCC {Z : ZeroConfig} {P : Params} {T : ℝ}
    (hGzGp : Z.Gz P T = P.Gp T) (ha : 0 < P.a T) (hL : 0 < P.L T) (hℓ₁ : 0 < ell1 T)
    (hl1 : 0 < P.lam1 T) {C₁ C₂ ET RN : ℝ}
    (htr1 : |P.trGtilde T - P.a T * P.L T * (Z.N T (2 * T) : ℝ)| ≤ C₁ * (P.L T * Real.sqrt (P.X T)))
    (hK : 0 ≤ 1 + C₂ * ET)
    (htr2 : P.trGtildeSq T - mainTr2PCC P T ≤ C₂ * ET * mainTr2PCC P T)
    (hRvM : T * ell1 T / (2 * Real.pi) ≤ (Z.N T (2 * T) : ℝ) + RN) :
    |RHLinalg.rtrace (P.hat T (Z.Gz P T)) - (Z.N T (2 * T) : ℝ)| ≤ C₁ * Real.sqrt (P.X T) / P.a T ∧
    RHLinalg.frobSq (P.hat T (Z.Gz P T)) ≤ cPCC (P.lam1 T) * (Z.N T (2 * T) : ℝ)
      + cPCC (P.lam1 T) * (((1 + C₂ * ET) / P.a T ^ 2 - 1) * (Z.N T (2 * T) : ℝ)
          + (1 + C₂ * ET) / P.a T ^ 2 * RN) := by
  rw [hGzGp, rtrace_hat, frobSq_hat, rtrace_tilde_Gp, frobSq_tilde_Gp]
  refine ⟨trGhat_sub_N_le ha hL htr1, ?_⟩
  have := frobGhat_le_PCC (T := T) (trG2 := P.trGtildeSq T) (N := (Z.N T (2 * T) : ℝ))
    (Jv := J (P.lam1 T)) ha hL hℓ₁ (J_nonneg hl1) hK (by simpa [mainTr2PCC] using htr2) hRvM
  simpa [cPCC, Params.lam1] using this

/-! ## 4. The λ-lemmas at `λ < 2` (the artifact states them for `λ ≤ 1`, "indeed for `λ < 2`") -/

lemma tendsto_rpow_halflam_sub_one' (P : Params) (hlam2 : P.lam < 2) :
    Tendsto (fun T : ℝ => T ^ (P.lam / 2 - 1)) atTop (𝓝 0) := by
  have : Tendsto (fun T : ℝ => T ^ (-(1 - P.lam / 2))) atTop (𝓝 0) :=
    tendsto_rpow_neg_atTop (by linarith)
  simpa [neg_sub] using this

lemma isLittleO_sqrtX_Tl' (P : Params) (hlam : 0 < P.lam) (hlam2 : P.lam < 2) :
    (fun T => Real.sqrt (P.X T)) =o[atTop] fun T => T * l T := by
  refine (isLittleO_iff).2 fun c hc => ?_
  filter_upwards [(tendsto_rpow_halflam_sub_one' P hlam2).eventually (eventually_le_nhds hc),
    eventually_gt_atTop 0, eventually_one_le_l] with T hTc hT hl
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
    abs_of_nonneg (by positivity), sqrtX_eq P hT]
  have h2π : T / (2 * Real.pi) ≤ T := div_le_self hT.le (by linarith [Real.pi_gt_three])
  calc (T / (2 * Real.pi)) ^ (P.lam / 2) ≤ T ^ (P.lam / 2) :=
        Real.rpow_le_rpow (by positivity) h2π (by linarith)
    _ = T * T ^ (P.lam / 2 - 1) := by
        conv_lhs => rw [show P.lam / 2 = 1 + (P.lam / 2 - 1) by ring]
        rw [Real.rpow_add hT, Real.rpow_one]
    _ ≤ T * c := mul_le_mul_of_nonneg_left hTc hT.le
    _ = c * T * 1 := by ring
    _ ≤ c * T * l T := mul_le_mul_of_nonneg_left hl (by positivity)
    _ = c * (T * l T) := by ring

lemma tendsto_theta_over_L' (P : Params) (hlam : 0 < P.lam) (hlam2 : P.lam < 2) :
    Tendsto (fun T => l T * T ^ (P.lam / 2 - 1) / P.L T) atTop (𝓝 0) := by
  have h1 := tendsto_rpow_halflam_sub_one' P hlam2
  have h2 : (fun T => l T * T ^ (P.lam / 2 - 1) / P.L T) =ᶠ[atTop]
      fun T => P.lam⁻¹ * T ^ (P.lam / 2 - 1) := by
    filter_upwards [eventually_l_pos] with T hl
    simp only [Params.L]; field_simp
  rw [tendsto_congr' h2]
  simpa using h1.const_mul P.lam⁻¹

/-- `λ₁(T) → λ` (the artifact's `ThmD.tendsto_lam1`, restated here to avoid the `ThmD` import). -/
lemma tendsto_lam1' (P : Params) (hlam : 0 < P.lam) :
    Tendsto (fun T => P.lam1 T) atTop (𝓝 P.lam) := by
  have hl := tendsto_l_atTop
  have hbound : ∀ᶠ T in atTop, P.lam - P.lam / l T ≤ P.lam1 T ∧ P.lam1 T ≤ P.lam := by
    filter_upwards [eventually_l_pos] with T hlT
    exact ⟨by linarith [sub_lam1_le P T hlam.le hlT], lam1_le P T hlam.le hlT⟩
  have hlow : Tendsto (fun T => P.lam - P.lam / l T) atTop (𝓝 P.lam) := by
    have h0 : Tendsto (fun T => P.lam / l T) atTop (𝓝 0) :=
      Tendsto.div_atTop tendsto_const_nhds hl
    have := tendsto_const_nhds (x := P.lam) (f := atTop (α := ℝ)) |>.sub h0
    simpa using this
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds
    (hbound.mono fun T h => h.1) (hbound.mono fun T h => h.2)

/-- `cPCC(λ₁)` is eventually in `[0, 2/λ + λ/3]` (since `λ/2 ≤ λ₁ ≤ λ` once `l ≥ 1`, and `0 ≤ J ≤ 1/3`). -/
lemma eventually_cPCC_bounds (P : Params) (hlam : 0 < P.lam) :
    ∀ᶠ T in atTop, 0 ≤ cPCC (P.lam1 T) ∧ cPCC (P.lam1 T) ≤ 2 / P.lam + P.lam / 3 := by
  filter_upwards [tendsto_l_atTop.eventually_ge_atTop 1] with T hl
  have hlpos : 0 < l T := by linarith
  have hc := c₀_pos; have hc1 := c₀_lt_one
  have hl1pos := lam1_pos P T hlam hlpos
  have hl1le := lam1_le P T hlam.le hlpos
  have hhalf : P.lam / 2 ≤ P.lam1 T := by
    rw [lam1_eq, le_div_iff₀ (by linarith)]; nlinarith
  have hJ0 := J_nonneg hl1pos
  have hJ1 := J_le_third (P.lam1 T)
  unfold cPCC
  refine ⟨by positivity, ?_⟩
  have h1 : 1 / P.lam1 T ≤ 2 / P.lam := by
    rw [div_le_div_iff₀ hl1pos hlam]; linarith
  have h2 : P.lam1 T * J (P.lam1 T) ≤ P.lam / 3 := by
    calc P.lam1 T * J (P.lam1 T) ≤ P.lam1 T * (1 / 3) :=
          mul_le_mul_of_nonneg_left hJ1 hl1pos.le
      _ ≤ P.lam * (1 / 3) := mul_le_mul_of_nonneg_right hl1le (by norm_num)
      _ = P.lam / 3 := by ring
  linarith

/-! ## 5. The conditional theorem, abstract zero configuration -/

/-- **The artifact's Theorem A assembly with the pair-correlation second moment, `λ < 2`.**
Under `PairCorrelationTraces` and the artifact's zero-side inputs, for every `ε > 0`,
`N₀*(T,2T) ≥ (HPCC(λ) − ε) N(T,2T)` for all large `T`.  Mirrors `Zeta23.Assembly.thmA_abstract_err`
line by line; the differences are `hlam2 : P.lam < 2` (used only through `T^{λ/2−1} → 0`), `cPCC` in place
of `cλ = 1/λ₁ + λ₁/3`, and the passage `λ₁ → λ` done by continuity of `HPCC` instead of `Hfun_lam1_ge`. -/
theorem thmA_abstract_err_PCC (Z : ZeroConfig) (hRvM : RiemannVonMangoldt Z) (P : Params)
    (hlam0 : 0 < P.lam) (hlam2 : P.lam < 2) (hw : 1 ≤ P.w) (Err : ℝ → ℝ)
    (hTr : PairCorrelationTraces P Err Z)
    (hBlock : ∀ᶠ T in atTop, BlockInputs Z P T)
    (θ₀ : ℝ → ℝ) (hTail : ∀ᶠ T in atTop, TailInputs Z P T (θ₀ T))
    (hθ₀ : ∃ C : ℝ, ∀ᶠ T in atTop, θ₀ T ≤ C * l T * T ^ (P.lam / 2 - 1))
    (hNII : ∃ C : ℝ, ∀ᶠ T in atTop, (NII Z T : ℝ) ≤ C * Real.sqrt T * l T)
    (hGzGp : ∀ᶠ T in atTop, Z.Gz P T = P.Gp T)
    (ha : ∀ᶠ T in atTop, 1 - 2 * P.w / P.L T ≤ P.a T ∧ P.a T ≤ 1)
    (hcalE : Tendsto Err atTop (𝓝 0)) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, (HPCC P.lam - ε) * (Z.N T (2 * T) : ℝ) ≤ Z.N0star T (2 * T) := by
  obtain ⟨C₁, hC₁, T₁, htr1⟩ := hTr.tr1
  obtain ⟨C₂, hC₂, T₂, htr2⟩ := hTr.tr2
  obtain ⟨CN, T₃, hRvMmain⟩ := hRvM.main
  obtain ⟨Cθ, hθ⟩ := hθ₀
  obtain ⟨CII, hII⟩ := hNII
  -- the functions of T (abbreviations)
  set N : ℝ → ℝ := fun T => (Z.N T (2 * T) : ℝ) with hNdef
  set cl : ℝ → ℝ := fun T => cPCC (P.lam1 T) with hcl
  set K : ℝ → ℝ := fun T => (1 + C₂ * Err T) / P.a T ^ 2 with hK
  set R₁ : ℝ → ℝ := fun T => C₁ * Real.sqrt (P.X T) / P.a T with hR₁
  set R₂ : ℝ → ℝ := fun T => cl T * ((K T - 1) * N T + K T * (|CN| * Real.log T)) with hR₂
  set B : ℝ → ℝ := fun T => θ₀ T / (P.a T * P.L T) with hBdef
  set dH : ℝ → ℝ := fun T => |HPCC (P.lam1 T) - HPCC P.lam| with hdH
  set err : ℝ → ℝ := fun T => (4 * R₁ T + R₂ T + 3 * (NII Z T : ℝ)
      + B T * (4 + 2 * Real.sqrt (cl T * N T + R₂ T) + B T)) + dH T * N T with herr
  -- basic limits
  have hLtop := tendsto_L_atTop P hlam0
  have ha1 := tendsto_a_one P hlam0 ha
  have hapos : ∀ᶠ T in atTop, 1 / 2 ≤ P.a T := by
    filter_upwards [ha, hLtop.eventually_ge_atTop (4 * P.w)] with T h hL4
    have hLpos : 0 < P.L T := by linarith
    have : 2 * P.w / P.L T ≤ 1 / 2 := by rw [div_le_iff₀ hLpos]; linarith
    linarith [h.1]
  have hcE0 : Tendsto (fun T => C₂ * Err T) atTop (𝓝 0) := by
    simpa using hcalE.const_mul C₂
  have hKto : Tendsto K atTop (𝓝 1) := by
    have h1 : Tendsto (fun T => 1 + C₂ * Err T) atTop (𝓝 1) := by
      simpa using tendsto_const_nhds.add hcE0
    have h2 : Tendsto (fun T => P.a T ^ 2) atTop (𝓝 1) := by simpa using ha1.pow 2
    simpa [hK, Pi.div_def] using h1.div h2 one_ne_zero
  -- λ₁ → λ, hence HPCC(λ₁) → HPCC(λ)
  have hlam1t : Tendsto (fun T => P.lam1 T) atTop (𝓝 P.lam) := tendsto_lam1' P hlam0
  have hHt : Tendsto (fun T => HPCC (P.lam1 T)) atTop (𝓝 (HPCC P.lam)) :=
    (continuousAt_HPCC hlam0.ne').tendsto.comp hlam1t
  have hdH0 : Tendsto dH atTop (𝓝 0) := by
    have := (hHt.sub (tendsto_const_nhds (x := HPCC P.lam))).abs
    simpa [hdH] using this
  -- (1) the main inequality, eventually in T
  have hmain : ∀ᶠ T in atTop, HPCC P.lam * N T - err T ≤ (Z.N0star T (2 * T) : ℝ) := by
    filter_upwards [hBlock, hTail, hGzGp, hapos, eventually_ge_atTop T₁,
      eventually_ge_atTop T₂, eventually_ge_atTop T₃, eventually_ge_atTop (0:ℝ), eventually_l_pos,
      eventually_log_nonneg, hcE0.eventually (eventually_gt_nhds (show (-1:ℝ) < 0 by norm_num))]
      with T hB hTl hGG ha2 hT₁ hT₂ hT₃ hT0 hl hlog hcE
    have hapos' : 0 < P.a T := by linarith
    have hLpos : 0 < P.L T := by simp only [Params.L]; positivity
    have hℓ₁ := ell1_pos hl
    have hl1pos := lam1_pos P T hlam0 hl
    have hKnn : 0 ≤ 1 + C₂ * Err T := by linarith
    have hA := seamA hT0 hB hTl hapos' hLpos
    have htr2' : P.trGtildeSq T - mainTr2PCC P T ≤ C₂ * Err T * mainTr2PCC P T := by
      have := htr2 T hT₂
      simp only at this
      rw [← mul_assoc] at this
      exact (le_abs_self _).trans this
    have htr1' : |P.trGtilde T - P.a T * P.L T * (Z.N T (2 * T) : ℝ)|
        ≤ C₁ * (P.L T * Real.sqrt (P.X T)) := by
      have := htr1 T hT₁; simpa only using this
    have hRvM' : T * ell1 T / (2 * Real.pi) ≤ N T + |CN| * Real.log T := by
      have h1 := (abs_le.mp (hRvMmain T hT₃)).1
      have h2 : CN * Real.log T ≤ |CN| * Real.log T :=
        mul_le_mul_of_nonneg_right (le_abs_self _) hlog
      have h3 : T / (2 * Real.pi) * ell1 T = T * ell1 T / (2 * Real.pi) := by ring
      simp only [hNdef]; linarith
    have hSB := seamB_PCC hGG hapos' hLpos hℓ₁ hl1pos htr1' hKnn htr2' hRvM'
    have hB₀ : 0 ≤ B T := div_nonneg hTl.theta_nonneg (mul_pos hapos' hLpos).le
    have h := N0star_lower_general hB₀ hA hSB.1 hSB.2
    have hN0 : 0 ≤ N T := Nat.cast_nonneg _
    have hHN : (HPCC P.lam - dH T) * N T ≤ (2 - cPCC (P.lam1 T)) * N T := by
      apply mul_le_mul_of_nonneg_right _ hN0
      have := neg_abs_le (HPCC (P.lam1 T) - HPCC P.lam)
      simp only [hdH, HPCC] at this ⊢
      linarith
    simp only [herr, hR₁, hR₂, hBdef, hcl, hK, hNdef, hdH] at h hHN ⊢
    linarith
  -- (2) err = o(N)
  have hNtop : Tendsto N atTop atTop := tendsto_N_atTop Z hRvM
  -- R₁ = o(N)
  have o1 : R₁ =o[atTop] N := by
    have hbd : (fun T => C₁ / P.a T) =O[atTop] (fun _ => (1:ℝ)) := by
      refine isBigO_one_of_abs_le (C := 2 * C₁) ?_
      filter_upwards [hapos] with T ha2
      rw [abs_of_nonneg (div_nonneg hC₁.le (by linarith))]
      rw [div_le_iff₀ (by linarith)]; nlinarith
    have := isLittleO_of_bdd_mul hbd
      (isLittleO_N_of_isLittleO_Tl Z hRvM (isLittleO_sqrtX_Tl' P hlam0 hlam2))
    exact this.congr_left fun T => by simp only [hR₁]; ring
  -- R₂ = o(N)
  have o2 : R₂ =o[atTop] N := by
    have hclO : cl =O[atTop] (fun _ => (1:ℝ)) := by
      refine isBigO_one_of_abs_le (C := 2 / P.lam + P.lam / 3) ?_
      filter_upwards [eventually_cPCC_bounds P hlam0] with T h
      rw [abs_of_nonneg h.1]; exact h.2
    have hK1 : Tendsto (fun T => K T - 1) atTop (𝓝 0) := by simpa using hKto.sub_const 1
    have hKO : K =O[atTop] (fun _ => (1:ℝ)) := by
      refine isBigO_one_of_abs_le (C := 2) ?_
      filter_upwards [hKto.eventually (eventually_ge_nhds (show (0:ℝ) < 1 by norm_num)),
        hKto.eventually (eventually_le_nhds (show (1:ℝ) < 2 by norm_num))] with T h1 h2
      rw [abs_of_nonneg h1]; exact h2
    have i1 : (fun T => (K T - 1) * N T) =o[atTop] N := isLittleO_of_tendsto_zero_mul hK1
    have i2 : (fun T => K T * (|CN| * Real.log T)) =o[atTop] N :=
      isLittleO_of_bdd_mul hKO ((isLittleO_N_of_isLittleO_Tl Z hRvM isLittleO_log_Tl).const_mul_left _)
    exact isLittleO_of_bdd_mul hclO (i1.add i2)
  -- N(I′∖I) = o(N)
  have o3 : (fun T => (NII Z T : ℝ)) =o[atTop] N := by
    have hO : (fun T => (NII Z T : ℝ)) =O[atTop] (fun T => Real.sqrt T * l T) := by
      refine IsBigO.of_bound CII ?_
      filter_upwards [hII, eventually_l_pos] with T h hl
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _),
        abs_of_nonneg (by positivity)]
      simpa [mul_assoc] using h
    exact hO.trans_isLittleO (isLittleO_N_of_isLittleO_Tl Z hRvM isLittleO_sqrt_mul_l_Tl)
  -- B → 0
  have o4 : Tendsto B atTop (𝓝 0) := by
    have hup : Tendsto (fun T => 2 * |Cθ| * (l T * T ^ (P.lam / 2 - 1) / P.L T)) atTop (𝓝 0) := by
      simpa using (tendsto_theta_over_L' P hlam0 hlam2).const_mul (2 * |Cθ|)
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup ?_ ?_
    · filter_upwards [hTail, hapos, eventually_l_pos] with T hTl ha2 hl
      have hLpos : 0 < P.L T := by simp only [Params.L]; positivity
      exact div_nonneg hTl.theta_nonneg (by positivity)
    · filter_upwards [hTail, hapos, eventually_l_pos, hθ, eventually_gt_atTop (0:ℝ)]
        with T hTl ha2 hl hθT hT0
      have hLpos : 0 < P.L T := by simp only [Params.L]; positivity
      have hapos' : 0 < P.a T := by linarith
      have hq : 0 ≤ l T * T ^ (P.lam / 2 - 1) / P.L T := by positivity
      simp only [hBdef]
      rw [div_le_iff₀ (mul_pos hapos' hLpos)]
      calc θ₀ T ≤ Cθ * l T * T ^ (P.lam / 2 - 1) := hθT
        _ ≤ |Cθ| * l T * T ^ (P.lam / 2 - 1) := by gcongr; exact le_abs_self _
        _ = |Cθ| * (l T * T ^ (P.lam / 2 - 1) / P.L T) * P.L T := by field_simp
        _ ≤ (2 * |Cθ| * (l T * T ^ (P.lam / 2 - 1) / P.L T)) * (P.a T * P.L T) := by
          have : |Cθ| * (l T * T ^ (P.lam / 2 - 1) / P.L T) * P.L T
              = (2 * |Cθ| * (l T * T ^ (P.lam / 2 - 1) / P.L T)) * (1 / 2 * P.L T) := by ring
          rw [this]; gcongr
  -- the bracket and the continuity term
  have o5 := err_isLittleO (R₁ := R₁) (R₂ := R₂) (NII := fun T => (NII Z T : ℝ)) (B := B) (cl := cl)
    hNtop o1 o2 o3 o4 (eventually_cPCC_bounds P hlam0)
  have o6 : (fun T => dH T * N T) =o[atTop] N := isLittleO_of_tendsto_zero_mul hdH0
  have herr_o : err =o[atTop] N := o5.add o6
  -- (3) conclude
  exact eps_form_of_isLittleO hmain (Eventually.of_forall fun T => Nat.cast_nonneg _) herr_o

/-! ## 6. The ζ-level reading, `λ ∈ (1, 2)` -/

/-- **Pair correlation on Fourier support `(1, λ]` ⇒ proportion `1 − 1/(3λ²)` of the zeros of `ζ` on the line
(dyadic ε-form).**  The zero-side inputs are the artifact's (`Tail.eventually_tailPackage`,
`eventually_blockInputs`, `eventually_side_conditions`), which it proves for `P.Valid`, i.e. `λ ≤ 1`; at
`λ ∈ (1,2)` they are hypotheses here.  `PairCorrelationTraces` is the pair-correlation input (R113). -/
theorem N0star_zeta_of_pairCorrelation (H : PaperInputs zetaZeroConfig) {ϱ : ℝ → ℝ}
    {lam : ℝ} (h1 : 1 < lam) (h2 : lam < 2) (Err : ℝ → ℝ)
    (hTr : PairCorrelationTraces (paramsOf ϱ lam) Err zetaZeroConfig)
    (hcalE : Tendsto Err atTop (𝓝 0))
    (hBlock : ∀ᶠ T in atTop, BlockInputs zetaZeroConfig (paramsOf ϱ lam) T)
    (θ₀ : ℝ → ℝ) (hTail : ∀ᶠ T in atTop, TailInputs zetaZeroConfig (paramsOf ϱ lam) T (θ₀ T))
    (hθ₀ : ∃ C : ℝ, ∀ᶠ T in atTop, θ₀ T ≤ C * l T * T ^ (lam / 2 - 1))
    (hNII : ∃ C : ℝ, ∀ᶠ T in atTop, (NII zetaZeroConfig T : ℝ) ≤ C * Real.sqrt T * l T)
    (hGzGp : ∀ᶠ T in atTop, zetaZeroConfig.Gz (paramsOf ϱ lam) T = (paramsOf ϱ lam).Gp T)
    (ha : ∀ᶠ T in atTop,
      1 - 2 * (paramsOf ϱ lam).w / (paramsOf ϱ lam).L T ≤ (paramsOf ϱ lam).a T ∧ (paramsOf ϱ lam).a T ≤ 1) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (1 - 1 / (3 * lam ^ 2) - ε) * (Ncount T (2 * T) : ℝ) ≤ N0star T (2 * T) := by
  have hmain := thmA_abstract_err_PCC zetaZeroConfig H.RvM (paramsOf ϱ lam)
    (by simp only [paramsOf]; linarith) (by simp only [paramsOf]; exact h2)
    (by simp only [paramsOf]; exact le_rfl) Err hTr hBlock θ₀ hTail
    (by simpa [paramsOf] using hθ₀) hNII hGzGp ha hcalE
  have hH : HPCC (paramsOf ϱ lam).lam = 1 - 1 / (3 * lam ^ 2) := by
    simp only [paramsOf]
    exact HPCC_eq_of_one_le h1.le
  intro ε hε
  obtain ⟨T₀, hT₀⟩ := hmain ε hε
  refine ⟨T₀, fun T hT => ?_⟩
  have := hT₀ T hT
  rw [hH] at this
  simpa [Ncount, N0star] using this

end Zeta23PC

end

#print axioms Zeta23PC.thmA_abstract_err_PCC
#print axioms Zeta23PC.N0star_zeta_of_pairCorrelation
#print axioms Zeta23PC.HPCC_eq_of_one_le
#print axioms Zeta23PC.pairCorrelationTraces_of_thmTraces
#print axioms Zeta23PC.HPCC_eq_Hfun_of_le_one
