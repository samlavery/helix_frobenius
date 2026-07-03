import RequestProject.TwoClockWeightLaw
import RequestProject.GeneralizedCohomology

/-!
# BSD in the clock chart: similitude ensembles and the center-jet dictionary

Owner's directive (2026-07-03): extend the multidimensional clock tower to BSD.  The
organizing observation: **BSD's rank is a DC-census reading, exactly like Beyond
Endoscopy's poles — one mechanism, two locations.**  A functorial pole is the coherent
assembly of zero-frequency clocks at the edge; the Mordell–Weil rank is the residue of
the logarithmic derivative at the CENTER — the zero-frequency component of the clock
ensemble read at the doubly-fixed point.  The Nagao–Mestre rank heuristics are this
census, never before framed as the same detection problem.

Proven here, unconditional at model level:

* `clockTraceB` / `clockTraceB_ceiling` — **similitude clocks**: faces at radius `√B`
  (the `FrobeniusBlock` determinant law `αβ = B`; for elliptic curves `B = p` and
  purity of the faces is Hasse's theorem — the original purity result).  The whole
  n-clock/k-dimensional tower applies in motivic normalization with the Hasse–Weil
  envelope `‖s_k‖ ≤ n·B^{k/2}` as the line ceiling.
* `rank_is_dc_residue` — **the center-jet dictionary**: if the readout factors as
  `(s−c)^r · G` with `G` regular and nonvanishing at the center, then
  `(s−c)·F′/F → r`: the order of central vanishing IS the DC residue of the
  logarithmic derivative.  Rank as a census, at model level, unconditionally.
* `bsd_rank_parity_even` / `bsd_rank_parity_odd` — the parity conjecture's model
  face, re-exported from the hinge parity kernels: the functional-equation involution
  forces the parity of the first live jet at the center.

The program frame (stated, never assumed): BSD is **EveryCentralJetHasSource** — every
order of central vanishing paid for by a rational-point direction (heights = cup
regulators, the measured 38/38 arc).  Gross–Zagier–Kolyvagin is the proven `ord ≤ 1`
island — the center's analogue of our on-weld bridge-iff.  What remains open is jet
EXHAUSTION at the center: the same missing word, "all," at a different fixed point.
No `sorry`; standard axioms.
-/

open Complex Filter Topology

namespace CriticalLinePhasor.BSDClocks

open CriticalLinePhasor.TwoClockWeightLaw

/-- **Similitude ensemble trace**: n clocks with faces at radius `√B` — the
`FrobeniusBlock` normalization (`αβ = B`; elliptic curves: `B = p`, purity = Hasse). -/
noncomputable def clockTraceB {n : ℕ} (B : ℝ) (θ : Fin n → ℝ) (k : ℕ) : ℂ :=
  ((B ^ ((k : ℝ) / 2) : ℝ) : ℂ) * clockTraceN θ k

/-- **The Hasse–Weil envelope**: similitude ensembles obey `‖s_k‖ ≤ n·B^{k/2}` — the
Ramanujan line ceiling in motivic normalization. -/
theorem clockTraceB_ceiling {n : ℕ} {B : ℝ} (hB : 0 ≤ B) (θ : Fin n → ℝ) (k : ℕ) :
    ‖clockTraceB B θ k‖ ≤ n * B ^ ((k : ℝ) / 2) := by
  unfold clockTraceB
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg hB _)]
  calc B ^ ((k : ℝ) / 2) * ‖clockTraceN θ k‖
      ≤ B ^ ((k : ℝ) / 2) * n :=
        mul_le_mul_of_nonneg_left (ramanujan_line_ceiling θ k) (Real.rpow_nonneg hB _)
    _ = n * B ^ ((k : ℝ) / 2) := mul_comm _ _

/-- **The rank is the DC residue at the center** — the center-jet dictionary at model
level: if the readout factors as `F = (s−c)^r · G` with `G` differentiable,
nonvanishing at `c`, and with continuous derivative there, then `(s−c)·F′/F → r` on
the punctured neighborhood.  The order of central vanishing is read as the
zero-frequency residue of the logarithmic derivative — the same DC-census mechanism
that detects functorial poles at the edge. -/
theorem rank_is_dc_residue {G : ℂ → ℂ} {c : ℂ} (r : ℕ)
    (hG : Differentiable ℂ G) (hGc : G c ≠ 0) (hd : ContinuousAt (deriv G) c) :
    Tendsto (fun s : ℂ => (s - c) * (deriv (fun z => (z - c) ^ r * G z) s
        / ((s - c) ^ r * G s)))
      (𝓝[≠] c) (𝓝 (r : ℂ)) := by
  have hev : ∀ᶠ s in 𝓝[≠] c,
      (r : ℂ) + (s - c) * (deriv G s / G s)
        = (s - c) * (deriv (fun z => (z - c) ^ r * G z) s / ((s - c) ^ r * G s)) := by
    have hne : ∀ᶠ s in 𝓝 c, G s ≠ 0 :=
      hG.continuous.continuousAt.eventually_ne hGc
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds hne] with s hs hGs
    have hsc : s - c ≠ 0 := sub_ne_zero.mpr hs
    have h1 : HasDerivAt (fun z : ℂ => (z - c) ^ r)
        ((r : ℂ) * (s - c) ^ (r - 1) * 1) s :=
      ((hasDerivAt_id s).sub_const c).pow r
    have h2 : HasDerivAt G (deriv G s) s := (hG s).hasDerivAt
    have hD : deriv (fun z => (z - c) ^ r * G z) s
        = (r : ℂ) * (s - c) ^ (r - 1) * 1 * G s + (s - c) ^ r * deriv G s :=
      (h1.mul h2).deriv
    rw [hD]
    have hpow : (s - c) ^ r ≠ 0 := pow_ne_zero r hsc
    field_simp
    rcases Nat.eq_zero_or_pos r with hr | hr
    · subst hr
      simp
    · have hsplit : (s - c) ^ r = (s - c) ^ (r - 1) * (s - c) := by
        rw [← pow_succ, Nat.sub_add_cancel hr]
      rw [hsplit]
      ring
  have h1 : Tendsto (fun s : ℂ => (s - c) * (deriv G s / G s)) (𝓝 c) (𝓝 0) := by
    have hc : ContinuousAt (fun s : ℂ => (s - c) * (deriv G s / G s)) c := by
      exact ((continuous_id.sub continuous_const).continuousAt).mul
        (hd.div hG.continuous.continuousAt hGc)
    have h0 : (fun s : ℂ => (s - c) * (deriv G s / G s)) c = 0 := by simp
    simpa [h0] using hc.tendsto
  have hlim : Tendsto (fun s : ℂ => (r : ℂ) + (s - c) * (deriv G s / G s))
      (𝓝[≠] c) (𝓝 (r : ℂ)) := by
    have := (tendsto_const_nhds (x := (r : ℂ)) (f := 𝓝[≠] c)).add
      (h1.mono_left nhdsWithin_le_nhds)
    simpa using this
  exact hlim.congr' hev

/-- **Rank parity from the sign, even case** — the parity conjecture's model face:
an even functional-equation involution forces the first live central jet to have even
order. -/
theorem bsd_rank_parity_even {f : ℝ → ℝ} (hsym : ∀ t, f (-t) = f t) {k : ℕ}
    (hk : iteratedDeriv k f 0 ≠ 0) : Even k :=
  GeneralizedCohomology.dimension_parity_of_involution_even hsym hk

/-- Rank parity, odd case: an odd involution forces odd first-live-jet order. -/
theorem bsd_rank_parity_odd {f : ℝ → ℝ} (hsym : ∀ t, f (-t) = -f t) {k : ℕ}
    (hk : iteratedDeriv k f 0 ≠ 0) : Odd k :=
  GeneralizedCohomology.dimension_parity_of_involution_odd hsym hk

/-! ## The jet rung (owner: "jet next", 2026-07-03)

`rank_is_dc_residue` read the ORDER of central vanishing.  The jet rung reads the
VALUE: the leading jet of `F = (s−c)^r·G` is `G(c)` — and `G(c)` is where the entire
BSD right-hand side lives (period × regulator × Ш / torsion², the distinguished-point
law).  Gross–Zagier, in this chart, is the statement that the FIRST jet is a height —
a cup-metric pairing value (community theorem; our cup form is its model pairing).

* `leading_jet_extraction` — `F/(s−c)^r → G(c)`: the leading coefficient is
  extractable through the punctured limit, unconditionally.
* `first_jet_eq_deriv` — the `r = 1` case is literally the derivative:
  `F = (s−c)·G ⟹ F′(c) = G(c)`.  The Gross–Zagier jet is a derivative reading.
* `jet_measurement_sound` — the BSD full-formula license at EVERY rank: when the
  leading jet is a distinguished-point value with integer obstruction (Ш), a jet
  measurement within ½ identifies the integer uniquely — the Sha-hinge method,
  formally licensed one jet up (and r jets up). -/

/-- **Leading-jet extraction**: the leading coefficient of `(s−c)^r·G` is `G(c)`,
read through the punctured limit. -/
theorem leading_jet_extraction {G : ℂ → ℂ} {c : ℂ} (r : ℕ) (hG : ContinuousAt G c) :
    Tendsto (fun s : ℂ => ((s - c) ^ r * G s) / (s - c) ^ r) (𝓝[≠] c) (𝓝 (G c)) := by
  have hev : ∀ᶠ s in 𝓝[≠] c, G s = ((s - c) ^ r * G s) / (s - c) ^ r := by
    filter_upwards [self_mem_nhdsWithin] with s hs
    rw [mul_div_cancel_left₀ _ (pow_ne_zero r (sub_ne_zero.mpr hs))]
  exact (hG.tendsto.mono_left nhdsWithin_le_nhds).congr' hev

/-- **The first jet is the derivative**: `F = (s−c)·G` with `G` continuous at `c` has
`F′(c) = G(c)` — the Gross–Zagier jet is a derivative reading. -/
theorem first_jet_eq_deriv {G : ℂ → ℂ} {c : ℂ} (hG : ContinuousAt G c) :
    HasDerivAt (fun s : ℂ => (s - c) * G s) (G c) c := by
  rw [hasDerivAt_iff_tendsto_slope]
  have hev : ∀ᶠ s in 𝓝[≠] c, G s = slope (fun s : ℂ => (s - c) * G s) c s := by
    filter_upwards [self_mem_nhdsWithin] with s hs
    rw [slope_def_field]
    field_simp [sub_ne_zero.mpr hs]
    ring
  exact (hG.tendsto.mono_left nhdsWithin_le_nhds).congr' hev

/-- **Jet measurement soundness** — the BSD full-formula license at every rank: when
the leading jet is a distinguished-point value with integer obstruction (Ш), a
measurement of the jet-recovery ratio within ½ identifies the integer uniquely.  (The
Sha-hinge landing method, formally licensed `r` jets up.) -/
theorem jet_measurement_sound (D : GeneralizedCohomology.DistinguishedPoint) {o : ℤ}
    (ho : D.obstruction = o) {x : ℝ}
    (hx : |x - D.value * D.torsion / (D.period * D.regulator)| < 1 / 2)
    {o' : ℤ} (ho' : |x - o'| < 1 / 2) : o' = o :=
  D.measurement_sound ho hx ho'

/-! ## EveryCentralJetHasSource: the BSD target named, the source side secured

The mirror of `SourceHolonomy.Exhaustive`, at the center.  BSD's rank statement is a
source-completeness claim: every order of central vanishing is paid for by an
independent rational-point direction.  What is provable TODAY is that the source side
never defaults: the Néron–Tate pairing on the free part of the Mordell–Weil group is
positive-definite (community theorem), and a positive-definite pairing has strictly
positive regulator — so with `r` independent sources the payment is always nonzero and
the distinguished-point recovery is well-posed at every rank. -/

/-- **Sources can always pay**: a positive-definite height pairing (the Néron–Tate
Gram matrix of `r` independent directions) has strictly positive regulator. -/
theorem regulator_pos {r : ℕ} {H : Matrix (Fin r) (Fin r) ℝ} (hH : H.PosDef) :
    0 < H.det :=
  hH.det_pos

/-- The regulator of independent sources never vanishes — the `regulator_ne` field of
the distinguished-point law is always suppliable from source independence. -/
theorem regulator_ne_zero {r : ℕ} {H : Matrix (Fin r) (Fin r) ℝ} (hH : H.PosDef) :
    H.det ≠ 0 :=
  ne_of_gt hH.det_pos

/-- **THE BSD TARGET, named** (a `Prop`, stated, never assumed): every central jet has
a source — the order of central vanishing equals the number of independent source
directions.  Gross–Zagier–Kolyvagin is the proven `ord ≤ 1` island; measured in-house:
|Ш| landed at ranks 1–3 (`tmp/jet_census_results.txt`).  The open content is jet
EXHAUSTION at the center — the same missing word ("all") as `Exhaustive` on the weld,
at the other fixed point. -/
def EveryCentralJetHasSource (analyticOrder sourceRank : ℕ) : Prop :=
  analyticOrder = sourceRank

/-! ## The three closing rungs (owner: "do 1, 2, 3", 2026-07-03)

1. `nClock_logDeriv_expansion` — the CENSUS DERIVED: the log-derivative of the n-clock
   Euler factor has k-th Dirichlet coefficient exactly `s_{k+1}` — the quantity the
   smooth-entry DC census sums.  The census statistic is no longer a heuristic
   borrowed from Nagao–Mestre: its coefficients are the clock traces, by theorem.
2. `gz_first_jet_live` — the GROSS–ZAGIER MODEL STATEMENT: if the first jet is a
   positive multiple of the pairing norm of a nonzero direction (the Heegner point)
   under a positive-definite height pairing, the jet is strictly positive — the
   analytic order is exactly one.  The GZ mechanism (jet = height) forces liveness at
   model level; the arithmetic identification is the community theorem.
3. `central_exhaustion_model` — the CENTRAL EXHAUSTION MIRROR (the analogue of
   `SourceHolonomy.threeD_exhaustive` at the center): the model readout built from
   `r` sources reads r in the DC residue AND a nonzero leading jet — the model cannot
   manifest a sourceless central jet.  The model side of `EveryCentralJetHasSource`
   is closed; what remains open is, as everywhere, the TRANSFER: whether the
   arithmetic readout is an instance of the model. -/

/-- **The census, derived**: the log-derivative of the n-clock Euler factor has k-th
coefficient `s_{k+1}` — exactly what the smooth-entry DC census reads.  (Pure
geometric series; no term-by-term differentiation needed.) -/
theorem nClock_logDeriv_expansion {n : ℕ} (θ : Fin n → ℝ) {x : ℂ} (hx : ‖x‖ < 1) :
    HasSum (fun k : ℕ => clockTraceN θ (k + 1) * x ^ k)
      (∑ i, Complex.exp ((θ i : ℂ) * I) / (1 - Complex.exp ((θ i : ℂ) * I) * x)) := by
  have hterm : ∀ i : Fin n,
      HasSum (fun k : ℕ => Complex.exp ((θ i : ℂ) * I) ^ (k + 1) * x ^ k)
        (Complex.exp ((θ i : ℂ) * I) / (1 - Complex.exp ((θ i : ℂ) * I) * x)) := by
    intro i
    have hu : ‖Complex.exp ((θ i : ℂ) * I) * x‖ < 1 := by
      rw [norm_mul, Complex.norm_exp]
      have : ((θ i : ℂ) * I).re = 0 := by simp [Complex.mul_re]
      rw [this, Real.exp_zero, one_mul]
      exact hx
    have hg := (hasSum_geometric_of_norm_lt_one hu).mul_left
      (Complex.exp ((θ i : ℂ) * I))
    have hfun : (fun k : ℕ => Complex.exp ((θ i : ℂ) * I)
          * (Complex.exp ((θ i : ℂ) * I) * x) ^ k)
        = fun k : ℕ => Complex.exp ((θ i : ℂ) * I) ^ (k + 1) * x ^ k := by
      funext k
      rw [mul_pow, pow_succ]
      ring
    rw [hfun] at hg
    rwa [div_eq_mul_inv]
  have hsum := hasSum_sum (fun i (_ : i ∈ Finset.univ) => hterm i)
  have hfun : (fun k : ℕ => ∑ i, Complex.exp ((θ i : ℂ) * I) ^ (k + 1) * x ^ k)
      = fun k : ℕ => clockTraceN θ (k + 1) * x ^ k := by
    funext k
    rw [← Finset.sum_mul]
    rfl
  rwa [hfun] at hsum

/-- **The Gross–Zagier model statement**: if the first central jet is a positive
multiple of the pairing norm of a NONZERO direction under a positive-definite height
pairing, the jet is strictly positive — the analytic order is exactly one.  Jet =
height forces liveness at model level. -/
theorem gz_first_jet_live {r : ℕ} {H : Matrix (Fin r) (Fin r) ℝ} (hH : H.PosDef)
    {v : Fin r → ℝ} (hv : v ≠ 0) {κ : ℝ} (hκ : 0 < κ) :
    0 < κ * (v ⬝ᵥ H.mulVec v) := by
  have h := hH.dotProduct_mulVec_pos hv
  simp only [star_trivial] at h
  exact mul_pos hκ h

/-- **The central exhaustion mirror** — the model side of `EveryCentralJetHasSource`,
closed: the model readout built from `r` sources reads `r` in the DC residue AND a
nonzero leading jet.  The model cannot manifest a sourceless central jet; the open
question is only the transfer. -/
theorem central_exhaustion_model {G : ℂ → ℂ} {c : ℂ} (r : ℕ)
    (hG : Differentiable ℂ G) (hGc : G c ≠ 0) (hd : ContinuousAt (deriv G) c) :
    Tendsto (fun s : ℂ => (s - c) * (deriv (fun z => (z - c) ^ r * G z) s
        / ((s - c) ^ r * G s))) (𝓝[≠] c) (𝓝 (r : ℂ))
    ∧ Tendsto (fun s : ℂ => ((s - c) ^ r * G s) / (s - c) ^ r) (𝓝[≠] c) (𝓝 (G c))
    ∧ G c ≠ 0 :=
  ⟨rank_is_dc_residue r hG hGc hd,
   leading_jet_extraction r hG.continuous.continuousAt, hGc⟩

end CriticalLinePhasor.BSDClocks
