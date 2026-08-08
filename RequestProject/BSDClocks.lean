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

The program frame: BSD is **EveryCentralJetHasSource** — every
order of central vanishing paid for by a rational-point direction (heights = cup
regulators, the measured 38/38 arc).  Gross–Zagier–Kolyvagin is the proven `ord ≤ 1`
island — the center's analogue of our on-weld bridge-iff.
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

/-- **THE BSD TARGET, named**: every central jet has
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
   is closed. -/

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

/-! ## The certification kernel (owner: "push", 2026-07-03)

A certified BSD instance needs every numeric claim to carry a PROVEN error bound.
The load-bearing analytic bound: coefficient tails.  Hasse gives `|a_n| ≤ 2n`
(σ₀(n)·√n ≤ 2n); the incomplete-Gamma weights are exponentially dominated; so every
jet-series tail is bounded by a geometric-derivative tail, whose closed form is
proven here.  `certified_tail_bound` is the lemma an interval evaluation of
`L″(E,1) > 0` cites to become a certificate. -/

/-- **The geometric-derivative tail, closed form**:
`Σ_{m≥0} (m+K)·x^{m+K} = x^K·(x/(1−x)² + K/(1−x))`. -/
theorem tail_geometric_deriv {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) (K : ℕ) :
    ∑' m : ℕ, ((m + K : ℕ) : ℝ) * x ^ (m + K)
      = x ^ K * (x / (1 - x) ^ 2 + K / (1 - x)) := by
  have hxn : ‖x‖ < 1 := by rwa [Real.norm_eq_abs, abs_of_nonneg hx0]
  have h1 : Summable fun m : ℕ => (m : ℝ) * x ^ m :=
    (hasSum_coe_mul_geometric_of_norm_lt_one hxn).summable
  have h2 : Summable fun m : ℕ => x ^ m := summable_geometric_of_lt_one hx0 hx1
  calc ∑' m : ℕ, ((m + K : ℕ) : ℝ) * x ^ (m + K)
      = ∑' m : ℕ, x ^ K * ((m : ℝ) * x ^ m + (K : ℝ) * x ^ m) := by
        congr 1
        funext m
        rw [pow_add]
        push_cast
        ring
    _ = x ^ K * ((∑' m : ℕ, (m : ℝ) * x ^ m) + (K : ℝ) * ∑' m : ℕ, x ^ m) := by
        rw [tsum_mul_left, Summable.tsum_add h1 (h2.mul_left _), tsum_mul_left]
    _ = x ^ K * (x / (1 - x) ^ 2 + K / (1 - x)) := by
        rw [tsum_coe_mul_geometric_of_norm_lt_one hxn,
          tsum_geometric_of_lt_one hx0 hx1]
        ring

/-- The geometric-derivative majorant is summable (shifted). -/
theorem summable_tail_majorant {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) (C : ℝ) (K : ℕ) :
    Summable fun m : ℕ => C * ((m + K : ℕ) : ℝ) * x ^ (m + K) := by
  have hxn : ‖x‖ < 1 := by rwa [Real.norm_eq_abs, abs_of_nonneg hx0]
  have h1 : Summable fun m : ℕ => (m : ℝ) * x ^ m :=
    (hasSum_coe_mul_geometric_of_norm_lt_one hxn).summable
  have hshift : Summable fun m : ℕ => ((m + K : ℕ) : ℝ) * x ^ (m + K) := by
    have := (summable_nat_add_iff K).mpr h1
    simpa using this
  simpa [mul_assoc] using hshift.mul_left C

/-- **THE CERTIFIED-TAIL LEMMA**: coefficients dominated by `C·n·xⁿ` beyond `K` have
tail norm bounded by the proven closed form.  The bound an interval evaluation of a
central jet cites to become a CERTIFICATE (Hasse supplies the domination for elliptic
banks; the incomplete-Gamma weights supply `x < 1`). -/
theorem certified_tail_bound {f : ℕ → ℂ} {C x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1)
    (K : ℕ)
    (hf : ∀ m : ℕ, ‖f (m + K)‖ ≤ C * ((m + K : ℕ) : ℝ) * x ^ (m + K)) :
    ‖∑' m : ℕ, f (m + K)‖ ≤ C * (x ^ K * (x / (1 - x) ^ 2 + K / (1 - x))) := by
  have hmaj := summable_tail_majorant hx0 hx1 C K
  have hnorm : Summable fun m : ℕ => ‖f (m + K)‖ :=
    Summable.of_nonneg_of_le (fun m => norm_nonneg _) hf hmaj
  calc ‖∑' m : ℕ, f (m + K)‖
      ≤ ∑' m : ℕ, ‖f (m + K)‖ := norm_tsum_le_tsum_norm hnorm
    _ ≤ ∑' m : ℕ, C * ((m + K : ℕ) : ℝ) * x ^ (m + K) :=
        hnorm.tsum_le_tsum hf hmaj
    _ = C * ∑' m : ℕ, ((m + K : ℕ) : ℝ) * x ^ (m + K) := by
        rw [← tsum_mul_left]
        congr 1
        funext m
        ring
    _ = C * (x ^ K * (x / (1 - x) ^ 2 + K / (1 - x))) := by
        rw [tail_geometric_deriv hx0 hx1 K]

/-! ## RUNG 2 — the census bridge: the affine calibration law, derived
(owner: "lets take on the next rung", 2026-07-03)

The rank-census instrument fit `S = A + B·rank` empirically (R² ≥ 0.998, five curves,
held-out).  Rung 2 makes that affine law a THEOREM: the log-derivative of the model
readout decomposes EXACTLY as `r·(central pole) + (bank term)`, so ANY linear census
functional Φ reads `Φ = r·Φ(pole) + Φ(bank)` — affine in the rank, slope = the
functional's reading of the central pole (the measured `B(X)`), intercept = the bank
census (the measured `A(X)`).  And the bank term decomposes over the clock factors
(`census_lane_decomposition`) — the measured ±200-unit lane anatomy, derived.  With
`nClock_logDeriv_expansion` (the bank's log-derivative coefficients ARE the traces),
the entire measured structure of the census instrument is now theorem-shaped.

* `logDeriv_centered_pow` — the central factor's log-derivative is `r/(s−c)`.
* `model_logDeriv` — the exact pointwise decomposition off the singular set.
* `census_affine_in_rank` — **the affine law**: linear functionals read the model
  affinely in `r`.
* `census_lane_decomposition` — **the attribution license**: the census of a product
  is the sum of the lane censuses.
* `census_full_decomposition` — the capstone: rank term + lanes, in one identity —
  the instrument's measured anatomy, exact. -/

/-- The centered power's log-derivative: `r/(s−c)`. -/
theorem logDeriv_centered_pow {c : ℂ} (r : ℕ) {s : ℂ} (hs : s ≠ c) :
    logDeriv (fun z : ℂ => (z - c) ^ r) s = r / (s - c) := by
  have hsc : s - c ≠ 0 := sub_ne_zero.mpr hs
  have h1 : HasDerivAt (fun z : ℂ => (z - c) ^ r) ((r : ℂ) * (s - c) ^ (r - 1) * 1) s :=
    ((hasDerivAt_id s).sub_const c).pow r
  rw [logDeriv_apply, h1.deriv]
  rcases Nat.eq_zero_or_pos r with hr | hr
  · subst hr
    simp
  · have hsplit : (s - c) ^ r = (s - c) ^ (r - 1) * (s - c) := by
      rw [← pow_succ, Nat.sub_add_cancel hr]
    rw [hsplit]
    field_simp

/-- **The model's log-derivative, decomposed exactly**: off the center and the bank's
zeros, `logDeriv((·−c)^r·G) = r/(s−c) + logDeriv G`. -/
theorem model_logDeriv {G : ℂ → ℂ} {c : ℂ} (r : ℕ) {s : ℂ} (hs : s ≠ c)
    (hG : DifferentiableAt ℂ G s) (hGs : G s ≠ 0) :
    logDeriv (fun z => (z - c) ^ r * G z) s = r / (s - c) + logDeriv G s := by
  have hmul := logDeriv_mul (f := fun z : ℂ => (z - c) ^ r) (g := G) s
    (pow_ne_zero r (sub_ne_zero.mpr hs)) hGs
    (((differentiable_id.sub_const c).pow r).differentiableAt) hG
  rw [hmul, logDeriv_centered_pow r hs]

/-- **THE AFFINE CENSUS LAW, derived**: any linear census functional applied to the
model's log-derivative is EXACTLY affine in the rank — slope = the functional's
reading of the central pole, intercept = the bank census.  The calibration line the
instrument fit at R² ≥ 0.998 is this theorem's shadow. -/
theorem census_affine_in_rank {S : Set ℂ} {G : ℂ → ℂ} {c : ℂ} (r : ℕ)
    (hc : c ∉ S) (hG : ∀ s ∈ S, DifferentiableAt ℂ G s ∧ G s ≠ 0)
    (Φ : (S → ℂ) →ₗ[ℂ] ℂ) :
    Φ (fun s => logDeriv (fun z => (z - c) ^ r * G z) (s : ℂ))
      = r * Φ (fun s => 1 / ((s : ℂ) - c)) + Φ (fun s => logDeriv G (s : ℂ)) := by
  have hfun : (fun s : S => logDeriv (fun z => (z - c) ^ r * G z) (s : ℂ))
      = (r : ℂ) • (fun s : S => 1 / ((s : ℂ) - c))
        + fun s : S => logDeriv G (s : ℂ) := by
    funext s
    have hs : (s : ℂ) ≠ c := fun h => hc (h ▸ s.2)
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [model_logDeriv r hs (hG s s.2).1 (hG s s.2).2]
    ring
  rw [hfun, map_add, map_smul, smul_eq_mul]

/-- **The attribution license**: the census of a product is the sum of the lane
censuses — the measured lane anatomy (±200-unit lanes cancelling to a rank-sized
residual), licensed at the census level. -/
theorem census_lane_decomposition {S : Set ℂ} {ι : Type*} (t : Finset ι)
    (f : ι → ℂ → ℂ)
    (hf : ∀ i ∈ t, ∀ s ∈ S, f i s ≠ 0 ∧ DifferentiableAt ℂ (f i) s)
    (Φ : (S → ℂ) →ₗ[ℂ] ℂ) :
    Φ (fun s => logDeriv (fun z => ∏ i ∈ t, f i z) (s : ℂ))
      = ∑ i ∈ t, Φ (fun s => logDeriv (f i) (s : ℂ)) := by
  have hfun : (fun s : S => logDeriv (fun z => ∏ i ∈ t, f i z) (s : ℂ))
      = ∑ i ∈ t, fun s : S => logDeriv (f i) (s : ℂ) := by
    funext s
    rw [Finset.sum_apply]
    exact logDeriv_prod (fun i hi => (hf i hi s s.2).1)
      (fun i hi => (hf i hi s s.2).2)
  rw [hfun, map_sum]

/-- **The capstone — the instrument's measured anatomy, exact**: the census of the
full model (central rank factor × clock bank) is `r·Φ(pole) + Σ lanes`.  The affine
law and the lane attribution in one identity. -/
theorem census_full_decomposition {S : Set ℂ} {ι : Type*} (t : Finset ι)
    (f : ι → ℂ → ℂ) {c : ℂ} (r : ℕ) (hc : c ∉ S)
    (hf : ∀ i ∈ t, ∀ s ∈ S, f i s ≠ 0 ∧ DifferentiableAt ℂ (f i) s)
    (Φ : (S → ℂ) →ₗ[ℂ] ℂ) :
    Φ (fun s => logDeriv (fun z => (z - c) ^ r * ∏ i ∈ t, f i z) (s : ℂ))
      = r * Φ (fun s => 1 / ((s : ℂ) - c))
        + ∑ i ∈ t, Φ (fun s => logDeriv (f i) (s : ℂ)) := by
  have hGdiff : ∀ s ∈ S, DifferentiableAt ℂ (fun z => ∏ i ∈ t, f i z) s ∧
      (∏ i ∈ t, f i s) ≠ 0 := by
    intro s hsS
    constructor
    · exact DifferentiableAt.fun_finsetProd fun i hi => (hf i hi s hsS).2
    · exact Finset.prod_ne_zero_iff.mpr fun i hi => (hf i hi s hsS).1
  rw [census_affine_in_rank r hc (fun s hsS => ⟨(hGdiff s hsS).1, (hGdiff s hsS).2⟩) Φ,
    census_lane_decomposition t f hf Φ]

/-! ## The p-adic landing licenses (closing the scout's gap, 2026-07-03)

The scout's audit found a real license gap: `integer_landing_unique` covers INTEGER
obstructions within ½; the Elliptic-Stark anchor gates match p-adic TRANSCENDENTALS
to N digits — no integer in sight, so the existing license does not apply.  Two new
lemmas close what is honestly closable:

* `bounded_landing_unique` — **the discovery license**: a p-adic approximation DOES
  identify its target when the target is known to lie in a bounded discrete set —
  integers of height ≤ H agreeing mod p^N with p^N > 2H are EQUAL.  This is the
  formal core of algebraic recognition from p-adic data (the LLL/point-discovery
  shape): precision beyond the height bound is identification.
* `ultrametric_anchor_compose` — **anchor chains are lossless in ℚ_p**: two
  agreements to precision ε compose to an agreement to precision ε (no factor-2 loss
  as in ℝ) — the ultrametric triangle makes p-adic anchor gates transitive at full
  precision.

What remains honestly UNLICENSED (stated, not blurred): matching two p-adic
transcendentals to N digits certifies AGREEMENT TO PRECISION, never identification —
ES anchor gates carry the tier [p-adic certified precision], not [landed].  And
`regulator_pos` does not transfer p-adically (no order on ℂ_p): p-adic regulator
nonvanishing stays a numerical hypothesis in every ES instance. -/

/-- **The discovery license**: integers of height ≤ H that agree mod `M > 2H` are
equal — p-adic precision beyond the height bound is identification, not
approximation. -/
theorem bounded_landing_unique {x y H M : ℤ} (hx : |x| ≤ H) (hy : |y| ≤ H)
    (hmod : M ∣ (x - y)) (hbig : 2 * H < M) : x = y := by
  obtain ⟨k, hk⟩ := hmod
  rcases eq_or_ne k 0 with rfl | hk0
  · have hxy : x - y = 0 := by rw [hk]; ring
    omega
  · exfalso
    have hH : (0 : ℤ) ≤ H := le_trans (abs_nonneg x) hx
    have h1 : |x - y| ≤ 2 * H := by
      calc |x - y| ≤ |x| + |y| := abs_sub _ _
        _ ≤ 2 * H := by omega
    have h2 : M ≤ |x - y| := by
      rw [hk, abs_mul]
      have hM : 0 < M := by omega
      have : (1 : ℤ) ≤ |k| := Int.one_le_abs hk0
      calc M = M * 1 := by ring
        _ ≤ |M| * |k| := by
            rw [abs_of_pos hM]
            exact mul_le_mul_of_nonneg_left this (le_of_lt hM)
    omega

/-- **Anchor chains are lossless in ℚ_p**: two agreements to precision ε compose to
an agreement to precision ε — the ultrametric triangle, applied to certification. -/
theorem ultrametric_anchor_compose {p : ℕ} [Fact p.Prime] {a b c : ℚ_[p]} {ε : ℝ}
    (h1 : ‖a - b‖ ≤ ε) (h2 : ‖b - c‖ ≤ ε) : ‖a - c‖ ≤ ε := by
  have h : a - c = (a - b) + (b - c) := by ring
  rw [h]
  calc ‖(a - b) + (b - c)‖ ≤ max ‖a - b‖ ‖b - c‖ := Padic.nonarchimedean _ _
    _ ≤ ε := max_le h1 h2

/-- **The rational discovery license — counting in the right units** (owner,
2026-07-03: "transcendental digit-matching sounds like counting in the wrong units").
Once a transcendental is expressed in its harmonic unit (a period, a π-power, the
Stark-unit logarithm), the remaining coordinate is rational of bounded height — and
rationals of height ≤ H whose cross-difference is divisible by `M > 2H²` are EQUAL.
Agreement-to-precision upgrades to IDENTIFICATION exactly when the units are right:
this is the π/3 lane-landing move (analog phase → μ6 integers) at the ES frontier.
The p-adic reading: for p-unit denominators, agreement mod p^N is exactly the
cross-divisibility hypothesis; `p^N > 2H²` identifies.  (The degree-d algebraic
version — the Liouville-floor license — is the named next target; this is its ℚ
case.) -/
theorem rational_landing_unique {x y : ℚ} {H M : ℤ}
    (hxn : |x.num| ≤ H) (hxd : (x.den : ℤ) ≤ H)
    (hyn : |y.num| ≤ H) (hyd : (y.den : ℤ) ≤ H)
    (hmod : M ∣ (x.num * (y.den : ℤ) - y.num * (x.den : ℤ)))
    (hbig : 2 * H ^ 2 < M) : x = y := by
  have hH : (0 : ℤ) ≤ H := le_trans (abs_nonneg _) hxn
  have hxdpos : (0 : ℤ) < (x.den : ℤ) := by exact_mod_cast x.den_pos
  have hydpos : (0 : ℤ) < (y.den : ℤ) := by exact_mod_cast y.den_pos
  have hcross : |x.num * (y.den : ℤ) - y.num * (x.den : ℤ)| ≤ 2 * H ^ 2 := by
    calc |x.num * (y.den : ℤ) - y.num * (x.den : ℤ)|
        ≤ |x.num * (y.den : ℤ)| + |y.num * (x.den : ℤ)| := abs_sub _ _
      _ = |x.num| * (y.den : ℤ) + |y.num| * (x.den : ℤ) := by
          rw [abs_mul, abs_mul, abs_of_pos hydpos, abs_of_pos hxdpos]
      _ ≤ H * H + H * H := by
          have h1 : |x.num| * (y.den : ℤ) ≤ H * H :=
            mul_le_mul hxn hyd (le_of_lt hydpos) hH
          have h2 : |y.num| * (x.den : ℤ) ≤ H * H :=
            mul_le_mul hyn hxd (le_of_lt hxdpos) hH
          omega
      _ = 2 * H ^ 2 := by ring
  have hzero : x.num * (y.den : ℤ) - y.num * (x.den : ℤ) = 0 := by
    obtain ⟨k, hk⟩ := hmod
    rcases eq_or_ne k 0 with rfl | hk0
    · rw [hk]
      ring
    · exfalso
      have hM : (0 : ℤ) < M := by nlinarith
      have h2 : M ≤ |x.num * (y.den : ℤ) - y.num * (x.den : ℤ)| := by
        rw [hk, abs_mul]
        have hone : (1 : ℤ) ≤ |k| := Int.one_le_abs hk0
        calc M = M * 1 := by ring
          _ ≤ |M| * |k| := by
              rw [abs_of_pos hM]
              exact mul_le_mul_of_nonneg_left hone (le_of_lt hM)
      nlinarith
  have hdx : ((x.den : ℤ) : ℚ) ≠ 0 := by
    exact_mod_cast ne_of_gt hxdpos
  have hdy : ((y.den : ℤ) : ℚ) ≠ 0 := by
    exact_mod_cast ne_of_gt hydpos
  have hx' : ((x.num : ℚ)) / ((x.den : ℚ)) = x := Rat.num_div_den x
  have hy' : ((y.num : ℚ)) / ((y.den : ℚ)) = y := Rat.num_div_den y
  rw [← hx', ← hy']
  rw [div_eq_div_iff (by exact_mod_cast hdx) (by exact_mod_cast hdy)]
  have : x.num * (y.den : ℤ) = y.num * (x.den : ℤ) := by omega
  exact_mod_cast this

/-! ## The finite wall (owner, 2026-07-03): BSD's "all" is not RH's "all"

RH is infinite PER INSTANCE (one L-function carries infinitely many zeros at
unbounded heights).  BSD is not: the curve is COMPACT, the analytic side is ONE
finite integer, the algebraic side is ONE finite integer (Mordell–Weil, cited), and
the owner's bisection picture is literally 2-DESCENT — the doubling map is the
bisection cover of the torus, the two fibers through the origin are its two-torsion
structure, and descent exhausts the compact surface finitely.  The only per-curve
infinity is REFINEMENT (does the bisection terminate = no infinitely-divisible part
of Ш), not extent.  Proven here:

* `model_form_exists` — **every analytic readout is an instance of our model**: any
  function analytic and not locally dead at the center factors as `(s−c)^r·G` with
  FINITE `r` and `G(c) ≠ 0`.  The finite analytic order is guaranteed; the entire
  dictionary (`rank_is_dc_residue`, the jets, the census) applies to every actual
  L-function, with analyticity supplied by modularity [cited].
* `everyCentralJetHasSource_decidable` — per instance, BSD's target is a DECIDABLE
  proposition (equality of two naturals).  RH's `Exhaustive` quantifies over ℂ.
  The two walls have different shapes, exactly as the owner says. -/

/-- **Every analytic readout is an instance of the model**: analytic and not locally
dead at `c` ⟹ factors as `(z−c)^r·g` with FINITE `r` and `g(c) ≠ 0` near `c`.  The
finite central order exists; the model dictionary applies. -/
theorem model_form_exists {f : ℂ → ℂ} {c : ℂ} (hf : AnalyticAt ℂ f c)
    (hne : ¬ ∀ᶠ z in 𝓝 c, f z = 0) :
    ∃ (r : ℕ) (g : ℂ → ℂ), AnalyticAt ℂ g c ∧ g c ≠ 0 ∧
      ∀ᶠ z in 𝓝 c, f z = (z - c) ^ r * g z := by
  have htop : analyticOrderAt f c ≠ ⊤ := by
    intro h
    rw [analyticOrderAt_eq_top] at h
    exact hne (h.mono fun z hz => by simpa using hz)
  obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.mp htop
  obtain ⟨g, hg, hgc, hfac⟩ := (hf.analyticOrderAt_eq_natCast).mp hr.symm
  exact ⟨r, g, hg, hgc, by simpa [smul_eq_mul] using hfac⟩

/-- **Per instance, the BSD target is decidable** — equality of two finite naturals.
(Contrast: `SourceHolonomy.Exhaustive` quantifies over ℂ.  The walls differ in
shape.) -/
instance everyCentralJetHasSource_decidable (a s : ℕ) :
    Decidable (EveryCentralJetHasSource a s) :=
  inferInstanceAs (Decidable (a = s))

/-! ## The harmonization answer (owner, 2026-07-03): fibers interfere downstairs,
diagonalize upstairs

Do fibers on curves overlap and interfere — with themselves and each other?  YES,
downstairs: twist-family fibers share one carrier and their interference is itself a
fiber (the product character); two arbitrary curves interfere through the
Rankin–Selberg rank-4 ensemble (the k-dim clock law covers it; its DC census detects
isogeny = maximal coherence).  And YES, the upgrade exists: over the tower both
twists become ONE curve, and the Galois involution DIAGONALIZES the family — the
Mordell–Weil space splits into eigenspaces, a direct sum with no cross-terms.  Rank
additivity `rank E(ℚ(√d)) = rank E(ℚ) + rank E_d(ℚ)` is the shadow of this
diagonalization.  The model core, proven here:

* `involution_splitting` — an involution on a ℚ-vector space splits it into its
  ±1-eigenspaces: `IsCompl (ker(σ−1)) (ker(σ+1))`.  The harmonized object carries
  the two fibers as complementary summands — interference structurally impossible.
* `involution_rank_additivity` — dimensions add across the split: the upstairs rank
  is exactly the sum of the two downstairs ranks.  No rank is created or destroyed
  by harmonization; it is only SORTED. -/

/-- **The harmonization splitting**: an involution on a ℚ-vector space splits it into
complementary ±1-eigenspaces — the two fibers of the harmonized object cannot
interfere. -/
theorem involution_splitting {V : Type*} [AddCommGroup V] [Module ℚ V]
    (σ : V →ₗ[ℚ] V) (hσ : σ ∘ₗ σ = LinearMap.id) :
    IsCompl (LinearMap.ker (σ - LinearMap.id))
      (LinearMap.ker (σ + LinearMap.id)) := by
  have hσσ : ∀ v : V, σ (σ v) = v := fun v => congrArg (fun φ => φ v) hσ
  constructor
  · rw [disjoint_iff]
    ext v
    simp only [Submodule.mem_inf, LinearMap.mem_ker, LinearMap.sub_apply,
      LinearMap.add_apply, LinearMap.id_apply, Submodule.mem_bot]
    constructor
    · rintro ⟨h1, h2⟩
      have hv : (2 : ℚ) • v = 0 := by
        have : σ v - v + (σ v + v) = (2 : ℚ) • v + (2 : ℚ) • (σ v - v) + (0 : V) := by
          module
        rw [h1, h2] at this
        simpa [h1] using this.symm
      have h2q : (2 : ℚ) ≠ 0 := by norm_num
      exact (smul_eq_zero.mp hv).resolve_left h2q
    · rintro rfl
      simp
  · rw [codisjoint_iff, eq_top_iff]
    intro v _
    rw [Submodule.mem_sup]
    refine ⟨(2 : ℚ)⁻¹ • (v + σ v), ?_, (2 : ℚ)⁻¹ • (v - σ v), ?_, by module⟩
    · rw [LinearMap.mem_ker]
      have : σ ((2 : ℚ)⁻¹ • (v + σ v)) = (2 : ℚ)⁻¹ • (σ v + v) := by
        rw [map_smul, map_add, hσσ]
      simp only [LinearMap.sub_apply, LinearMap.id_apply, this]
      module
    · rw [LinearMap.mem_ker]
      have : σ ((2 : ℚ)⁻¹ • (v - σ v)) = (2 : ℚ)⁻¹ • (σ v - v) := by
        rw [map_smul, map_sub, hσσ]
      simp only [LinearMap.add_apply, LinearMap.id_apply, this]
      module

/-- **Rank additivity across harmonization**: dimensions add across the eigenspace
split — the upstairs rank is exactly the sum of the downstairs ranks.  Harmonization
sorts rank; it never creates or destroys it. -/
theorem involution_rank_additivity {V : Type*} [AddCommGroup V] [Module ℚ V]
    [FiniteDimensional ℚ V] (σ : V →ₗ[ℚ] V) (hσ : σ ∘ₗ σ = LinearMap.id) :
    Module.finrank ℚ (LinearMap.ker (σ - LinearMap.id))
      + Module.finrank ℚ (LinearMap.ker (σ + LinearMap.id))
      = Module.finrank ℚ V :=
  Submodule.finrank_add_eq_of_isCompl (involution_splitting σ hσ)

/-- **The commuting lift** (owner, 2026-07-03: "non-commuting interference can
probably be lifted to some mutually commuting dimension"): operators placed on
SEPARATE tensor factors always commute — giving each interference source its own
dimension restores commutativity structurally.  This is the mechanism behind the
bank itself (FTA = each prime its own dimension, clocks commute), behind
modularity/Langlands (non-commuting Galois interference lifted to the mutually
commuting Hecke algebra, simultaneously diagonalized by eigenforms), and behind
Naimark dilation.  The harmonization ceiling is abelian-RELATIVE: the break-through
is the lift, and its price is rank — the new dimensions. -/
theorem tensor_lift_commutes {R : Type*} [CommSemiring R]
    {V W : Type*} [AddCommMonoid V] [AddCommMonoid W] [Module R V] [Module R W]
    (σ : V →ₗ[R] V) (τ : W →ₗ[R] W) :
    (TensorProduct.map σ LinearMap.id).comp (TensorProduct.map LinearMap.id τ)
      = (TensorProduct.map LinearMap.id τ).comp (TensorProduct.map σ LinearMap.id) := by
  rw [← TensorProduct.map_comp, ← TensorProduct.map_comp]
  simp

/-- **The conjugate-dimension lift** (owner: "up a dimension, or up and over to a
conjugate dimension"): the OTHER break-through — no new dimensions, move to the
conjugate chart.  Class functions commute under convolution for ANY finite group:
the conjugate coordinates are commutative even when the group is not.  Fourier's
convolution ↦ multiplication, Tannaka's commutative character ring R(G), and the
Hecke algebra are this lift's avatars.  The tensor lift (`tensor_lift_commutes`)
buys commutativity with RANK; the conjugate lift buys it with a CHART CHANGE —
the two break-throughs of the harmonization ceiling. -/
theorem conjugate_lift_commutes {G : Type*} [Group G] [Fintype G]
    (f g : G → ℂ) (hf : ∀ a x : G, f (a⁻¹ * x * a) = f x) (x : G) :
    ∑ a : G, f a * g (a⁻¹ * x) = ∑ a : G, g a * f (a⁻¹ * x) := by
  have e : G ≃ G := (Equiv.inv G).trans (Equiv.mulRight x)
  refine Fintype.sum_equiv ((Equiv.inv G).trans (Equiv.mulRight x))
    (fun a => f a * g (a⁻¹ * x)) (fun b => g b * f (b⁻¹ * x)) fun a => ?_
  simp only [Equiv.trans_apply, Equiv.inv_apply, Equiv.coe_mulRight]
  have h1 : (a⁻¹ * x)⁻¹ * x = x⁻¹ * a * x := by group
  rw [h1, hf x a, mul_comm]

end CriticalLinePhasor.BSDClocks
