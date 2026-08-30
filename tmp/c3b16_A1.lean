import c3b15_A2

/-!
# C3 batch 16, block A1 — the monotonicity package, and the adaptive-window exclusion

## What batch 15 claimed and what it actually proved

Batch 15's ledger said the uniform choice `a = a(x)` "**PROVABLY DOES NOT EXIST** for this
instrument, by two compiled theorems".  **That overstated the compiled content.**
`C3B15.criterion_forces_x_bound` gives, for each **fixed** `a` with `Qwin a > 0`, a cap
`x² ≤ mass/(2·Qwin a)`.  That is `∀a ∃cap`, not `∃cap ∀a`, and it leaves open an adaptive
`a(x)` whose cap grows with `x`.  Relabelled UNCOMPILED there; this block supplies what is
missing.

## What is proved here

Three structural facts, all from `Rker ≥ 0` and set inclusion, none touching the target:

* `Tail_antitone` — the tail mass is antitone;
* `Qwin_mono` — the window second moment is monotone on `a ≥ 0`;
* `Qwin_ge_annulus` — **`2c²(Tail c − Tail a) ≤ Qwin a`** for `0 ≤ c ≤ a`, because on the
  annulus `c ≤ |v| < a` one has `v² ≥ c²` and that annulus carries mass `2(Tail c − Tail a)`.

Together with `Tail_zero : Tail 0 = mass/2`, these give the exclusion in the exact quantifier
order that was missing — **`∃cap ∀a`** — from a single explicit numeric witness:

`no_adaptive_window_of_witness`: if some `c > 0` has `mass/4 < Tail c`, then **every** `a`
admissible for the criterion (`4·Tail a ≤ mass`) satisfies `x² ≤ mass/(2·2c²(Tail c − mass/4))`
— a bound independent of `a`.  No adaptive window can escape it.

The witness is the one remaining input.  Measured (`tmp/c3b16_num1_out.txt` §M2):
`Tail 0 = 5.70991541722184e−03 = mass/2` to `reldiff 0.00`, and `Tail(0.05) = 4.168e−03`
against `mass/4 = 2.855e−03`, so `c = 0.05` is a witness with room to spare; the largest
tested witness is `c = 0.095`.  **That inequality is numerically verified and NOT formalised**
— it is a quantitative fact about `R` requiring certified numerics, and it is named here
rather than assumed silently.

## A minorant-class kill, compiled

`reject_shifted_minorant` records why `cos z ≥ 2e^{−βz²} − 2` — true for every `β > 0` — is
useless: any minorant of the form `2m − 2` with `m ≤ 1` assembles to something `≤ −2·Tail a`,
hence never positive.  Verified numerically first (§G0: nonpositive at every sampled `(a,x)`,
and identically `0` in the central part at `x = 0` where the truth is `W(a) > 0`).

SCOPE: monotonicity, one annulus bound, one conditional exclusion, one instrument kill.
-/

open MeasureTheory Set Filter Topology

noncomputable section

namespace C3B16

open C3B10
open C3B14
open C3B15

/-! ### 1. Monotonicity -/

/-- The tail mass is antitone: a larger cut-off leaves less mass. -/
theorem Tail_antitone {a b : ℝ} (hab : a ≤ b) : Tail b ≤ Tail a := by
  unfold Tail
  refine setIntegral_mono_set Rker_integrable.integrableOn ?_ ?_
  · filter_upwards with v using Rker_nonneg v
  · exact HasSubset.Subset.eventuallyLE (Ioi_subset_Ioi hab)

/-- The window second moment is monotone on `a ≥ 0`. -/
theorem Qwin_mono {a b : ℝ} (_ha : 0 ≤ a) (hab : a ≤ b) : Qwin a ≤ Qwin b := by
  unfold Qwin
  refine setIntegral_mono_set (sq_Rker_integrableOn b) ?_ ?_
  · filter_upwards with v
    have := Rker_nonneg v
    positivity
  · refine HasSubset.Subset.eventuallyLE (Ioo_subset_Ioo ?_ hab)
    linarith

/-- `Tail 0` is half the total mass, by evenness. -/
theorem Tail_zero : Tail 0 = cosMom Rker 0 / 2 := by
  have h := window_mass 0 le_rfl
  have hz : (∫ v in Ioo (-(0:ℝ)) 0, Rker v) = 0 := by
    simp
  rw [hz] at h
  unfold Tail
  linarith [h]

/-! ### 2. THE ANNULUS LOWER BOUND -/

/-- **THE ANNULUS BOUND.**  On `c ≤ |v| < a` one has `v² ≥ c²`, and that annulus carries mass
`2(Tail c − Tail a)`.  Hence `Qwin a ≥ 2c²(Tail c − Tail a)`.  This is the ingredient that
converts the per-`a` cap into a uniform one. -/
theorem Qwin_ge_annulus {c a : ℝ} (hc : 0 ≤ c) (hca : c ≤ a) :
    2 * c ^ 2 * (Tail c - Tail a) ≤ Qwin a := by
  have ha : (0:ℝ) ≤ a := le_trans hc hca
  have hsub : Ioo (-c) c ⊆ Ioo (-a) a := Ioo_subset_Ioo (by linarith) hca
  have hI : IntegrableOn (fun v : ℝ => v ^ 2 * Rker v) (Ioo (-a) a) := sq_Rker_integrableOn a
  have hR : IntegrableOn Rker (Ioo (-a) a) := Rker_integrable.integrableOn
  -- split the window into the inner disc and the annulus
  have hsplit : (∫ v in Ioo (-a) a ∩ Ioo (-c) c, v ^ 2 * Rker v)
      + (∫ v in Ioo (-a) a \ Ioo (-c) c, v ^ 2 * Rker v)
      = ∫ v in Ioo (-a) a, v ^ 2 * Rker v :=
    integral_inter_add_diff measurableSet_Ioo hI
  have hsplitR : (∫ v in Ioo (-a) a ∩ Ioo (-c) c, Rker v)
      + (∫ v in Ioo (-a) a \ Ioo (-c) c, Rker v)
      = ∫ v in Ioo (-a) a, Rker v :=
    integral_inter_add_diff measurableSet_Ioo hR
  have hint : Ioo (-a) a ∩ Ioo (-c) c = Ioo (-c) c := inter_eq_self_of_subset_right hsub
  rw [hint] at hsplit hsplitR
  -- on the annulus `v² ≥ c²`
  have hann : c ^ 2 * (∫ v in Ioo (-a) a \ Ioo (-c) c, Rker v)
      ≤ ∫ v in Ioo (-a) a \ Ioo (-c) c, v ^ 2 * Rker v := by
    rw [← integral_const_mul]
    refine integral_mono_ae ((hR.mono_set diff_subset).const_mul _)
      (hI.mono_set diff_subset) ?_
    filter_upwards [ae_restrict_mem (measurableSet_Ioo.diff measurableSet_Ioo)] with v hv
    have hRn : 0 ≤ Rker v := Rker_nonneg v
    have hcv : c ^ 2 ≤ v ^ 2 := by
      rcases not_and_or.mp (fun h => hv.2 ⟨h.1, h.2⟩) with h | h
      · have : v ≤ -c := le_of_not_gt h
        nlinarith [hc]
      · have : c ≤ v := le_of_not_gt h
        nlinarith [hc]
    nlinarith [hcv, hRn]
  -- the annulus mass, from `window_mass`
  have hmassA := window_mass a ha
  have hmassC := window_mass c hc
  have hdiffR : (∫ v in Ioo (-a) a \ Ioo (-c) c, Rker v) = 2 * (Tail c - Tail a) := by
    unfold Tail at hmassA hmassC ⊢
    linarith [hsplitR, hmassA, hmassC]
  have hQc : 0 ≤ ∫ v in Ioo (-c) c, v ^ 2 * Rker v := Qwin_nonneg c
  unfold Qwin
  rw [hdiffR] at hann
  linarith [hsplit, hann, hQc]

/-! ### 3. THE ADAPTIVE-WINDOW EXCLUSION, in the correct quantifier order -/

/-- **`∃cap ∀a`.**  Given one explicit `c > 0` with `mass/4 < Tail c`, every `a` admissible
for the criterion obeys the SAME cap.  No adaptive `a(x)` escapes it.

The witness hypothesis `mass/4 < Tail c` is the single remaining input; it is a quantitative
fact about `R`, numerically verified (`c = 0.05`: `Tail c = 4.168e−03` against
`mass/4 = 2.855e−03`) and **not formalised**. -/
theorem no_adaptive_window_of_witness {c : ℝ} (hc : 0 < c)
    (hw : cosMom Rker 0 / 4 < Tail c) {a x : ℝ} (_ha : 0 ≤ a)
    (hadm : 4 * Tail a ≤ cosMom Rker 0)
    (hcrit : 2 * x ^ 2 * Qwin a + 4 * Tail a ≤ cosMom Rker 0) :
    x ^ 2 ≤ cosMom Rker 0 / (2 * (2 * c ^ 2 * (Tail c - cosMom Rker 0 / 4))) := by
  have hTa : Tail a ≤ cosMom Rker 0 / 4 := by linarith [hadm]
  -- admissibility forces `c ≤ a`, via antitonicity
  have hca : c ≤ a := by
    by_contra hlt
    push_neg at hlt
    have := Tail_antitone (le_of_lt hlt)
    linarith [hTa, hw, this]
  -- the uniform lower bound on `Qwin a`
  have hQ : 2 * c ^ 2 * (Tail c - cosMom Rker 0 / 4) ≤ Qwin a := by
    have h1 := Qwin_ge_annulus (le_of_lt hc) hca
    have h2 : 2 * c ^ 2 * (Tail c - cosMom Rker 0 / 4)
        ≤ 2 * c ^ 2 * (Tail c - Tail a) := by
      have : (0:ℝ) ≤ 2 * c ^ 2 := by positivity
      nlinarith [hTa, this]
    linarith [h1, h2]
  have hQpos : 0 < 2 * c ^ 2 * (Tail c - cosMom Rker 0 / 4) := by
    have h1 : (0:ℝ) < 2 * c ^ 2 := by positivity
    have h2 : (0:ℝ) < Tail c - cosMom Rker 0 / 4 := by linarith [hw]
    positivity
  have hT0 : 0 ≤ 4 * Tail a := by
    have := Tail_nonneg a
    linarith
  have hmain : 2 * x ^ 2 * (2 * c ^ 2 * (Tail c - cosMom Rker 0 / 4)) ≤ cosMom Rker 0 := by
    have hx2 : (0:ℝ) ≤ 2 * x ^ 2 := by positivity
    nlinarith [hcrit, hQ, hx2, hT0]
  rw [le_div_iff₀ (by linarith : (0:ℝ) < 2 * (2 * c ^ 2 * (Tail c - cosMom Rker 0 / 4)))]
  linarith [hmain]

/-! ### 4. A MINORANT-CLASS KILL

`cos z ≥ 2e^{−βz²} − 2` is a true pointwise inequality for every `β > 0`, and it is useless.
The reason is not about Gaussians: **any** minorant of the shape `2m − 2` with `m ≤ 1`
assembles, against a nonnegative kernel, to at most `−2·Tail a`. -/

/-- **THE KILL.**  If `g ≤ w` pointwise on the window (here `g` is the minorant's integral and
`w` the window mass), the assembled criterion `2g − 2w − 2T` is at most `−2T ≤ 0`.  So no
minorant of the form `2m − 2` with `m ≤ 1` can ever produce a positive criterion. -/
theorem reject_shifted_minorant {g w T : ℝ} (hgw : g ≤ w) (hT : 0 ≤ T) :
    2 * g - 2 * w - 2 * T ≤ 0 := by linarith

/-- And at `x = 0` the loss is total: the minorant contributes `0` where the true central
integral is the whole window mass. -/
theorem reject_shifted_minorant_at_zero {w T : ℝ} (hT : 0 ≤ T) :
    2 * w - 2 * w - 2 * T ≤ 0 := by linarith

end C3B16

section AxiomAudit
#print axioms C3B16.Tail_antitone
#print axioms C3B16.Qwin_mono
#print axioms C3B16.Tail_zero
#print axioms C3B16.Qwin_ge_annulus
#print axioms C3B16.no_adaptive_window_of_witness
#print axioms C3B16.reject_shifted_minorant
#print axioms C3B16.reject_shifted_minorant_at_zero
end AxiomAudit
