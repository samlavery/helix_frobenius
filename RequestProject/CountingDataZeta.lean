/-
Consumes results from https://github.com/anthropics/zeta-23-lean
at commit 3635e74826a4c1fcece7d1cd2b6fa75e43a00510 (Lean v4.33.0-rc2), registered as the
Lake path dependency `Zeta23` (see lakefile.toml).
Copyright the zeta-23-lean contributors, Anthropic PBC; Apache License 2.0
(http://www.apache.org/licenses/LICENSE-2.0).

Imported, not ported — nothing is copied into this file.  The upstream results consumed are:

* `Zeta23.riemannVonMangoldt_zeta`  (Zeta23/Final.lean, line 235) — an UNCONDITIONAL
  `RiemannVonMangoldt zetaZeroConfig`.  Its `main` field reads
  `|N(T,2T) − (T/2π)·ell1 T| ≤ C·log T`  for `T ≥ T₀`,
  with `ell1 T = log(T/2π) + 2·log 2 − 1` (`Zeta23.ell1`, Zeta23/Defs.lean, line 52).
  It is unconditional because `Zeta23.gammaFacts` (Zeta23/GammaFacts/Complete.lean, line 30)
  is proved outright from `Zeta23.StirlingVert.mu_stirling`.
* `Zeta23.Assembly.dyadic`  (Zeta23/Assembly.lean, line 592) — the dyadic-window to cumulative
  transfer for interval-additive nonnegative counts.
* `Zeta23.tendsto_Ncount_zero_atTop`  (Zeta23/Main.lean, line 34).
* `Zeta23.Ncount_add`  (Zeta23/RvM/NcountWindow.lean, line 34) — window additivity.
* `Zeta23.zetaZeroConfig_N`  (Zeta23/Statement/SeamClosed.lean, line 31).
-/
import Zeta23.Final
import Zeta23.Main
import RequestProject.AccumulatedDefect

/-!
# A first inhabitant of `CountingData`: ζ's cumulative zero census

`AccumulatedDefect.lean` states `accumulated_defect_positive` over the structure `CountingData`,
which had **no instances anywhere in this tree** — the structure, the theorem, and one docstring
mention were its only occurrences, so the theorem was vacuous.  This file builds the first
instance, unconditionally, from Zeta23's Riemann–von Mangoldt formula for ζ.

## The normalization, with the `T`-order term booked explicitly

Zeta23's RvM is a **dyadic window** count; `CountingData.N` is **cumulative**.  Writing
`G(T) := (1/2π)·T·log T` for the cumulative profile, the dyadic increment of `G` and the RvM
main term differ by an exact `T`-order term, which is *not* absorbed into an error:

  `G(2t) − G(t) = (1/2π)·(t·log t + 2t·log 2)`,
  `(t/2π)·ell1 t = (1/2π)·(t·log t + 2t·log 2 − t·(log 2π + 1))`,

so, with `κ := log(2π) + 1`,

  `G(2t) − G(t) − (t/2π)·ell1 t = κ·t/(2π)`   exactly   (`profileDiff_sub_main`).

That `κ·t/(2π)` is the whole of the `ell1`-versus-`log` mismatch.  It is `O(t)`, hence
`o(t·log t)`, so it is invisible at the resolution `CountingData` asks for — but it is the
reason the cumulative constant is `1/(2π)` and not something else, and it is what makes the
telescoped main term come out as the classical `(T/2π)(log(T/2π) − 1)` rather than
`(T/2π)·log T`.  Summing the dyadic windows, the `log 2` contributions cancel in the limit
(`Σ_{k≥0} 2^{−(k+1)}(1−k) = 0`), which is why `cmain = 1/(2π)`.

## Harmonic content

The census's own scale is `T·log T`, never unit `1`.  The DC mode is `(1/2π)·T·log T` and is
evaluated exactly; there are two distinct AC layers, and they are kept apart: a genuine
`T`-order term `κ·T/(2π)` from the chart mismatch above, and the `O(log T)` RvM fluctuation.
Both are `o(T·log T)`, but only after being computed — neither is estimated away up front.
The difficulty is entirely in the chart: transferring a dyadic reading to a cumulative one.

## Scope

See `zeta_countingData` for what is proved and `accumulated_defect_zeta_inapplicable` for the
honest statement of what `accumulated_defect_positive` does and does not yield from it.
-/

namespace CriticalLinePhasor.AccumulatedDefect

namespace ZetaCounting

open Filter Topology

/-! ## The cumulative main-term profile -/

/-- `G(T) = (1/2π)·T·log T`, clamped constant below height `3`.  The clamp is what makes `G`
monotone on all of `ℝ`: `Real.log` is even, so `T·log T` is not monotone near the origin, and
`Zeta23.Assembly.dyadic` demands nonnegativity of the interval form at *every* pair. -/
noncomputable def mainProfile (T : ℝ) : ℝ :=
  (1 / (2 * Real.pi)) * (max T 3 * Real.log (max T 3))

lemma mainProfile_eq {T : ℝ} (hT : 3 ≤ T) :
    mainProfile T = (1 / (2 * Real.pi)) * (T * Real.log T) := by
  rw [mainProfile, max_eq_left hT]

lemma mainProfile_mono : Monotone mainProfile := by
  intro a b hab
  have h3a : (3 : ℝ) ≤ max a 3 := le_max_right _ _
  have h3b : (3 : ℝ) ≤ max b 3 := le_max_right _ _
  have hm : max a 3 ≤ max b 3 := max_le_max hab le_rfl
  have hla : 0 ≤ Real.log (max a 3) := Real.log_nonneg (by linarith)
  have hlm : Real.log (max a 3) ≤ Real.log (max b 3) := Real.log_le_log (by linarith) hm
  have hmul : max a 3 * Real.log (max a 3) ≤ max b 3 * Real.log (max b 3) :=
    mul_le_mul hm hlm hla (by linarith)
  have hπ : (0 : ℝ) ≤ 1 / (2 * Real.pi) := by positivity
  exact mul_le_mul_of_nonneg_left hmul hπ

lemma mainProfile_nonneg (T : ℝ) : 0 ≤ mainProfile T := by
  have h3 : (3 : ℝ) ≤ max T 3 := le_max_right _ _
  have : 0 ≤ Real.log (max T 3) := Real.log_nonneg (by linarith)
  have hπ : (0 : ℝ) ≤ 1 / (2 * Real.pi) := by positivity
  exact mul_nonneg hπ (mul_nonneg (by linarith) this)

/-- The interval form of the profile: nonnegative at *every* pair, additive on ordered triples. -/
noncomputable def profileDiff (a b : ℝ) : ℝ := mainProfile (max a b) - mainProfile a

lemma profileDiff_nonneg (a b : ℝ) : 0 ≤ profileDiff a b :=
  sub_nonneg.mpr (mainProfile_mono (le_max_left a b))

lemma profileDiff_of_le {a b : ℝ} (h : a ≤ b) :
    profileDiff a b = mainProfile b - mainProfile a := by
  rw [profileDiff, max_eq_right h]

lemma profileDiff_add {a b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c) :
    profileDiff a c = profileDiff a b + profileDiff b c := by
  rw [profileDiff_of_le (hab.trans hbc), profileDiff_of_le hab, profileDiff_of_le hbc]
  ring

/-! ## The chart mismatch, computed exactly -/

/-- `κ = log(2π) + 1`: the exact coefficient of the `T`-order term separating the cumulative
profile's dyadic increment from the RvM main term. -/
noncomputable def kappa : ℝ := Real.log (2 * Real.pi) + 1

lemma one_le_kappa : 1 ≤ kappa := by
  have hπ := Real.pi_gt_three
  have : (0 : ℝ) ≤ Real.log (2 * Real.pi) := Real.log_nonneg (by linarith)
  rw [kappa]; linarith

/-- **The mismatch, exactly.**  `G(2t) − G(t) − (t/2π)·ell1 t = κ·t/(2π)`. -/
lemma profileDiff_sub_main {t : ℝ} (ht : 3 ≤ t) :
    profileDiff t (2 * t) - t / (2 * Real.pi) * Zeta23.ell1 t = kappa * t / (2 * Real.pi) := by
  have ht0 : (0 : ℝ) < t := by linarith
  have h2t : (3 : ℝ) ≤ 2 * t := by linarith
  have hle : t ≤ 2 * t := by linarith
  have hπ : (0 : ℝ) < 2 * Real.pi := by positivity
  rw [profileDiff_of_le hle, mainProfile_eq h2t, mainProfile_eq ht, Zeta23.ell1, Zeta23.l,
    Real.log_div ht0.ne' hπ.ne', Real.log_mul two_ne_zero ht0.ne', kappa]
  field_simp
  ring

/-! ## Elementary size lemmas -/

lemma log_le_two_sqrt {t : ℝ} (ht : 0 < t) : Real.log t ≤ 2 * Real.sqrt t := by
  have hs : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht
  have h1 : Real.log (Real.sqrt t) ≤ Real.sqrt t - 1 := Real.log_le_sub_one_of_pos hs
  have h2 : Real.log (Real.sqrt t) = Real.log t / 2 := Real.log_sqrt ht.le
  linarith

/-- `c·log t ≤ t` once `t ≥ (2c)²`. -/
lemma mul_log_le_self {c t : ℝ} (hc : 0 ≤ c) (ht1 : 1 ≤ t) (ht : (2 * c) ^ 2 ≤ t) :
    c * Real.log t ≤ t := by
  have ht0 : (0 : ℝ) < t := by linarith
  have hsq : Real.sqrt t * Real.sqrt t = t := Real.mul_self_sqrt ht0.le
  have h2c : 2 * c ≤ Real.sqrt t := by
    have h := Real.sqrt_le_sqrt ht
    rwa [Real.sqrt_sq (by positivity)] at h
  calc c * Real.log t ≤ c * (2 * Real.sqrt t) :=
        mul_le_mul_of_nonneg_left (log_le_two_sqrt ht0) hc
    _ = 2 * c * Real.sqrt t := by ring
    _ ≤ Real.sqrt t * Real.sqrt t := mul_le_mul_of_nonneg_right h2c (Real.sqrt_nonneg t)
    _ = t := hsq

/-! ## Riemann–von Mangoldt, normalized -/

/-- Zeta23's RvM for ζ, repackaged with a nonnegative constant and a threshold above `3`. -/
lemma rvm_zeta : ∃ C T₀ : ℝ, 0 ≤ C ∧ 3 ≤ T₀ ∧ ∀ T : ℝ, T₀ ≤ T →
    |(Zeta23.Ncount T (2 * T) : ℝ) - T / (2 * Real.pi) * Zeta23.ell1 T| ≤ C * Real.log T := by
  obtain ⟨C, T₀, h⟩ := Zeta23.riemannVonMangoldt_zeta.main
  refine ⟨|C|, max T₀ 3, abs_nonneg C, le_max_right _ _, fun T hT => ?_⟩
  have h1 : T₀ ≤ T := le_trans (le_max_left _ _) hT
  have h3 : (3 : ℝ) ≤ T := le_trans (le_max_right _ _) hT
  have hlog : 0 ≤ Real.log T := Real.log_nonneg (by linarith)
  have hb := h T h1
  simp only [Zeta23.zetaZeroConfig_N] at hb
  exact hb.trans (mul_le_mul_of_nonneg_right (le_abs_self C) hlog)

/-! ## The two dyadic comparisons -/

/-- Upper dyadic comparison: the window census never exceeds the profile increment, once `t` is
large enough that the `O(log t)` RvM fluctuation is dominated by the `κ·t/(2π)` mismatch. -/
lemma dyadic_upper (ε : ℝ) (_hε : 0 < ε) :
    ∃ T₁ : ℝ, ∀ t : ℝ, T₁ ≤ t →
      (1 - ε) * (Zeta23.Ncount t (2 * t) : ℝ) ≤ profileDiff t (2 * t) := by
  obtain ⟨C, T₀, hC0, hT₀3, hrvm⟩ := rvm_zeta
  refine ⟨max T₀ ((2 * (2 * Real.pi * C)) ^ 2 + 1), fun t ht => ?_⟩
  have htT₀ : T₀ ≤ t := le_trans (le_max_left _ _) ht
  have ht3 : (3 : ℝ) ≤ t := le_trans hT₀3 htT₀
  have ht1 : (1 : ℝ) ≤ t := by linarith
  have htsq : (2 * (2 * Real.pi * C)) ^ 2 ≤ t := by
    have := le_trans (le_max_right _ _) ht; linarith
  have hπ : (0 : ℝ) < 2 * Real.pi := by positivity
  have hNn : (0 : ℝ) ≤ (Zeta23.Ncount t (2 * t) : ℝ) := Nat.cast_nonneg _
  -- `2πC·log t ≤ t ≤ κ·t`
  have hkey : C * Real.log t ≤ kappa * t / (2 * Real.pi) := by
    have h1 : 2 * Real.pi * C * Real.log t ≤ t :=
      mul_log_le_self (by positivity) ht1 htsq
    have h2 : t ≤ kappa * t := by nlinarith [one_le_kappa, ht3]
    rw [le_div_iff₀ hπ]
    nlinarith
  have hgap := profileDiff_sub_main ht3
  have hupper : (Zeta23.Ncount t (2 * t) : ℝ) ≤ profileDiff t (2 * t) := by
    have h := (abs_le.mp (hrvm t htT₀)).2
    linarith
  nlinarith [hNn, hupper]

/-- Lower dyadic comparison: the window census is at least `(1−ε)` of the profile increment,
once `t` is large enough that `ε·t·log t` swallows both the `κ·t/(2π)` mismatch and the
`O(log t)` fluctuation. -/
lemma dyadic_lower (ε : ℝ) (hε : 0 < ε) :
    ∃ T₁ : ℝ, ∀ t : ℝ, T₁ ≤ t →
      (1 - ε) * profileDiff t (2 * t) ≤ (Zeta23.Ncount t (2 * t) : ℝ) := by
  obtain ⟨C, T₀, hC0, hT₀3, hrvm⟩ := rvm_zeta
  refine ⟨max (max T₀ (Real.exp (2 * kappa / ε)))
      ((2 * (2 * Real.pi * C * 2 / ε)) ^ 2 + 1), fun t ht => ?_⟩
  have htT₀ : T₀ ≤ t := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) ht
  have htexp : Real.exp (2 * kappa / ε) ≤ t :=
    le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) ht
  have ht3 : (3 : ℝ) ≤ t := le_trans hT₀3 htT₀
  have ht1 : (1 : ℝ) ≤ t := by linarith
  have ht0 : (0 : ℝ) < t := by linarith
  have hlogone : (1 : ℝ) ≤ Real.log t := by
    have hexp : Real.exp 1 ≤ t := by linarith [Real.exp_one_lt_d9]
    have h := Real.log_le_log (Real.exp_pos 1) hexp
    rwa [Real.log_exp] at h
  have htsq : (2 * (2 * Real.pi * C * 2 / ε)) ^ 2 ≤ t := by
    have := le_trans (le_max_right _ _) ht; linarith
  have hπ : (0 : ℝ) < 2 * Real.pi := by positivity
  -- `log t ≥ 2κ/ε`
  have hlogt : 2 * kappa / ε ≤ Real.log t := by
    have h := Real.log_le_log (Real.exp_pos _) htexp
    rwa [Real.log_exp] at h
  have hlog0 : 0 < Real.log t := by
    have : (0 : ℝ) < 2 * kappa / ε := by
      have := one_le_kappa; positivity
    linarith
  -- the profile increment dominates `(1/2π)·t·log t`
  have hprof : (1 / (2 * Real.pi)) * (t * Real.log t) ≤ profileDiff t (2 * t) := by
    have h2t : (3 : ℝ) ≤ 2 * t := by linarith
    have hle : t ≤ 2 * t := by linarith
    rw [profileDiff_of_le hle, mainProfile_eq h2t, mainProfile_eq ht3,
      Real.log_mul two_ne_zero ht0.ne']
    have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    have hinv : (0 : ℝ) ≤ 1 / (2 * Real.pi) := by positivity
    nlinarith [mul_nonneg (mul_nonneg hinv ht0.le) hlog2]
  -- `κ·t/(2π) ≤ (ε/2)·(1/2π)·t·log t`
  have hA : kappa * t / (2 * Real.pi) ≤ ε / 2 * ((1 / (2 * Real.pi)) * (t * Real.log t)) := by
    rw [div_le_iff₀ hε] at hlogt
    have hmul : 2 * kappa * t ≤ Real.log t * ε * t := mul_le_mul_of_nonneg_right hlogt ht0.le
    rw [div_le_iff₀ hπ]
    have hrw : ε / 2 * (1 / (2 * Real.pi) * (t * Real.log t)) * (2 * Real.pi)
        = Real.log t * ε * t / 2 := by field_simp
    rw [hrw]
    linarith
  -- `C·log t ≤ (ε/2)·(1/2π)·t·log t`
  have hB : C * Real.log t ≤ ε / 2 * ((1 / (2 * Real.pi)) * (t * Real.log t)) := by
    have h1 : 2 * Real.pi * C * 2 / ε * Real.log t ≤ t :=
      mul_log_le_self (by positivity) ht1 htsq
    have hepi : (0 : ℝ) < ε / (4 * Real.pi) := by positivity
    have h2 := mul_le_mul_of_nonneg_left h1 hepi.le
    have hlhs : ε / (4 * Real.pi) * (2 * Real.pi * C * 2 / ε * Real.log t)
        = C * Real.log t := by field_simp; ring
    rw [hlhs] at h2
    have hrw : ε / 2 * (1 / (2 * Real.pi) * (t * Real.log t))
        = ε / (4 * Real.pi) * (t * Real.log t) := by field_simp; ring
    rw [hrw]
    have htl : t ≤ t * Real.log t := by nlinarith [ht0.le, hlogone]
    nlinarith [hepi.le, htl]
  have hgap := profileDiff_sub_main ht3
  have hlow := (abs_le.mp (hrvm t htT₀)).1
  nlinarith [hprof, hA, hB]

/-! ## Dyadic → cumulative, both directions -/

lemma count_add {a b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c) :
    ((Zeta23.Ncount a c : ℕ) : ℝ) = (Zeta23.Ncount a b : ℝ) + (Zeta23.Ncount b c : ℝ) := by
  exact_mod_cast congrArg (Nat.cast : ℕ → ℝ) (Zeta23.Ncount_add hab hbc)

lemma tendsto_profileDiff : Tendsto (fun T => profileDiff 0 T) atTop atTop := by
  have hlin : Tendsto (fun T : ℝ => (1 / (2 * Real.pi)) * T + -mainProfile 0) atTop atTop :=
    Filter.tendsto_atTop_add_const_right _ _
      (Filter.Tendsto.const_mul_atTop (by positivity) Filter.tendsto_id)
  refine tendsto_atTop_mono' _ ?_ hlin
  filter_upwards [eventually_ge_atTop (max 3 (Real.exp 1))] with T hT
  have hT3 : (3 : ℝ) ≤ T := le_trans (le_max_left _ _) hT
  have hTe : Real.exp 1 ≤ T := le_trans (le_max_right _ _) hT
  have hT0 : (0 : ℝ) < T := by linarith
  have hlog1 : (1 : ℝ) ≤ Real.log T := by
    have h := Real.log_le_log (Real.exp_pos 1) hTe
    rwa [Real.log_exp] at h
  have hpd : profileDiff 0 T = mainProfile T - mainProfile 0 :=
    profileDiff_of_le (by linarith)
  rw [hpd, mainProfile_eq hT3]
  have hinv : (0 : ℝ) < 1 / (2 * Real.pi) := by positivity
  have htl : T ≤ T * Real.log T := by nlinarith [hT0.le]
  nlinarith [hinv.le, htl]

/-- Cumulative lower bound, by `Zeta23.Assembly.dyadic` with the census as `f`. -/
lemma cumulative_lower : ∀ ε > (0 : ℝ), ∃ T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T →
    (1 - ε) * profileDiff 0 T ≤ (Zeta23.Ncount 0 T : ℝ) :=
  Zeta23.Assembly.dyadic
    (f := fun a b => (Zeta23.Ncount a b : ℝ)) (g := profileDiff) (c := 1)
    (fun _ _ _ hab hbc => count_add hab hbc)
    (fun _ _ _ hab hbc => profileDiff_add hab hbc)
    (fun _ _ => Nat.cast_nonneg _) profileDiff_nonneg tendsto_profileDiff
    (fun ε hε => dyadic_lower ε hε)

/-- Cumulative upper bound, by `Zeta23.Assembly.dyadic` with the roles swapped. -/
lemma cumulative_upper : ∀ ε > (0 : ℝ), ∃ T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T →
    (1 - ε) * (Zeta23.Ncount 0 T : ℝ) ≤ profileDiff 0 T :=
  Zeta23.Assembly.dyadic
    (f := profileDiff) (g := fun a b => (Zeta23.Ncount a b : ℝ)) (c := 1)
    (fun _ _ _ hab hbc => profileDiff_add hab hbc)
    (fun _ _ _ hab hbc => count_add hab hbc)
    profileDiff_nonneg (fun _ _ => Nat.cast_nonneg _)
    (Zeta23.tendsto_Ncount_zero_atTop Zeta23.zetaSeam Zeta23.riemannVonMangoldt_zeta)
    (fun ε hε => dyadic_upper ε hε)

/-! ## The instance -/

/-- **The first inhabitant of `CountingData`**: ζ's cumulative zero census `N(0,T]`, with
density coefficient `cmain = 1/(2π)`.  Unconditional. -/
noncomputable def zetaCountingData : CountingData where
  N T := (Zeta23.Ncount 0 T : ℝ)
  cmain := 1 / (2 * Real.pi)
  approx := by
    intro ε hε
    set P₀ : ℝ := mainProfile 0 with hP₀
    have hP₀0 : 0 ≤ P₀ := mainProfile_nonneg 0
    set δ : ℝ := min (1 / 2) (Real.pi * ε) with hδ
    have hπ0 : (0 : ℝ) < Real.pi := Real.pi_pos
    have hδ0 : 0 < δ := lt_min (by norm_num) (by positivity)
    have hδhalf : δ ≤ 1 / 2 := min_le_left _ _
    have hδπε : δ ≤ Real.pi * ε := min_le_right _ _
    obtain ⟨TA, hTA⟩ := cumulative_lower δ hδ0
    obtain ⟨TB, hTB⟩ := cumulative_upper δ hδ0
    refine ⟨max (max TA TB) (max 3 (max (Real.exp 1) (2 * P₀ / ε + 1))), ?_, ?_⟩
    · exact le_max_of_le_right (le_max_left _ _)
    intro T hT
    have hTA' : TA ≤ T := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hT
    have hTB' : TB ≤ T := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hT
    have hT3 : (3 : ℝ) ≤ T := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hT
    have hTe : Real.exp 1 ≤ T :=
      le_trans (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))) hT
    have hTP : 2 * P₀ / ε + 1 ≤ T :=
      le_trans (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _))) hT
    have hT0 : (0 : ℝ) < T := by linarith
    have hlog1 : (1 : ℝ) ≤ Real.log T := by
      have h := Real.log_le_log (Real.exp_pos 1) hTe
      rwa [Real.log_exp] at h
    have hπ : (0 : ℝ) < 2 * Real.pi := by positivity
    set Y : ℝ := T * Real.log T with hY
    have hY0 : 0 < Y := by rw [hY]; positivity
    have hYT : T ≤ Y := by rw [hY]; nlinarith
    set X : ℝ := (1 / (2 * Real.pi)) * Y with hX
    have hX0 : 0 < X := by rw [hX]; positivity
    have hpd : profileDiff 0 T = X - P₀ := by
      rw [profileDiff_of_le (by linarith : (0:ℝ) ≤ T), mainProfile_eq hT3, hX, hY, hP₀]
    have hA := hTA T hTA'
    have hB := hTB T hTB'
    rw [hpd] at hA hB
    -- `P₀ ≤ (ε/2)·Y`
    have hPY : P₀ ≤ ε / 2 * Y := by
      have h1 : 2 * P₀ / ε ≤ T := by linarith
      rw [div_le_iff₀ hε] at h1
      nlinarith [hYT, hY0.le]
    -- upper: `Ncum − X ≤ 2πδ·X ≤ ε·Y`
    have hupper : (Zeta23.Ncount 0 T : ℝ) - X ≤ ε * Y := by
      have hone : (0 : ℝ) < 1 - δ := by linarith
      have hstep : (1 - δ) * ((Zeta23.Ncount 0 T : ℝ) - X) ≤ -(1 - δ) * P₀ + δ * X := by
        nlinarith [hB]
      have hδX : δ * X ≤ Real.pi * ε * X := by nlinarith [hX0.le]
      have hπεX : Real.pi * ε * X = ε * Y / 2 := by
        rw [hX]; field_simp
      nlinarith [hP₀0, hone, hY0.le]
    -- lower: `Ncum − X ≥ −P₀ − δ·X ≥ −ε·Y`
    have hlower : -(ε * Y) ≤ (Zeta23.Ncount 0 T : ℝ) - X := by
      have hδX : δ * X ≤ Real.pi * ε * X := by nlinarith [hX0.le]
      have hπεX : Real.pi * ε * X = ε * Y / 2 := by
        rw [hX]; field_simp
      nlinarith [hA, hP₀0, hPY]
    rw [abs_le]
    constructor
    · rw [hX] at hlower; linarith [hlower]
    · rw [hX] at hupper; linarith [hupper]

end ZetaCounting

/-! ## What this does, and does not, give -/

/-- **The structure is inhabited**: `accumulated_defect_positive` is no longer vacuous. -/
theorem countingData_nonempty : Nonempty CountingData :=
  ⟨ZetaCounting.zetaCountingData⟩

/-- **The density coefficient of ζ**, named for the record: `1/(2π)`. -/
theorem zeta_cmain : ZetaCounting.zetaCountingData.cmain = 1 / (2 * Real.pi) := rfl

/-- **The applicability gap, stated as a theorem.**  `accumulated_defect_positive` needs a
strict inequality between density coefficients.  Any two `CountingData` built from degree-one
`L`-functions — ζ and Dirichlet `L(s,χ)` alike, since `ell1q q T = log(qT/2π) + 2log 2 − 1` has
the same `T·log T` coefficient `1/(2π)` as `ell1` — have *equal* `cmain`, so the hypothesis
`hgap` is unsatisfiable between them and the theorem yields nothing.  A genuine gap needs two
different **degrees**. -/
theorem accumulated_defect_self_inapplicable
    (P C : CountingData) (hP : P.cmain = 1 / (2 * Real.pi))
    (hC : C.cmain = 1 / (2 * Real.pi)) : ¬ (C.cmain < P.cmain) := by
  rw [hP, hC]; exact lt_irrefl _

end CriticalLinePhasor.AccumulatedDefect

#print axioms CriticalLinePhasor.AccumulatedDefect.ZetaCounting.profileDiff_sub_main
#print axioms CriticalLinePhasor.AccumulatedDefect.ZetaCounting.zetaCountingData
#print axioms CriticalLinePhasor.AccumulatedDefect.countingData_nonempty
#print axioms CriticalLinePhasor.AccumulatedDefect.accumulated_defect_self_inapplicable
