import Mathlib
import RequestProject.ClosedForm

set_option maxHeartbeats 4000000
set_option maxRecDepth 4000

open scoped BigOperators
open scoped Real
open scoped Classical

open Complex Filter

/-!
# The exact `π/3` full fiber

This file records the **exact** Dirichlet-eta fiber at the harmonic cell `H := π/3`, with
*no kernel, no cutoff, no smoothing weight*.  The fiber is the genuine (conditionally
convergent) alternating Dirichlet series read on the critical line, and is *defined* to be
the analytic Dirichlet eta value there, so the representation is exact rather than
approximate.

Fix the harmonic cell and the critical read-out point:
```
H      := π / 3
s(T)   := 1/2 + i · H · T
```

The full fiber is the exact alternating series
```
FullFiber T  :=  ∑_{n ≥ 1} (-1)^(n-1) n^(-1/2) exp(-i H T log n)
              =  ∑_{n ≥ 1} (-1)^(n-1) n^(-s(T))
              =  η(1/2 + i H T),
```
and the finite truncations are mere observations of this one exact object:
```
PartialFiber N T  :=  ∑_{n < N} (-1)^n (n+1)^(-s(T))
TailFiber   N T  :=  FullFiber T − PartialFiber N T
```
so that `PartialFiber N T + TailFiber N T = FullFiber T` holds *exactly* for every `N`.

The exact object is the **infinite** eta fiber; the finite sums only approximate it.  Its
zeros are exactly the critical-line zeros of `ζ`:
```
FullFiber T = 0  ⇔  η(1/2 + i H T) = 0  ⇔  ζ(1/2 + i H T) = 0.
```
-/

namespace CriticalLinePhasor.Pi3Fiber

open CriticalLinePhasor CriticalLinePhasor.EtaTrivial

/-- **The harmonic cell** `H := π/3`. -/
noncomputable def H : ℝ := Real.pi / 3

/-- The critical read-out point `s(T) := 1/2 + i · H · T`. -/
noncomputable def sFiber (T : ℝ) : ℂ := (1 / 2 : ℂ) + ((H * T : ℝ) : ℂ) * I

/-- The real part of `s(T)` is `1/2`: the fiber is read on the critical line. -/
theorem sFiber_re (T : ℝ) : (sFiber T).re = 1 / 2 := by
  simp [sFiber, Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im]

/-- **The exact `π/3` full fiber** `FullFiber T := η(1/2 + i H T)`.  This is the genuine
alternating Dirichlet eta value, defined exactly (no kernel / cutoff / smoothing). -/
noncomputable def FullFiber (T : ℝ) : ℂ := etaTrivial (sFiber T)

/-- **The full fiber is exactly the eta value on the critical read-out.** -/
theorem FullFiber_eq_eta (T : ℝ) : FullFiber T = etaTrivial (sFiber T) := rfl

/-- **Zero equivalence (eta form).** -/
theorem FullFiber_eq_zero_iff_eta (T : ℝ) :
    FullFiber T = 0 ↔ etaTrivial (sFiber T) = 0 := Iff.rfl

/-- **Zero equivalence (zeta form).**  The full fiber vanishes exactly at the critical-line
zeros of `ζ`: `FullFiber T = 0 ↔ ζ(1/2 + i H T) = 0`. -/
theorem FullFiber_eq_zero_iff_zeta (T : ℝ) :
    FullFiber T = 0 ↔ riemannZeta (sFiber T) = 0 := by
  unfold FullFiber sFiber
  exact etaTrivial_eq_zero_iff_critical (H * T)

/-- **The finite partial fiber** `PartialFiber N T := ∑_{n < N} (-1)^n (n+1)^(-s(T))`. -/
noncomputable def PartialFiber (N : ℕ) (T : ℝ) : ℂ := etaCarrierFinite (sFiber T) N

/-- The partial fiber, unfolded as a finite alternating Dirichlet sum. -/
theorem PartialFiber_eq (N : ℕ) (T : ℝ) :
    PartialFiber N T = ∑ n ∈ Finset.range N, (-1 : ℂ) ^ n / ((n : ℂ) + 1) ^ (sFiber T) := rfl

/-
**Critical-line phasor form of the partial fiber.**  Each term is an exact phasor with
magnitude `(n+1)^(-1/2)` and spin `-(H·T·log (n+1))`.
-/
theorem PartialFiber_eq_phasor (N : ℕ) (T : ℝ) :
    PartialFiber N T = ∑ n ∈ Finset.range N,
      (-1 : ℂ) ^ n * ((((n : ℝ) + 1) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
        Complex.exp (-(H * T * Real.log ((n : ℝ) + 1)) * I) := by
  rw [PartialFiber_eq]
  refine Finset.sum_congr rfl (fun n _ => ?_)
  rw [div_eq_mul_inv, ← Complex.cpow_neg,
    show ((n : ℂ) + 1) = (((n + 1 : ℕ)) : ℂ) by push_cast; ring,
    show -(sFiber T) = -((1 / 2 : ℂ) + ((H * T : ℝ) : ℂ) * I) by rw [sFiber],
    CriticalLinePhasor.cpow_critical_line (H * T) (n + 1) (Nat.succ_pos n)]
  push_cast
  ring

/-- **The tail** `TailFiber N T := FullFiber T − PartialFiber N T`.  It is not a second
object; it is just the part of the one exact fiber not yet observed. -/
noncomputable def TailFiber (N : ℕ) (T : ℝ) : ℂ := FullFiber T - PartialFiber N T

/-- **Exact decomposition.**  For every `N`, `PartialFiber N T + TailFiber N T = FullFiber T`
holds exactly, with no residue. -/
theorem PartialFiber_add_TailFiber (N : ℕ) (T : ℝ) :
    PartialFiber N T + TailFiber N T = FullFiber T := by
  unfold TailFiber; ring

/-!
### Identification of the exact limit with `η` via analytic continuation

The conditionally convergent fiber series, paired two terms at a time, is the *absolutely*
convergent series `pairedEta s = ∑' k, ((2k+1)^(-s) − (2k+2)^(-s))`, which converges for
`Re s > 0`.  On `Re s > 1` it agrees with `η` by rearrangement; both sides are holomorphic
on the slit half-plane `{Re s > 0} \ {1}`, so by the identity principle they agree there —
in particular on the critical line `Re s = 1/2`.  This identifies the exact fiber limit with
`η`, hence with `FullFiber`.
-/

/-- The `k`-th **paired eta term** `(2k+1)^(-s) − (2k+2)^(-s)`. -/
noncomputable def pairedTerm (s : ℂ) (k : ℕ) : ℂ :=
  ((2 * (k : ℂ) + 1)) ^ (-s) - ((2 * (k : ℂ) + 2)) ^ (-s)

/-- The **paired eta series** `∑' k, ((2k+1)^(-s) − (2k+2)^(-s))`, absolutely convergent for
`Re s > 0`. -/
noncomputable def pairedEta (s : ℂ) : ℂ := ∑' k : ℕ, pairedTerm s k

/-- Norm bound on the difference of consecutive complex powers:
`‖a^(-w) - (a+1)^(-w)‖ ≤ ‖w‖ * a^(-Re w - 1)` for `a ≥ 1` and `Re w > 0`. -/
theorem cpow_neg_consecutive_norm_le {w : ℂ} (hw : 0 < w.re) {a : ℝ} (ha : 1 ≤ a) :
    ‖(a : ℂ) ^ (-w) - ((a + 1 : ℝ) : ℂ) ^ (-w)‖ ≤ ‖w‖ * a ^ (-w.re - 1) := by
  have ha0 : (0 : ℝ) < a := lt_of_lt_of_le one_pos ha
  have hle : a ≤ a + 1 := by linarith
  have hw0 : w ≠ 0 := by intro h; rw [h] at hw; simp at hw
  have h0notmem : (0 : ℝ) ∉ Set.uIcc a (a + 1) := by
    rw [Set.uIcc_of_le hle]; simp only [Set.mem_Icc, not_and, not_le]; intro h; linarith
  have h_integral : ((a + 1 : ℝ) : ℂ) ^ (-w) - (a : ℂ) ^ (-w)
      = -w * ∫ x in a..(a + 1), (x : ℂ) ^ (-w - 1) := by
    rw [integral_cpow (Or.inr ⟨by rwa [Ne, ← add_eq_zero_iff_eq_neg, sub_add_cancel, neg_eq_zero], h0notmem⟩)]
    rw [show (-w - 1) + 1 = -w by ring]
    field_simp
  have h_intbound1 : ‖∫ x in a..(a + 1), (x : ℂ) ^ (-w - 1)‖
      ≤ ∫ x in a..(a + 1), x ^ (-w.re - 1) := by
    calc ‖∫ x in a..(a + 1), (x : ℂ) ^ (-w - 1)‖
        ≤ ∫ x in a..(a + 1), ‖(x : ℂ) ^ (-w - 1)‖ :=
          intervalIntegral.norm_integral_le_integral_norm hle
      _ = ∫ x in a..(a + 1), x ^ (-w.re - 1) := by
          refine intervalIntegral.integral_congr (fun x hx => ?_)
          rw [Set.uIcc_of_le hle] at hx
          rw [Complex.norm_cpow_eq_rpow_re_of_pos (by linarith [hx.1])]
          norm_num
  have h_intbound2 : ∫ x in a..(a + 1), x ^ (-w.re - 1) ≤ a ^ (-w.re - 1) := by
    have hmono : ∫ x in a..(a + 1), x ^ (-w.re - 1)
        ≤ ∫ _x in a..(a + 1), a ^ (-w.re - 1) := by
      refine intervalIntegral.integral_mono_on hle ?_ intervalIntegrable_const (fun x hx => ?_)
      · apply intervalIntegral.intervalIntegrable_rpow
        right; exact h0notmem
      · rw [Real.rpow_le_rpow_iff_of_neg (by linarith [hx.1]) ha0 (by linarith)]
        linarith [hx.1]
    simpa using hmono
  calc ‖(a : ℂ) ^ (-w) - ((a + 1 : ℝ) : ℂ) ^ (-w)‖
      = ‖((a + 1 : ℝ) : ℂ) ^ (-w) - (a : ℂ) ^ (-w)‖ := by rw [norm_sub_rev]
    _ = ‖w‖ * ‖∫ x in a..(a + 1), (x : ℂ) ^ (-w - 1)‖ := by
        rw [h_integral, norm_mul, norm_neg]
    _ ≤ ‖w‖ * a ^ (-w.re - 1) :=
        mul_le_mul_of_nonneg_left (le_trans h_intbound1 h_intbound2) (norm_nonneg _)


/-
**Absolute summability of the paired eta terms** for `Re s > 0`.
-/
theorem pairedTerm_summable {s : ℂ} (hs : 0 < s.re) :
    Summable (fun k => pairedTerm s k) := by
  have h_integral_bound : ∀ k : ℕ, ‖pairedTerm s k‖ ≤ ‖s‖ * ∫ x in (2 * k + 1 : ℝ).. (2 * k + 2 : ℝ), x ^ (-s.re - 1) := by
    intro k
    have h_integral : (2 * (k : ℂ) + 2) ^ (-s) - (2 * (k : ℂ) + 1) ^ (-s) = -s * ∫ x in (2 * (k : ℝ) + 1).. (2 * (k : ℝ) + 2), (x : ℂ) ^ (-s - 1) := by
      rw [ integral_cpow ] <;> norm_num;
      · grind +suggestions;
      · exact Or.inr ⟨ by rintro rfl; norm_num at hs, by intros; linarith ⟩;
    have h_integral_bound : ‖∫ x in (2 * (k : ℝ) + 1).. (2 * (k : ℝ) + 2), (x : ℂ) ^ (-s - 1)‖ ≤ ∫ x in (2 * (k : ℝ) + 1).. (2 * (k : ℝ) + 2), x ^ (-s.re - 1) := by
      convert intervalIntegral.norm_integral_le_integral_norm _ using 1;
      · refine' intervalIntegral.integral_congr fun x hx => _;
        rw [ Complex.norm_cpow_eq_rpow_re_of_pos ( by cases Set.mem_uIcc.mp hx <;> linarith ) ] ; norm_num;
      · norm_num;
    have hval : pairedTerm s k
        = s * ∫ (x : ℝ) in (2 * (k : ℝ) + 1)..(2 * (k : ℝ) + 2), (x : ℂ) ^ (-s - 1) := by
      rw [show pairedTerm s k
            = -((2 * (k : ℂ) + 2) ^ (-s) - (2 * (k : ℂ) + 1) ^ (-s)) by unfold pairedTerm; ring,
        h_integral]
      ring
    rw [hval, norm_mul]
    exact mul_le_mul_of_nonneg_left h_integral_bound (norm_nonneg s)
  -- The integral $\int_{2k+1}^{2k+2} x^{-s.re-1} \, dx$ is bounded by $(2k+1)^{-s.re-1}$.
  have h_integral_bound : ∀ k : ℕ, ∫ x in (2 * k + 1 : ℝ).. (2 * k + 2 : ℝ), x ^ (-s.re - 1) ≤ (2 * k + 1 : ℝ) ^ (-s.re - 1) := by
    intro k
    have h_integral_bound : ∫ x in (2 * k + 1 : ℝ).. (2 * k + 2 : ℝ), x ^ (-s.re - 1) ≤ ∫ x in (2 * k + 1 : ℝ).. (2 * k + 2 : ℝ), (2 * k + 1 : ℝ) ^ (-s.re - 1) := by
      refine' intervalIntegral.integral_mono_on _ _ _ _ <;> norm_num;
      · apply_rules [ intervalIntegral.intervalIntegrable_rpow ] ; norm_num;
        exact Or.inr fun h => by linarith;
      · intro x hx₁ hx₂; rw [ Real.rpow_le_rpow_iff_of_neg ] <;> linarith;
    norm_num at * ; linarith;
  -- The series $\sum_{k=0}^{\infty} (2k+1)^{-s.re-1}$ is a convergent p-series with $p = s.re + 1 > 1$.
  have h_pseries : Summable (fun k : ℕ => (2 * k + 1 : ℝ) ^ (-s.re - 1)) := by
    exact_mod_cast Summable.comp_injective ( Real.summable_nat_rpow.2 <| by linarith ) fun a b h => by simpa using h;
  exact .of_norm <| Summable.of_nonneg_of_le ( fun k => norm_nonneg _ ) ( fun k => le_trans ( by solve_by_elim ) <| mul_le_mul_of_nonneg_left ( h_integral_bound k ) <| norm_nonneg _ ) <| h_pseries.mul_left _

/-
**Rearrangement on `Re s > 1`.**  Pairing the absolutely convergent eta series two terms
at a time gives the paired eta series, so `pairedEta s = η(s)` there.
-/
theorem pairedEta_eq_etaTrivial_of_one_lt {s : ℂ} (hs : 1 < s.re) :
    pairedEta s = etaTrivial s := by
  have hsum : Summable (fun n : ℕ => (-1 : ℂ) ^ n / ((n : ℂ) + 1) ^ s) :=
    etaCarrier_summable hs
  have he : Summable (fun k : ℕ => (-1 : ℂ) ^ (2 * k) / (((2 * k : ℕ) : ℂ) + 1) ^ s) :=
    hsum.comp_injective (fun a b h => by simpa using h)
  have ho : Summable (fun k : ℕ => (-1 : ℂ) ^ (2 * k + 1) / (((2 * k + 1 : ℕ) : ℂ) + 1) ^ s) :=
    hsum.comp_injective (fun a b h => by simpa using h)
  rw [etaTrivial_eq_tsum hs, ← tsum_even_add_odd he ho, pairedEta, ← Summable.tsum_add he ho]
  refine tsum_congr (fun k => ?_)
  have e2 : ((2 * k : ℕ) : ℂ) + 1 = 2 * (k : ℂ) + 1 := by push_cast; ring
  have e3 : ((2 * k + 1 : ℕ) : ℂ) + 1 = 2 * (k : ℂ) + 2 := by push_cast; ring
  have o2 : ((-1 : ℂ)) ^ (2 * k) = 1 := by rw [pow_mul]; norm_num
  have o3 : ((-1 : ℂ)) ^ (2 * k + 1) = -1 := by rw [pow_succ, pow_mul]; norm_num
  rw [pairedTerm, e2, e3, o2, o3, Complex.cpow_neg, Complex.cpow_neg]
  ring

/-
**The paired eta series is holomorphic on the right half-plane** `Re s > 0`.
-/
theorem pairedEta_differentiableAt {s : ℂ} (hs : 0 < s.re) :
    DifferentiableAt ℂ pairedEta s := by
  set a := s.re / 2 with ha_def
  set r := s.re / 2 with hr_def
  set U := Metric.ball s r with hU_def
  have ha : 0 < a := half_pos hs
  have hr : 0 < r := ha
  have hsU : s ∈ U := Metric.mem_ball_self hr
  -- each term is differentiable on U
  have h_diff : ∀ k : ℕ, DifferentiableOn ℂ
      (fun w => (2 * (k : ℂ) + 1) ^ (-w) - (2 * (k : ℂ) + 2) ^ (-w)) U := by
    intro k
    have hne1 : (2 * (k : ℂ) + 1) ≠ 0 := by
      rw [show (2 * (k : ℂ) + 1) = ((2 * (k : ℝ) + 1 : ℝ) : ℂ) by push_cast; ring]
      exact_mod_cast (by positivity : (0 : ℝ) < 2 * (k : ℝ) + 1).ne'
    have hne2 : (2 * (k : ℂ) + 2) ≠ 0 := by
      rw [show (2 * (k : ℂ) + 2) = ((2 * (k : ℝ) + 2 : ℝ) : ℂ) by push_cast; ring]
      exact_mod_cast (by positivity : (0 : ℝ) < 2 * (k : ℝ) + 2).ne'
    exact (differentiableOn_id.neg.const_cpow (Or.inl hne1)).sub
      (differentiableOn_id.neg.const_cpow (Or.inl hne2))
  -- uniform bound via aux lemma
  have h_bound : ∀ k : ℕ, ∀ w ∈ U,
      ‖(2 * (k : ℂ) + 1) ^ (-w) - (2 * (k : ℂ) + 2) ^ (-w)‖
        ≤ (‖s‖ + r) * (2 * (k : ℝ) + 1) ^ (-a - 1) := by
    intro k w hw
    have hdist : ‖w - s‖ < r := by
      rw [hU_def, Metric.mem_ball, dist_eq_norm] at hw; exact hw
    have hre : |w.re - s.re| < r := by
      have : |(w - s).re| ≤ ‖w - s‖ := Complex.abs_re_le_norm _
      simpa [Complex.sub_re] using lt_of_le_of_lt this hdist
    have hsplit := abs_lt.mp hre
    have hwre : 0 < w.re := by linarith [hsplit.1]
    have hwre_a : a ≤ w.re := by linarith [hsplit.1]
    have hwnorm : ‖w‖ ≤ ‖s‖ + r := by
      have h1 : ‖w‖ ≤ ‖w - s‖ + ‖s‖ := by
        calc ‖w‖ = ‖(w - s) + s‖ := by rw [show (w - s) + s = w from by ring]
          _ ≤ ‖w - s‖ + ‖s‖ := norm_add_le _ _
      linarith
    have hk1 : (1 : ℝ) ≤ 2 * (k : ℝ) + 1 := by have := Nat.cast_nonneg (α := ℝ) k; linarith
    have haux := cpow_neg_consecutive_norm_le hwre (a := 2 * (k : ℝ) + 1) hk1
    have e1 : ((2 * (k : ℝ) + 1 : ℝ) : ℂ) = 2 * (k : ℂ) + 1 := by push_cast; ring
    have e2 : ((2 * (k : ℝ) + 1 + 1 : ℝ) : ℂ) = 2 * (k : ℂ) + 2 := by push_cast; ring
    rw [e1, e2] at haux
    refine le_trans haux ?_
    apply mul_le_mul hwnorm _ (by positivity) (by positivity)
    apply Real.rpow_le_rpow_of_exponent_le hk1
    linarith
  have h_summable : Summable (fun k : ℕ => (‖s‖ + r) * (2 * (k : ℝ) + 1) ^ (-a - 1)) := by
    apply Summable.mul_left
    have hsum : Summable (fun n : ℕ => ((2 * n + 1 : ℕ) : ℝ) ^ (-a - 1)) :=
      (Real.summable_nat_rpow.2 (by linarith)).comp_injective (fun x y h => by simpa using h)
    refine hsum.congr (fun n => ?_)
    rw [show ((2 * n + 1 : ℕ) : ℝ) = 2 * (n : ℝ) + 1 by push_cast; ring]
  have h_main : DifferentiableOn ℂ
      (fun w => ∑' k : ℕ, ((2 * (k : ℂ) + 1) ^ (-w) - (2 * (k : ℂ) + 2) ^ (-w))) U :=
    Complex.differentiableOn_tsum_of_summable_norm h_summable h_diff Metric.isOpen_ball h_bound
  have hda : DifferentiableAt ℂ
      (fun w => ∑' k : ℕ, ((2 * (k : ℂ) + 1) ^ (-w) - (2 * (k : ℂ) + 2) ^ (-w))) s :=
    h_main.differentiableAt (Metric.isOpen_ball.mem_nhds hsU)
  have hfun : pairedEta = fun w => ∑' k : ℕ, ((2 * (k : ℂ) + 1) ^ (-w) - (2 * (k : ℂ) + 2) ^ (-w)) := by
    funext w; rfl
  rw [hfun]; exact hda

/-
The slit right half-plane `{Re s > 0} \ {1}` is preconnected.
-/
theorem rightHalfPlane_sdiff_one_isPreconnected :
    IsPreconnected ({s : ℂ | 0 < s.re} \ {1}) := by
  -- Write the set as a union of four convex pieces: U1, U2, U3, U4.
  set U1 : Set ℂ := {s : ℂ | 0 < s.re ∧ s.re < 1}
  set U2 : Set ℂ := {s : ℂ | 0 < s.re ∧ 0 < s.im}
  set U3 : Set ℂ := {s : ℂ | 1 < s.re}
  set U4 : Set ℂ := {s : ℂ | 0 < s.re ∧ s.im < 0};
  -- Prove that ${s | 0 < s.re} \ {1} = U1 ∪ U2 ∪ U3 ∪ U4$.
  have h_union : {s : ℂ | 0 < s.re} \ {1} = U1 ∪ U2 ∪ U3 ∪ U4 := by
    ext s
    simp only [U1, U2, U3, U4, Set.mem_sdiff, Set.mem_setOf_eq, Set.mem_singleton_iff,
      Set.mem_union, Complex.ext_iff, Complex.one_re, Complex.one_im]
    constructor
    · rintro ⟨hpos, hne⟩
      rcases lt_trichotomy s.re 1 with h | h | h
      · exact Or.inl (Or.inl (Or.inl ⟨hpos, h⟩))
      · have him : s.im ≠ 0 := fun h0 => hne ⟨h, h0⟩
        rcases lt_or_gt_of_ne him with hi | hi
        · exact Or.inr ⟨hpos, hi⟩
        · exact Or.inl (Or.inl (Or.inr ⟨hpos, hi⟩))
      · exact Or.inl (Or.inr h)
    · rintro (((⟨h1, h2⟩ | ⟨h1, h2⟩) | h3) | ⟨h1, h2⟩)
      · exact ⟨h1, fun hc => by linarith [hc.1]⟩
      · exact ⟨h1, fun hc => by simp [hc.2] at h2⟩
      · exact ⟨by linarith, fun hc => by linarith [hc.1]⟩
      · exact ⟨h1, fun hc => by simp [hc.2] at h2⟩
  -- Each $U_i$ is convex, hence preconnected.
  have h_convex : Convex ℝ U1 ∧ Convex ℝ U2 ∧ Convex ℝ U3 ∧ Convex ℝ U4 := by
    refine' ⟨ _, _, _, _ ⟩;
    · exact convex_halfSpace_re_gt 0 |> Convex.inter <| convex_halfSpace_re_lt 1;
    · exact convex_halfSpace_re_gt 0 |> Convex.inter <| convex_halfSpace_im_gt 0;
    · exact convex_halfSpace_re_gt 1;
    · exact convex_halfSpace_re_gt 0 |> Convex.inter <| convex_halfSpace_im_lt 0;
  -- Glue with `IsPreconnected.union` along a chain of common points: `U1 ∩ U2 ∋ (1/2 + I)`, `U2 ∩ U3 ∋ (2 + I)`, `U3 ∩ U4 ∋ (2 - I)`.
  have h_common_points : (1 / 2 + Complex.I) ∈ U1 ∩ U2 ∧ (2 + Complex.I) ∈ U2 ∩ U3 ∧ (2 - Complex.I) ∈ U3 ∩ U4 := by
    norm_num [ U1, U2, U3, U4 ];
  -- Apply `IsPreconnected.union` to each pair of sets.
  have h_union1 : IsPreconnected (U1 ∪ U2) := by
    apply_rules [ IsPreconnected.union, h_convex.1.isPreconnected, h_convex.2.1.isPreconnected ];
    exacts [ h_common_points.1.1, h_common_points.1.2 ]
  have h_union2 : IsPreconnected (U1 ∪ U2 ∪ U3) := by
    apply_rules [ IsPreconnected.union, h_union1 ];
    exacts [ Set.mem_union_right _ h_common_points.2.1.1, h_common_points.2.1.2, h_convex.2.2.1.isPreconnected ]
  have h_union3 : IsPreconnected (U1 ∪ U2 ∪ U3 ∪ U4) := by
    apply_rules [ IsPreconnected.union ];
    exacts [ Or.inr h_common_points.2.2.1, h_common_points.2.2.2, h_convex.2.2.2.isPreconnected ];
  exact h_union ▸ h_union3

/-
**Identification by the identity principle.**  `pairedEta s = η(s)` throughout the slit
right half-plane `{Re s > 0} \ {1}`.
-/
theorem pairedEta_eq_etaTrivial {s : ℂ} (hs : 0 < s.re) (hne : s ≠ 1) :
    pairedEta s = etaTrivial s := by
  -- Let `U := {s : ℂ | 0 < s.re} \ {1}`, which is preconnected by `rightHalfPlane_sdiff_one_isPreconnected`, and pick `z₀ := (2 : ℂ) ∈ U` (re = 2 > 0, ≠ 1).
  set U : Set ℂ := {s | 0 < s.re} \ {1}
  set z₀ : ℂ := 2
  have hz₀ : z₀ ∈ U := by
    norm_num [ U, z₀ ];
  -- Analyticity of `pairedEta` on `U`: `pairedEta` is `DifferentiableOn ℂ` on the open half-plane `{s | 0 < s.re}` (pointwise `DifferentiableAt` from `pairedEta_differentiableAt`, then `DifferentiableOn`), so by `DifferentiableOn.analyticOnNhd` (the half-plane is open) it is `AnalyticOnNhd ℂ pairedEta {0 < re}`, and `.mono (diff_subset.trans ...)` restricts it to `U`.
  have h_analytic_pairedEta : AnalyticOnNhd ℂ pairedEta U := by
    apply_rules [ DifferentiableOn.analyticOnNhd ];
    · exact fun x hx => DifferentiableAt.differentiableWithinAt ( pairedEta_differentiableAt hx.1 );
    · exact isOpen_Ioi.preimage Complex.continuous_re |> IsOpen.sdiff <| isClosed_singleton;
  -- Analyticity of `etaTrivial` on `U`: on the open set `{1}ᶜ`, `etaTrivial s = (1 - 2^(1-s)) * riemannZeta s` is differentiable — `(1 - 2^(1-s))` is entire and `riemannZeta` is differentiable at every `s ≠ 1` (`differentiableAt_riemannZeta`); hence `DifferentiableOn ℂ etaTrivial {1}ᶜ`, giving `AnalyticOnNhd ℂ etaTrivial {1}ᶜ` by `DifferentiableOn.analyticOnNhd`, restricted via `.mono` to `U ⊆ {1}ᶜ`.
  have h_analytic_etaTrivial : AnalyticOnNhd ℂ etaTrivial U := by
    apply_rules [ DifferentiableOn.analyticOnNhd ];
    · refine' DifferentiableOn.mul _ _;
      · exact DifferentiableOn.sub ( differentiableOn_const _ ) ( DifferentiableOn.cpow ( differentiableOn_const _ ) ( differentiableOn_id.const_sub _ ) ( by intro s hs; norm_num [ Complex.cpow_def ] ) );
      · intro s hs; exact differentiableAt_riemannZeta ( by aesop ) |> DifferentiableAt.differentiableWithinAt;
    · exact isOpen_Ioi.preimage Complex.continuous_re |> IsOpen.sdiff <| isClosed_singleton;
  apply h_analytic_pairedEta.eqOn_of_preconnected_of_eventuallyEq h_analytic_etaTrivial (rightHalfPlane_sdiff_one_isPreconnected) hz₀;
  · filter_upwards [ IsOpen.mem_nhds ( isOpen_lt continuous_const Complex.continuous_re ) ( show 1 < z₀.re by norm_num ) ] with s hs using pairedEta_eq_etaTrivial_of_one_lt hs;
  · exact ⟨ hs, hne ⟩

/-- The fiber read-out point is never `1` (its real part is `1/2`). -/
theorem sFiber_ne_one (T : ℝ) : sFiber T ≠ 1 := by
  intro h
  have hre : (sFiber T).re = (1 : ℂ).re := by rw [h]
  rw [sFiber_re] at hre; norm_num at hre

/-
**The partial fibers converge to the paired eta value.**
-/
theorem PartialFiber_tendsto_pairedEta (T : ℝ) :
    Filter.Tendsto (fun N => PartialFiber N T) Filter.atTop (nhds (pairedEta (sFiber T))) := by
  have hsre : 0 < (sFiber T).re := by rw [sFiber_re]; norm_num
  -- (1) even partial sums equal partial sums of the paired terms
  have heven : ∀ N : ℕ, PartialFiber (2 * N) T
      = ∑ k ∈ Finset.range N, pairedTerm (sFiber T) k := by
    intro N
    induction N with
    | zero => simp [PartialFiber_eq]
    | succ n ih =>
        rw [Finset.sum_range_succ, ← ih, PartialFiber_eq, PartialFiber_eq,
          show 2 * (n + 1) = (2 * n + 1) + 1 by ring,
          Finset.sum_range_succ, Finset.sum_range_succ, add_assoc]
        congr 1
        have e2 : ((2 * n : ℕ) : ℂ) + 1 = 2 * (n : ℂ) + 1 := by push_cast; ring
        have e3 : ((2 * n + 1 : ℕ) : ℂ) + 1 = 2 * (n : ℂ) + 2 := by push_cast; ring
        have o2 : ((-1 : ℂ)) ^ (2 * n) = 1 := by rw [pow_mul]; norm_num
        have o3 : ((-1 : ℂ)) ^ (2 * n + 1) = -1 := by rw [pow_succ, pow_mul]; norm_num
        rw [pairedTerm, e2, e3, o2, o3, Complex.cpow_neg, Complex.cpow_neg]
        ring
  -- (2) partial sums of the paired terms converge to `pairedEta`
  have hps : Filter.Tendsto (fun N => ∑ k ∈ Finset.range N, pairedTerm (sFiber T) k)
      Filter.atTop (nhds (pairedEta (sFiber T))) :=
    (pairedTerm_summable hsre).hasSum.tendsto_sum_nat
  have h_even : Filter.Tendsto (fun N => PartialFiber (2 * N) T) Filter.atTop
      (nhds (pairedEta (sFiber T))) := by simpa only [heven] using hps
  -- (3) the individual terms tend to zero
  have h_term : Filter.Tendsto (fun N : ℕ => (-1 : ℂ) ^ N / ((N : ℂ) + 1) ^ (sFiber T))
      Filter.atTop (nhds 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hnorm : ∀ N : ℕ, ‖(-1 : ℂ) ^ N / ((N : ℂ) + 1) ^ (sFiber T)‖
        = ((N : ℝ) + 1) ^ (-(1 / 2 : ℝ)) := by
      intro N
      rw [norm_div, norm_pow, norm_neg, norm_one, one_pow,
        show ((N : ℂ) + 1) = (((N : ℝ) + 1 : ℝ) : ℂ) by push_cast; ring,
        Complex.norm_cpow_eq_rpow_re_of_pos (by positivity), sFiber_re, one_div,
        ← Real.rpow_neg (by positivity)]
    refine Filter.Tendsto.congr (fun N => (hnorm N).symm) ?_
    have h1 : Filter.Tendsto (fun N : ℕ => (N : ℝ) + 1) Filter.atTop Filter.atTop :=
      Filter.tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
    exact (tendsto_rpow_neg_atTop (by norm_num)).comp h1
  -- (4) odd partial sums also converge to `pairedEta`
  have hodd : Filter.Tendsto (fun N => PartialFiber (2 * N + 1) T) Filter.atTop
      (nhds (pairedEta (sFiber T))) := by
    have hsplit : ∀ N : ℕ, PartialFiber (2 * N + 1) T
        = PartialFiber (2 * N) T + (-1 : ℂ) ^ (2 * N) / (((2 * N : ℕ) : ℂ) + 1) ^ (sFiber T) := by
      intro N; rw [PartialFiber_eq, PartialFiber_eq, Finset.sum_range_succ]
    have h2N : Filter.Tendsto (fun N : ℕ => 2 * N) Filter.atTop Filter.atTop :=
      Filter.tendsto_atTop_mono (fun n => by simp only [id_eq]; omega) tendsto_id
    have hcomb := h_even.add (h_term.comp h2N)
    rw [add_zero] at hcomb
    simpa only [hsplit, Function.comp_apply] using hcomb
  -- (5) assemble even and odd into convergence of the whole sequence
  rw [Metric.tendsto_atTop]
  rw [Metric.tendsto_atTop] at h_even hodd
  intro ε hε
  obtain ⟨N1, hN1⟩ := h_even ε hε
  obtain ⟨N2, hN2⟩ := hodd ε hε
  refine ⟨2 * (N1 + N2) + 1, fun n hn => ?_⟩
  rcases Nat.even_or_odd' n with ⟨k, rfl | rfl⟩
  · exact hN1 k (by omega)
  · exact hN2 k (by omega)

/-- **The partial fibers converge to the exact full fiber.**
`PartialFiber N T → FullFiber T` as `N → ∞`, i.e. the finite observations exhaust the one
exact eta fiber. -/
theorem PartialFiber_tendsto_FullFiber (T : ℝ) :
    Filter.Tendsto (fun N => PartialFiber N T) Filter.atTop (nhds (FullFiber T)) := by
  have h1 := PartialFiber_tendsto_pairedEta T
  have h2 : pairedEta (sFiber T) = FullFiber T := by
    rw [FullFiber]
    exact pairedEta_eq_etaTrivial (by rw [sFiber_re]; norm_num) (sFiber_ne_one T)
  rwa [h2] at h1

/-- **The tail vanishes.**  The unobserved part of the exact fiber tends to `0`. -/
theorem TailFiber_tendsto_zero (T : ℝ) :
    Filter.Tendsto (fun N => TailFiber N T) Filter.atTop (nhds 0) := by
  have h := PartialFiber_tendsto_FullFiber T
  have : Filter.Tendsto (fun N => FullFiber T - PartialFiber N T) Filter.atTop
      (nhds (FullFiber T - FullFiber T)) := tendsto_const_nhds.sub h
  simpa [TailFiber, sub_self] using this

/-- **Conditional (Dirichlet/alternating) convergence of the partial fibers** on the
critical line.  The truncations form a Cauchy sequence (hence converge), even though the
series is only conditionally — not absolutely — convergent there. -/
theorem PartialFiber_cauchySeq (T : ℝ) :
    CauchySeq (fun N => PartialFiber N T) :=
  (PartialFiber_tendsto_FullFiber T).cauchySeq

end CriticalLinePhasor.Pi3Fiber