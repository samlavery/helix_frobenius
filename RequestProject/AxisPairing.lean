import Mathlib

/-!
# Axis pairing: the free and the open part of the standing wave

On the weld axis the two-lane bank splits the classical readout into a part that is real
*termwise* — the paired bank `∑ (K n + conj (K n))`, the standing wave, carrying no
arithmetic — and an odd lane-mode whose extinction is *exactly* the functional equation.

This restates gate 2 (whole-bank axis reality) in the carrier's extinction genre:
* `pairedBank_real`        : the paired bank is real — free, termwise, any fiber;
* `readout_decomposition`  : classical readout = (paired + odd)/2;
* `fe_iff_oddMode_eq_zero` : the axis functional equation ⟺ the odd mode vanishes.

So the open content of axis reality is precisely an extinction statement (odd mode ≡ 0),
the same genre as the residual-mode extinction `R = 0`; the reality of the standing wave
itself is not arithmetic and is proved here for every finite bank.
-/

namespace AxisPairing

open Finset Complex

/-- The two-lane paired bank at the axis: each phasor summed with its conjugate lane. -/
def pairedBank (K : ℕ → ℂ) (F : Finset ℕ) : ℂ :=
  ∑ n ∈ F, (K n + (starRingEnd ℂ) (K n))

/-- The odd lane-mode: the anti-symmetric combination whose vanishing is the functional
equation (with unit `ε` and dual kernel `K'`). -/
def oddMode (ε : ℂ) (K K' : ℕ → ℂ) (F : Finset ℕ) : ℂ :=
  ∑ n ∈ F, (K n - ε * (starRingEnd ℂ) (K' n))

/-- The paired bank is real, termwise, for every finite bank and every fiber:
the standing wave costs nothing. -/
theorem pairedBank_real (K : ℕ → ℂ) (F : Finset ℕ) : (pairedBank K F).im = 0 := by
  unfold pairedBank
  induction F using Finset.cons_induction with
  | empty => simp
  | cons a s ha ih =>
      rw [Finset.sum_cons, Complex.add_im, ih, add_zero]
      simp [Complex.add_conj]

/-- The classical single-lane readout decomposes into the (free) paired bank and the
(arithmetic) odd mode. -/
theorem readout_decomposition (K : ℕ → ℂ) (F : Finset ℕ) :
    (∑ n ∈ F, K n) = (pairedBank K F + oddMode 1 K K F) / 2 := by
  unfold pairedBank oddMode
  rw [← Finset.sum_add_distrib]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro n _
  ring

/-- The axis functional equation is exactly extinction of the odd lane-mode. -/
theorem fe_iff_oddMode_eq_zero (ε : ℂ) (K K' : ℕ → ℂ) (F : Finset ℕ) :
    (∑ n ∈ F, K n) = ε * ∑ n ∈ F, (starRingEnd ℂ) (K' n) ↔ oddMode ε K K' F = 0 := by
  unfold oddMode
  rw [Finset.sum_sub_distrib, Finset.mul_sum]
  exact sub_eq_zero.symm

end AxisPairing
