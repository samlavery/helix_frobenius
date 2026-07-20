import Mathlib

/-!
# The μ₃ Prym parity: the lift-distribution law

Companion to `tmp/w3_spec.md` (2026-07-19).  For an étale μ₃-cover, the
effective locus V¹ ⊂ Nm⁻¹(ω) splits into three components indexed by the
total sheet-shift Σ mod 3 (the ℤ/3-twin of Mumford's ℤ/2 Prym parity;
mechanism: the divisor-motion cycle of an |ω|-loop is nullhomologous, so
monodromy preserves Σ).  This file proves, unconditionally, the resulting
DISTRIBUTION LAW for rational lifts over a divisor with closed points of
degrees d₁,…,d_r (machine-confirmed 48/48 over F₇, tmp/w3_parity.sage):

* relative parity of a lift = Σ dᵢkᵢ mod 3 (kᵢ = per-point sheet shifts);
* if some dᵢ ≢ 0 mod 3, the 3^r lifts distribute UNIFORMLY (3^(r-1) per
  parity class);
* if all dᵢ ≡ 0 mod 3, all lifts have the SAME parity (concentration).

Scope: does not assume or prove RH/GRH.  The geometric inputs (monodromy
invariance of Σ, the component count) are cited context; this file proves
the counting law the instrument tested.
-/

namespace MuThreePrymParity

open Finset

/-- The parity of a sheet-choice `k : Fin r → ZMod 3` for point degrees
`d : Fin r → ZMod 3` (degrees reduced mod 3). -/
def parity {r : ℕ} (d k : Fin r → ZMod 3) : ZMod 3 := ∑ i, d i * k i

/-- Parity is additive in the sheet-choice: it is a group character. -/
theorem parity_add {r : ℕ} (d k k' : Fin r → ZMod 3) :
    parity d (k + k') = parity d k + parity d k' := by
  unfold parity
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun j _ => by simp [mul_add]

/-- Concentration: if every degree is ≡ 0 mod 3, every lift has parity 0 —
all rational lifts land in one component. -/
theorem concentration {r : ℕ} (d : Fin r → ZMod 3) (hd : ∀ i, d i = 0)
    (k : Fin r → ZMod 3) : parity d k = 0 := by
  unfold parity
  simp [hd]

/-- The scaled indicator at a slot with invertible degree realizes any
prescribed parity value. -/
theorem parity_indicator {r : ℕ} (d : Fin r → ZMod 3) (i₀ : Fin r)
    (hd : d i₀ ≠ 0) (e : ZMod 3) :
    parity d (fun j => if j = i₀ then e * (d i₀)⁻¹ else 0) = e := by
  unfold parity
  simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [mul_comm (d i₀), mul_assoc, inv_mul_cancel₀ hd, mul_one]

/-- Uniformity: if some degree is a unit mod 3, then each of the three
parity classes contains exactly `3^(r-1)` sheet-choices — the rational
lifts distribute uniformly over the three components of V¹. -/
theorem uniformity {r : ℕ} (d : Fin r → ZMod 3) (i₀ : Fin r)
    (hd : d i₀ ≠ 0) (c : ZMod 3) :
    (univ.filter fun k : Fin r → ZMod 3 => parity d k = c).card =
      3 ^ (r - 1) := by
  classical
  have key : ∀ c₁ c₂ : ZMod 3,
      (univ.filter fun k : Fin r → ZMod 3 => parity d k = c₁).card =
      (univ.filter fun k : Fin r → ZMod 3 => parity d k = c₂).card := by
    intro c₁ c₂
    set δ : Fin r → ZMod 3 :=
      fun j => if j = i₀ then (c₂ - c₁) * (d i₀)⁻¹ else 0 with hδdef
    have hpd : parity d δ = c₂ - c₁ := parity_indicator d i₀ hd (c₂ - c₁)
    apply Finset.card_bij (fun k _ => k + δ)
    · intro k hk
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
      rw [parity_add, hk, hpd]
      ring
    · intro k₁ _ k₂ _ h
      exact add_right_cancel h
    · intro k hk
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
      refine ⟨k - δ, ?_, sub_add_cancel _ _⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      have h2 := parity_add d (k - δ) δ
      rw [sub_add_cancel, hk, hpd] at h2
      have h3 : parity d (k - δ) = c₂ - (c₂ - c₁) := by
        rw [eq_sub_iff_add_eq]
        exact h2.symm
      calc parity d (k - δ) = c₂ - (c₂ - c₁) := h3
        _ = c₁ := by ring
  have total : ∑ c' : ZMod 3,
      (univ.filter fun k : Fin r → ZMod 3 => parity d k = c').card = 3 ^ r := by
    rw [← Finset.card_eq_sum_card_fiberwise
        (fun (x : Fin r → ZMod 3) (_ : x ∈ univ) => mem_univ (parity d x))]
    rw [Finset.card_univ, Fintype.card_fun, ZMod.card, Fintype.card_fin]
  have eq3 : (3 : ℕ) * (univ.filter fun k : Fin r → ZMod 3 =>
      parity d k = c).card = 3 ^ r := by
    have hsum : ∑ c' : ZMod 3, (univ.filter fun k : Fin r → ZMod 3 =>
        parity d k = c').card =
        3 * (univ.filter fun k : Fin r → ZMod 3 => parity d k = c).card := by
      rw [Finset.sum_congr rfl fun c' _ => key c' c, Finset.sum_const,
          smul_eq_mul, Finset.card_univ, ZMod.card]
    rw [← hsum]
    exact total
  have hr : 0 < r := i₀.pos
  have hpow : 3 ^ r = 3 * 3 ^ (r - 1) := by
    conv_lhs => rw [show r = (r - 1) + 1 by omega]
    rw [pow_succ]
    ring
  omega

end MuThreePrymParity
