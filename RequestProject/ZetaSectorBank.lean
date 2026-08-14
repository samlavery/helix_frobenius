/-
ZetaSectorBank.lean — the instantiation bridge, first plank (RH_LEDGER 147–149).

The measured P=M law (attempt 100, +11.5σ) concerns ANGLE-SECTOR balance: the zeta
bank's phasors sorted into six μ6 sectors by the angle t·log n, with antipodal sectors
balancing at zeros. Audit 147 found this law has no formal counterpart — the existing
Pchan/Mchan split is by character VALUE and degenerates for ζ (entry 148: name
collision). This file defines the angle-sector decomposition at the CONCRETE zeta
bank — vonMangoldt weights, no character hypotheses, no synthetic stand-ins — and
proves the first rungs: the decomposition is exact (partition), the antipodal pairing
is an involution, the term norms are the weights. The balance law itself is stated as
a named definition (`AngleSectorBalanceLaw`) connected to `riemannZeta`; it is not
asserted in this file.
-/
import Mathlib

open Complex Finset Filter

namespace ZetaSectorBank

/-- The angle coordinate of clock `n` at ordinate `t`: the fractional part of
`t·log n / 2π` — the phasor's position on the unit circle, in `[0,1)`. -/
noncomputable def angleFrac (t : ℝ) (n : ℕ) : ℝ :=
  Int.fract (t * Real.log n / (2 * Real.pi))

lemma angleFrac_nonneg (t : ℝ) (n : ℕ) : 0 ≤ angleFrac t n := Int.fract_nonneg _

lemma angleFrac_lt_one (t : ℝ) (n : ℕ) : angleFrac t n < 1 := Int.fract_lt_one _

/-- The μ6 sector of clock `n` at ordinate `t`: which sixth of the circle the
phasor angle occupies. -/
noncomputable def sectorOf (t : ℝ) (n : ℕ) : Fin 6 :=
  ⟨⌊(6 : ℝ) * angleFrac t n⌋₊, by
    have h0 : (0 : ℝ) ≤ 6 * angleFrac t n := by
      have := angleFrac_nonneg t n; linarith
    have h1 : (6 : ℝ) * angleFrac t n < 6 := by
      have := angleFrac_lt_one t n; linarith
    exact (Nat.floor_lt h0).mpr (by exact_mod_cast h1)⟩

/-- The concrete zeta phasor: weight `Λ(n)/√n`, angle `−t·log n`. -/
noncomputable def zetaTerm (t : ℝ) (n : ℕ) : ℂ :=
  ((ArithmeticFunction.vonMangoldt n / Real.sqrt n : ℝ) : ℂ)
    * Complex.exp (((-(t * Real.log n) : ℝ) : ℂ) * Complex.I)

/-- The zeta phasor bank: the partial sum of the concrete phasors. -/
noncomputable def bank (N : ℕ) (t : ℝ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 N, zetaTerm t n

/-- The sector channel: the sub-bank of phasors currently in sector `j`. -/
noncomputable def sectorChan (j : Fin 6) (N : ℕ) (t : ℝ) : ℂ :=
  ∑ n ∈ (Finset.Icc 1 N).filter (fun n => sectorOf t n = j), zetaTerm t n

/-- **Rung 1 (partition):** the six sector channels decompose the concrete zeta bank
exactly. No character hypotheses; this is the zeta bank itself. -/
theorem sector_partition (N : ℕ) (t : ℝ) :
    ∑ j : Fin 6, sectorChan j N t = bank N t := by
  classical
  unfold sectorChan bank
  exact Finset.sum_fiberwise (Finset.Icc 1 N) (fun n => sectorOf t n) (zetaTerm t)

/-- The antipodal pairing on sectors. -/
def antipode (j : Fin 6) : Fin 6 := j + 3

/-- **Rung 2:** the antipodal pairing is an involution without fixed points. -/
theorem antipode_involutive : Function.Involutive antipode := by
  intro j; fin_cases j <;> rfl

theorem antipode_ne (j : Fin 6) : antipode j ≠ j := by
  fin_cases j <;> decide

/-- **Rung 3 (pair decomposition):** the bank is the sum of the three antipodal
sector pairs. -/
theorem bank_pair_decomposition (N : ℕ) (t : ℝ) :
    bank N t
      = (sectorChan 0 N t + sectorChan 3 N t)
        + (sectorChan 1 N t + sectorChan 4 N t)
        + (sectorChan 2 N t + sectorChan 5 N t) := by
  rw [← sector_partition, Fin.sum_univ_six]
  ring

/-- The antipodal imbalance of the bank at truncation `N`: the formal counterpart of
the measured `B(t)` (attempt 145). -/
noncomputable def imbalance (N : ℕ) (t : ℝ) : ℝ :=
  ‖sectorChan 0 N t - sectorChan 3 N t‖
    + ‖sectorChan 1 N t - sectorChan 4 N t‖
    + ‖sectorChan 2 N t - sectorChan 5 N t‖

theorem imbalance_nonneg (N : ℕ) (t : ℝ) : 0 ≤ imbalance N t := by
  unfold imbalance; positivity

/-- **Rung 4 (term norms):** each phasor's norm is exactly its weight. -/
theorem norm_zetaTerm (t : ℝ) (n : ℕ) :
    ‖zetaTerm t n‖ = ArithmeticFunction.vonMangoldt n / Real.sqrt n := by
  unfold zetaTerm
  rw [norm_mul]
  have h1 : ‖Complex.exp (((-(t * Real.log n) : ℝ) : ℂ) * Complex.I)‖ = 1 := by
    have hre : ((((-(t * Real.log n) : ℝ)) : ℂ) * Complex.I).re = 0 := by
      rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
      ring
    rw [Complex.norm_exp, hre, Real.exp_zero]
  have hnn : (0 : ℝ) ≤ ArithmeticFunction.vonMangoldt n / Real.sqrt n :=
    div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg _)
  rw [h1, mul_one]
  calc ‖(((ArithmeticFunction.vonMangoldt n / Real.sqrt n : ℝ)) : ℂ)‖
      = ‖ArithmeticFunction.vonMangoldt n / Real.sqrt n‖ := by norm_cast
    _ = ArithmeticFunction.vonMangoldt n / Real.sqrt n := by
        rw [Real.norm_eq_abs, abs_of_nonneg hnn]

/-- **Rung 5 (balance transfers to the bank):** if all three antipodal pairs balance
exactly at truncation `N`, the bank collapses onto the doubled half-channels. -/
theorem balanced_bank_eq (N : ℕ) (t : ℝ)
    (h0 : sectorChan 0 N t = sectorChan 3 N t)
    (h1 : sectorChan 1 N t = sectorChan 4 N t)
    (h2 : sectorChan 2 N t = sectorChan 5 N t) :
    bank N t = 2 * (sectorChan 3 N t + sectorChan 4 N t + sectorChan 5 N t) := by
  rw [bank_pair_decomposition, h0, h1, h2]; ring

/-- Sector balance at an ordinate: the antipodal imbalance vanishes in the limit.
The formal object corresponding to the measured μ6 law. DEFINED, not asserted. -/
def SectorBalanceAt (t : ℝ) : Prop :=
  Tendsto (fun N => imbalance N t) atTop (nhds 0)

/-- **The named target of the instantiation bridge:** at every critical-line zero of
`ζ`, the concrete bank balances antipodally. This is the measured law (attempt 100,
+11.5σ; attempt 145: 33% of its content beyond the computable band). Its proof from
the carrier/fiber geometry is the open task of the bridge; nothing in this file
asserts it. This is the first statement in the corpus connecting the sector machinery
to `riemannZeta` itself. -/
def AngleSectorBalanceLaw : Prop :=
  ∀ t : ℝ, riemannZeta (1 / 2 + (t : ℂ) * Complex.I) = 0 → SectorBalanceAt t

/-- **Rung 6 (exact finite balance characterized):** the imbalance vanishes at
truncation `N` iff all three antipodal pairs agree exactly. -/
theorem imbalance_eq_zero_iff (N : ℕ) (t : ℝ) :
    imbalance N t = 0 ↔
      sectorChan 0 N t = sectorChan 3 N t ∧ sectorChan 1 N t = sectorChan 4 N t
        ∧ sectorChan 2 N t = sectorChan 5 N t := by
  unfold imbalance
  constructor
  · intro h
    have na := norm_nonneg (sectorChan 0 N t - sectorChan 3 N t)
    have nb := norm_nonneg (sectorChan 1 N t - sectorChan 4 N t)
    have nc := norm_nonneg (sectorChan 2 N t - sectorChan 5 N t)
    have ha : ‖sectorChan 0 N t - sectorChan 3 N t‖ = 0 := by linarith
    have hb : ‖sectorChan 1 N t - sectorChan 4 N t‖ = 0 := by linarith
    have hc : ‖sectorChan 2 N t - sectorChan 5 N t‖ = 0 := by linarith
    exact ⟨sub_eq_zero.mp (norm_eq_zero.mp ha), sub_eq_zero.mp (norm_eq_zero.mp hb),
      sub_eq_zero.mp (norm_eq_zero.mp hc)⟩
  · rintro ⟨h0, h1, h2⟩
    rw [h0, h1, h2]
    simp

/-- **Rung 7 (the conditional detector):** GRANTING the balance law, persistent
imbalance at an ordinate certifies that `ζ(½ + it) ≠ 0`. The law's first compiled
consequence: the geometry's balance field, if lawful, is a pointwise zero-free
certificate. Conditional on `AngleSectorBalanceLaw` — stated as a hypothesis, exactly
as the house rules require. -/
theorem zeta_ne_zero_of_imbalance_persistent
    (hLaw : AngleSectorBalanceLaw) (t : ℝ) (c : ℝ) (hc : 0 < c)
    (hpers : ∀ᶠ N in atTop, c ≤ imbalance N t) :
    riemannZeta (1 / 2 + (t : ℂ) * Complex.I) ≠ 0 := by
  intro hzero
  have hbal : Tendsto (fun N => imbalance N t) atTop (nhds 0) := hLaw t hzero
  have hp : ∀ᶠ y in nhds (0 : ℝ), y < c := by
    filter_upwards [Iio_mem_nhds hc] with y hy using hy
  have h1 : ∀ᶠ N in atTop, imbalance N t < c := hbal.eventually hp
  obtain ⟨N, hlt, hge⟩ := (h1.and hpers).exists
  linarith

end ZetaSectorBank

#print axioms ZetaSectorBank.sector_partition
#print axioms ZetaSectorBank.bank_pair_decomposition
#print axioms ZetaSectorBank.norm_zetaTerm
#print axioms ZetaSectorBank.balanced_bank_eq
#print axioms ZetaSectorBank.antipode_involutive
#print axioms ZetaSectorBank.imbalance_eq_zero_iff
#print axioms ZetaSectorBank.zeta_ne_zero_of_imbalance_persistent
