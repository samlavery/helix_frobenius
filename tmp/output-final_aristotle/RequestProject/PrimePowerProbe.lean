import RequestProject.ClosedForm
import RequestProject.ChiralCup

/-!
# The prime-power probe helix: a von Mangoldt measurement channel

This file implements the *prime-power probe* architecture requested in the project notes.  The
guiding principle is the classification test recorded throughout this project: for each target we
ask only whether discharging it would **assume RH** or be **circular**; if neither, it is a valid
unconditional target and we prove it.  Nothing here assumes the Riemann Hypothesis (or GRH), and
nothing here is circular.  The genuine RH content — that *all* critical-line crossings are
arithmetic zeros — is **neither assumed nor proved**; what is proved is the unconditional
"two-ledger" bookkeeping that the architecture actually requires.

## Two ledgers, not one grid

* **Helix / crossing grid = geometry of cancellation.**  This is the chiral-cup Gram machinery of
  `RequestProject.ChiralCup` / `RequestProject.CupIdentity`: the opposite-handed defect operator
  `Dop` and the positive Gram form `Cup F G = ⟪Dop F, Dop G⟫`.  The geometry is *continuous*: the
  cancellation height `cupHeight F = (Cup F F).re ≥ 0` never cuts exactly at `p^r`.

* **Prime-power ledger = arithmetic forcing weights.**  Prime powers enter only through the
  explicit formula, i.e. the von Mangoldt log-derivative
  `-L'/L(s,χ) = ∑_n Λ(n) χ(n) n^(−s)`, where `Λ(n)` is nonzero only at prime powers.  So the third
  helix is **not** a cutting helix; it is a *measurement channel* that samples the same event.

## The channel

For a Dirichlet character `χ mod q`, a real abscissa `σ` and a real height `h`, the von Mangoldt
measurement channel is
```
M(σ, h) = ∑_{p^r} Λ(p^r) χ(p^r) p^(−rσ) e^(−i h log(p^r))
        = ∑_n χ(n) Λ(n) n^(−(σ + i h)).
```
Each prime power `p^r` contributes a **local Frobenius transport** with

* weight/amplitude `Λ(p^r) · (p^r)^(−σ)`,
* phase `−h · log(p^r)`,
* sign `χ(p^r)`,

and the global transport is the Euler/Mangoldt superposition over all prime powers.

## What is delivered (all unconditional, `sorry`/`axiom`-free)

1. `channelTerm_eq_zero_of_not_isPrimePow` — the channel is supported on prime powers only.
2. `frobeniusLocal_eq_channelTerm`, `vonMangoldtChannel_eq_frobenius_superposition` — the channel
   is exactly the Euler/Mangoldt superposition of local Frobenius contributions (weight, phase,
   sign as above).
3. `vonMangoldtChannel_eq_neg_logDeriv` — **intertwining / arithmetic faithfulness**: for `σ > 1`
   the channel closes onto the explicit-formula side, `M(σ,h) = −L'/L(σ + i h, χ)`.
4. `LFunction_ne_zero_of_one_lt_re`, `noDominance_no_offline_zero` — **no-dominance**: in the
   region of absolute convergence (`σ > 1`) the ledger always closes (`L ≠ 0`), so there is no
   off-line drift there.  (The critical-line statement is RH and is *not* claimed.)
5. `cupHeight_nonneg`, `cup_self_eq_two_energy`, `cup_intertwining` — **geometry ↔ arithmetic
   intertwining**: the continuous chiral-cup energy of the truncated probe fibre equals exactly
   twice the prime-power ledger energy `∑_{n<N} ‖Λ(n) χ(n) n^(−(σ+ih))‖²`.  The geometric cup never
   forces its crests onto prime powers; it merely *samples* the von Mangoldt ledger.

`Mathlib`-only; built on the existing unconditional `ChiralCup`/`CupIdentity` and
`DirichletCarrier` infrastructure.
-/

open Complex DirichletCharacter ArithmeticFunction
open scoped LSeries.notation
open CriticalLinePhasor.CupIdentity

namespace CriticalLinePhasor.PrimePowerProbe
noncomputable section

variable {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)

/-! ## The continuous crossing geometry (helix ledger), re-exported -/

/-- The continuous **crossing defect** `D_H(F) = P_R(F) − J P_L(F)` is the chiral defect `Dop`. -/
def crossingDefect (F : ℕ →₀ ℂ) : ℕ →₀ ℂ := Dop F

/-- The continuous **cancellation height** `Cup_H(F) = ‖D_H(F)‖²`, the real part of the cup form. -/
def cupHeight (F : ℕ →₀ ℂ) : ℝ := (Cup F F).re

/-- The cancellation height is always nonnegative (Gram positivity); the geometry is continuous
and never "cuts" at prime powers. -/
theorem cupHeight_nonneg (F : ℕ →₀ ℂ) : 0 ≤ cupHeight F :=
  CriticalLinePhasor.ChiralCup.cup_positive_semidefinite F

/-! ## The prime-power measurement channel -/

/-- The complex spectral parameter `s = σ + i h`. -/
def specParam (σ h : ℝ) : ℂ := (σ : ℂ) + (h : ℂ) * I

@[simp] theorem specParam_re (σ h : ℝ) : (specParam σ h).re = σ := by
  simp [specParam]

/-- The **local Frobenius contribution** of the integer `n`: sign `χ(n)`, weight `Λ(n)`,
amplitude `n^(−σ)`, phase `−h·log n`.  (For `n = p^r` this is the local Frobenius transport
weight of the prime power.) -/
def frobeniusLocal (σ h : ℝ) (n : ℕ) : ℂ :=
  χ (n : ZMod q) * (Λ n : ℂ) * (((n : ℝ) ^ (-σ) : ℝ) : ℂ) * Complex.exp (-(h * Real.log n) * I)

/-- The **channel term** in canonical Dirichlet form: `χ(n) · Λ(n) · n^(−(σ+ih))`. -/
def channelTerm (σ h : ℝ) (n : ℕ) : ℂ :=
  χ (n : ZMod q) * (Λ n : ℂ) * (n : ℂ) ^ (-(specParam σ h))

/-- The **von Mangoldt measurement channel** `M(σ, h) = ∑_n χ(n) Λ(n) n^(−(σ+ih))`. -/
def vonMangoldtChannel (σ h : ℝ) : ℂ := ∑' n : ℕ, channelTerm χ σ h n

/-! ## 1. Prime-power support: the channel measures only prime powers -/

/-
The channel term vanishes off the prime powers: `Λ(n) ≠ 0 ↔ IsPrimePow n`.
-/
omit [NeZero q] in
theorem channelTerm_eq_zero_of_not_isPrimePow (σ h : ℝ) {n : ℕ} (hn : ¬ IsPrimePow n) :
    channelTerm χ σ h n = 0 := by
  unfold channelTerm; simp +decide [ hn, ArithmeticFunction.vonMangoldt ] ;

/-! ## 2. Euler/Mangoldt superposition of local Frobenius contributions -/

/-
Each channel term **is** its local Frobenius contribution: the same event written with the
amplitude `n^(−σ)` and the phase `e^(−i h log n)` separated out.
-/
omit [NeZero q] in
theorem frobeniusLocal_eq_channelTerm (σ h : ℝ) (n : ℕ) :
    frobeniusLocal χ σ h n = channelTerm χ σ h n := by
  by_cases hn : n = 0 <;> simp_all +decide [ frobeniusLocal, channelTerm, specParam ];
  norm_num [ Complex.cpow_def_of_ne_zero, hn ] ; ring;
  norm_num [ Real.rpow_def_of_pos ( Nat.cast_pos.mpr ( Nat.pos_of_ne_zero hn ) ), Complex.ofReal_log ( Nat.cast_nonneg _ ) ] ; ring;
  rw [ mul_assoc, ← Complex.exp_add ] ; ring

/-
**Euler/Mangoldt superposition.**  The channel is the superposition of the local Frobenius
contributions over all prime powers.
-/
omit [NeZero q] in
theorem vonMangoldtChannel_eq_frobenius_superposition (σ h : ℝ) :
    vonMangoldtChannel χ σ h = ∑' n : ℕ, frobeniusLocal χ σ h n := by
  exact tsum_congr fun n => frobeniusLocal_eq_channelTerm χ σ h n |> Eq.symm

/-! ## 3. Intertwining / arithmetic faithfulness: the ledger closes onto `−L'/L` -/

/-
**Intertwining theorem (arithmetic faithfulness).**  In the region of absolute convergence
`σ > 1`, the prime-power ledger closes onto the explicit-formula side:
`M(σ, h) = −L'/L(σ + i h, χ)`.
-/
omit [NeZero q] in
theorem vonMangoldtChannel_eq_neg_logDeriv (σ h : ℝ) (hσ : 1 < σ) :
    vonMangoldtChannel χ σ h
      = -deriv (L (fun n => χ (n : ZMod q))) (specParam σ h)
          / L (fun n => χ (n : ZMod q)) (specParam σ h) := by
  have hs : 1 < (specParam σ h).re := by rw [specParam_re]; exact hσ
  exact (CriticalLinePhasor.DirichletCarrier.dirichlet_logDeriv_eq_tsum χ hs).symm

/-! ## 4. No-dominance: in the convergence region the ledger always closes -/

/-
For `σ > 1` the Dirichlet `L`-function does not vanish: the denominator of the explicit-formula
ledger is nonzero, so the ledger closes.
-/
theorem LFunction_ne_zero_of_one_lt_re (σ h : ℝ) (hσ : 1 < σ) :
    LFunction χ (specParam σ h) ≠ 0 := by
  apply_rules [ DirichletCharacter.LFunction_ne_zero_of_one_le_re ];
  · exact Or.inr ( ne_of_apply_ne Complex.re ( by norm_num [ specParam_re ] ; linarith ) );
  · exact le_of_lt ( by simpa [ specParam_re ] using hσ )

/-- **No-dominance theorem (convergence region).**  In the half-plane of absolute convergence
`σ > 1` there is no off-line drift: the carrier `L(σ + i h, χ)` never vanishes, so the
explicit-formula ledger closes for every height `h`.  (The critical-line `σ = 1/2` statement is the
Riemann Hypothesis and is *not* asserted here.) -/
theorem noDominance_no_offline_zero (σ h : ℝ) (hσ : 1 < σ) :
    LFunction χ (specParam σ h) ≠ 0 :=
  LFunction_ne_zero_of_one_lt_re χ σ h hσ

/-! ## 5. Geometry ↔ arithmetic intertwining (cup energy = prime-power ledger energy) -/

/-
The chiral-cup self-energy of a fibre is exactly twice its `ℓ²` energy:
`Cup F F = 2·∑_n ‖F n‖²`.  (The two opposite-handed embeddings land on disjoint even/odd sites,
each carrying `‖F n‖`.)
-/
theorem cup_self_eq_two_energy (F : ℕ →₀ ℂ) :
    Cup F F = ((2 * ∑ n ∈ F.support, ‖F n‖ ^ 2 : ℝ) : ℂ) := by
  simp_all +decide [ Cup, inner ];
  simp +decide [ Dop, Finsupp.sum, mul_comm ];
  rw [ show ( iotaR F - Jconj ( iotaL F ) |> Finsupp.support ) = ( F.support.image ( fun n => 2 * n ) ) ∪ ( F.support.image ( fun n => 2 * n + 1 ) ) from ?_ ];
  · rw [ Finset.sum_union ];
    · rw [ Finset.sum_image, Finset.sum_image ] <;> norm_num [ iotaR, iotaL, Jconj ];
      rw [ ← Finset.sum_add_distrib ] ; rw [ Finset.mul_sum ] ; refine' Finset.sum_congr rfl fun x hx => _ ; simp +decide [ Finsupp.embDomain_apply, embR, embL ] ; ring;
      split_ifs <;> norm_num [ Complex.mul_conj, Complex.normSq_eq_norm_sq ] ; ring; all_goals omega;
    · norm_num [ Finset.disjoint_right ];
      intros; omega;
  · ext n; simp +decide [ Finsupp.mem_support_iff ] ;
    unfold iotaR iotaL Jconj; simp +decide [ Finsupp.embDomain_apply ] ;
    split_ifs <;> simp_all +decide [ sub_eq_zero, embR, embL ];
    · grind +splitIndPred;
    · grind;
    · grind +splitIndPred

/-- The **truncated probe fibre**: the prime-power ledger weights at the sites `n < N`. -/
def probeFibre (σ h : ℝ) (N : ℕ) : ℕ →₀ ℂ :=
  ∑ n ∈ Finset.range N, Finsupp.single n (channelTerm χ σ h n)

/-
The probe fibre reads off the channel term at each site below `N`.
-/
omit [NeZero q] in
theorem probeFibre_apply (σ h : ℝ) (N : ℕ) (n : ℕ) :
    (probeFibre χ σ h N) n = if n ∈ Finset.range N then channelTerm χ σ h n else 0 := by
  rw [probeFibre, Finsupp.finsetSum_apply]
  simp only [Finsupp.single_apply]
  rw [Finset.sum_ite_eq' (Finset.range N) n (fun i => channelTerm χ σ h i)]

/-
**Intertwining of the two ledgers.**  The continuous chiral-cup energy of the truncated probe
fibre equals exactly twice the prime-power ledger energy
`∑_{n<N} ‖χ(n) Λ(n) n^(−(σ+ih))‖²`.  The geometry samples the von Mangoldt ledger without forcing
its crests onto prime powers.
-/
omit [NeZero q] in
theorem cup_intertwining (σ h : ℝ) (N : ℕ) :
    Cup (probeFibre χ σ h N) (probeFibre χ σ h N)
      = ((2 * ∑ n ∈ Finset.range N, ‖channelTerm χ σ h n‖ ^ 2 : ℝ) : ℂ) := by
  convert cup_self_eq_two_energy ( probeFibre χ σ h N ) using 1;
  simp +decide [ probeFibre_apply ];
  rw [ Finset.sum_subset ( show ( probeFibre χ σ h N |> Finsupp.support ) ⊆ Finset.range N from ?_ ) ];
  · exact Finset.sum_congr rfl fun x hx => by aesop;
  · simp +contextual [ probeFibre_apply ];
  · intro n hn; contrapose! hn; simp_all +decide [ probeFibre_apply ] ;

end
end CriticalLinePhasor.PrimePowerProbe