import RequestProject.CPSEdgeProductBound3D
import RequestProject.CPSEdgeNonvanishingEngine3D

/-!
# Assembly: the Mertens product bound and bank edge nonvanishing

The primewise assembly of the per-prime Mertens-square positivity into the
product bound consumed by the edge-nonvanishing engine, and the combined
capstone.  For a tempered self-dual bank `α` (unit roots, real power sums):

* `bankEulerReadout α` is the exponential of the primewise `−log` Euler
  factor sum — the analytic face of the Euler product on `Re s > 1`;
* `norm_bank_product_ge_one` is the de la Vallée Poussin bound
  `1 ≤ ‖ζ(σ)‖²·‖D(σ)‖·‖C(σ+iy)‖⁴·‖D(σ+2iy)‖` with `D` the diagonal
  pair-bank readout — exponential of the termwise Mertens square;
* `bank_edge_nonvanishing` combines the bound with the engine: any entire
  function agreeing with the bank readout on `Re s > 1`, with any
  continuous companion agreeing with the pair readout there, has no zero
  on `Re s = 1`.

The remaining seam to the CPS tower is exactly the two `EqOn` hypotheses:
the identification of the retained standard continuations with the bank
readouts on `Re s > 1`.  No `axiom`, no `sorry`.
-/

open Complex

namespace CriticalLinePhasor.ThreeDConverse

variable {m : ℕ}

/-- The bank Euler logarithm: the primewise sum of `−log` Euler factors of
the tempered bank. -/
noncomputable def bankEulerLog {ι : Type*} [Fintype ι]
    (α : Nat.Primes → ι → ℂ) (s : ℂ) : ℂ :=
  ∑' p : Nat.Primes, ∑ i, -Complex.log (1 - (p : ℂ) ^ (-s) * α p i)

/-- The bank Euler readout: the exponential of the bank Euler logarithm. -/
noncomputable def bankEulerReadout {ι : Type*} [Fintype ι]
    (α : Nat.Primes → ι → ℂ) (s : ℂ) : ℂ :=
  Complex.exp (bankEulerLog α s)

/-- The diagonal Rankin--Selberg pair bank `{αᵢ·αₖ}`. -/
def pairBank (α : Nat.Primes → Fin m → ℂ) :
    Nat.Primes → Fin m × Fin m → ℂ :=
  fun p ik => α p ik.1 * α p ik.2

theorem pairBank_norm (α : Nat.Primes → Fin m → ℂ)
    (hα : ∀ p i, ‖α p i‖ = 1) :
    ∀ (p : Nat.Primes) (ik : Fin m × Fin m), ‖pairBank α p ik‖ = 1 := by
  intro p ik
  rw [pairBank, norm_mul, hα p ik.1, hα p ik.2, one_mul]

/-- Summability of the primewise `−log` Euler factor sums for a unit bank
on `Re s > 1`. -/
theorem summable_bank_neg_log {ι : Type*} [Fintype ι]
    {α : Nat.Primes → ι → ℂ} (hα : ∀ p i, ‖α p i‖ = 1)
    {s : ℂ} (hs : 1 < s.re) :
    Summable fun p : Nat.Primes =>
      ∑ i, -Complex.log (1 - (p : ℂ) ^ (-s) * α p i) := by
  refine summable_sum fun i _ => ?_
  have hbound : ∀ p : Nat.Primes,
      ‖(p : ℂ) ^ (-s) * α p i‖ ≤ (p : ℝ) ^ (-s).re := by
    intro p
    rw [norm_mul, hα p i, mul_one,
      norm_natCast_cpow_of_re_ne_zero _ (re_neg_ne_zero_of_one_lt_re hs)]
  refine ((Nat.Primes.summable_rpow.mpr ?_).of_nonneg_of_le
    (fun _ => norm_nonneg _) hbound).of_norm.clog_one_sub.neg
  simp only [neg_re, neg_lt_neg_iff, hs]

/-- The three abscissas along the Mertens contour all lie right of `1`. -/
theorem one_lt_re_triple {σ : ℝ} (hσ : 1 < σ) (y : ℝ) :
    1 < ((σ : ℂ)).re ∧ 1 < ((σ : ℂ) + y * I).re
      ∧ 1 < ((σ : ℂ) + 2 * y * I).re := by
  refine ⟨by simpa using hσ, ?_, ?_⟩ <;>
    · simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im,
        mul_one, zero_sub, mul_im, zero_mul, add_zero, re_ofNat, im_ofNat,
        sub_zero, zero_add, neg_zero]
      simpa using hσ

/-- **The Mertens product bound for a tempered self-dual bank.**  For
`σ > 1`, the ζ-square, the diagonal pair readout, the fourth power of the
twisted bank readout, and the double-twisted pair readout multiply to at
least `1`. -/
theorem norm_bank_product_ge_one (α : Nat.Primes → Fin m → ℂ)
    (hα : ∀ p i, ‖α p i‖ = 1)
    (hreal : ∀ (p : Nat.Primes) (n : ℕ), (∑ i, α p i ^ n).im = 0)
    {σ : ℝ} (hσ : 1 < σ) (y : ℝ) :
    1 ≤ ‖riemannZeta (σ : ℂ)‖ ^ 2
      * ‖bankEulerReadout (pairBank α) (σ : ℂ)‖
      * ‖bankEulerReadout α ((σ : ℂ) + y * I)‖ ^ 4
      * ‖bankEulerReadout (pairBank α) ((σ : ℂ) + 2 * y * I)‖ := by
  obtain ⟨h₀, h₁, h₂⟩ := one_lt_re_triple hσ y
  -- summable log families
  have H₀ : Summable fun p : Nat.Primes =>
      -Complex.log (1 - (p : ℂ) ^ (-(σ : ℂ))) := by
    have := summable_bank_neg_log (ι := Fin 1)
      (α := fun _ _ => (1 : ℂ)) (fun _ _ => norm_one) h₀
    simpa using this
  have HD : Summable fun p : Nat.Primes =>
      ∑ ik : Fin m × Fin m,
        -Complex.log (1 - (p : ℂ) ^ (-(σ : ℂ)) * pairBank α p ik) :=
    summable_bank_neg_log (pairBank_norm α hα) h₀
  have HC : Summable fun p : Nat.Primes =>
      ∑ i, -Complex.log (1 - (p : ℂ) ^ (-((σ : ℂ) + y * I)) * α p i) :=
    summable_bank_neg_log hα h₁
  have HD2 : Summable fun p : Nat.Primes =>
      ∑ ik : Fin m × Fin m,
        -Complex.log
          (1 - (p : ℂ) ^ (-((σ : ℂ) + 2 * y * I)) * pairBank α p ik) :=
    summable_bank_neg_log (pairBank_norm α hα) h₂
  have hsum₀ := (hasSum_re H₀.hasSum).summable.mul_left 2
  have hsumD := (hasSum_re HD.hasSum).summable
  have hsumC := (hasSum_re HC.hasSum).summable.mul_left 4
  have hsumD2 := (hasSum_re HD2.hasSum).summable
  -- express everything as exponentials
  rw [← riemannZeta_eulerProduct_exp_log h₀]
  simp only [bankEulerReadout, bankEulerLog, norm_exp]
  rw [re_tsum H₀, re_tsum HD, re_tsum HC, re_tsum HD2,
    ← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add,
    ← Real.exp_add, Real.one_le_exp_iff, ← tsum_mul_left, ← tsum_mul_left]
  push_cast
  rw [← hsum₀.tsum_add hsumD, ← (hsum₀.add hsumD).tsum_add hsumC,
    ← ((hsum₀.add hsumD).add hsumC).tsum_add hsumD2]
  refine tsum_nonneg fun p => ?_
  -- per-prime instantiation
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast p.2.two_le
  have hppos : (0 : ℝ) < (p : ℝ) := by linarith
  set a : ℝ := (p : ℝ) ^ (-σ) with ha
  have ha₀ : 0 ≤ a := Real.rpow_nonneg (le_of_lt hppos) _
  have ha₁ : a < 1 := by
    rw [ha, Real.rpow_neg (le_of_lt hppos), inv_lt_one_iff₀]
    right
    exact Real.one_lt_rpow (by linarith) (by linarith)
  have hpc : ((p : ℂ)) = (((p : ℝ)) : ℂ) := by norm_cast
  set z : ℂ := (p : ℂ) ^ (-(y * I) : ℂ) with hz'
  have hz : ‖z‖ = 1 := by
    rw [hz', hpc, norm_cpow_eq_rpow_re_of_pos hppos]
    simp
  -- cast identities for the three Euler arguments
  have hcast0 : (p : ℂ) ^ (-(σ : ℂ)) = ((a : ℝ) : ℂ) := by
    rw [ha, hpc, Complex.ofReal_cpow (le_of_lt hppos), ofReal_neg]
  have hcast1 : (p : ℂ) ^ (-((σ : ℂ) + y * I))
      = ((a : ℝ) : ℂ) * z := by
    rw [show -((σ : ℂ) + y * I) = -(σ : ℂ) + -(y * I) by ring,
      cpow_add _ _ (by exact_mod_cast p.2.pos.ne'), hcast0, hz']
  have hcast2 : (p : ℂ) ^ (-((σ : ℂ) + 2 * y * I))
      = ((a : ℝ) : ℂ) * z ^ 2 := by
    rw [show -((σ : ℂ) + 2 * y * I) = -(σ : ℂ) + (2 : ℕ) * -(y * I) by
        push_cast; ring,
      cpow_add _ _ (by exact_mod_cast p.2.pos.ne'), hcast0, hz',
      cpow_nat_mul]
  -- convert the pair sums to double sums and close with the core
  have hcore := re_log_comb_nonneg_bank (α p) (hα p) (hreal p) ha₀ ha₁ hz
  have hDpair : (∑ ik : Fin m × Fin m,
      -Complex.log (1 - (p : ℂ) ^ (-(σ : ℂ)) * pairBank α p ik))
      = ∑ i, ∑ k, -Complex.log (1 - ((a : ℝ) : ℂ) * (α p i * α p k)) := by
    rw [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro k _
    rw [hcast0]
    rfl
  have hD2pair : (∑ ik : Fin m × Fin m,
      -Complex.log
        (1 - (p : ℂ) ^ (-((σ : ℂ) + 2 * y * I)) * pairBank α p ik))
      = ∑ i, ∑ k,
          -Complex.log (1 - ((a : ℝ) : ℂ) * (α p i * α p k * z ^ 2)) := by
    rw [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro k _
    rw [hcast2, pairBank]
    ring_nf
  have hCtwist : (∑ i, -Complex.log
      (1 - (p : ℂ) ^ (-((σ : ℂ) + y * I)) * α p i))
      = ∑ i, -Complex.log (1 - ((a : ℝ) : ℂ) * (α p i * z)) := by
    apply Finset.sum_congr rfl
    intro i _
    rw [hcast1]
    ring_nf
  rw [hDpair, hCtwist, hD2pair, hcast0]
  simpa using hcore

/-- **Bank edge nonvanishing.**  Any entire function agreeing with the
tempered self-dual bank readout on `Re s > 1`, given any continuous
companion agreeing with the diagonal pair readout there, has no zero on the
line `Re s = 1`.  This is the engine fed by the Mertens product bound; the
two `EqOn` hypotheses are the identification seam to the CPS tower. -/
theorem bank_edge_nonvanishing (α : Nat.Primes → Fin m → ℂ)
    (hα : ∀ p i, ‖α p i‖ = 1)
    (hreal : ∀ (p : Nat.Primes) (n : ℕ), (∑ i, α p i ^ n).im = 0)
    {C D : ℂ → ℂ} (hC : Differentiable ℂ C) (hD : Continuous D)
    (hCeq : Set.EqOn C (bankEulerReadout α) {s : ℂ | 1 < s.re})
    (hDeq : Set.EqOn D (bankEulerReadout (pairBank α)) {s : ℂ | 1 < s.re})
    (y : ℝ) :
    C (1 + y * I) ≠ 0 := by
  apply edge_nonvanishing_of_product_bound hC hD
  intro σ hσ _
  obtain ⟨h₀, h₁, h₂⟩ := one_lt_re_triple hσ y
  rw [hCeq (Set.mem_setOf.mpr h₁), hDeq (Set.mem_setOf.mpr h₀),
    hDeq (Set.mem_setOf.mpr h₂)]
  exact norm_bank_product_ge_one α hα hreal hσ y

end CriticalLinePhasor.ThreeDConverse

#print axioms CriticalLinePhasor.ThreeDConverse.summable_bank_neg_log
#print axioms CriticalLinePhasor.ThreeDConverse.norm_bank_product_ge_one
#print axioms CriticalLinePhasor.ThreeDConverse.bank_edge_nonvanishing
