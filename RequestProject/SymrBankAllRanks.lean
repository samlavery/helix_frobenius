import RequestProject.HeckeMultiplicativityWire
import RequestProject.GlobalHelixCPSDualPair

/-!
# The Sym^r bank at every rank: one seed structure, all ranks

The rank-uniform coefficient object of the program.  From the single typed seed
package `HeckeEigenData` (which is rank-independent — it speaks only of the GL(2)
seed), this file builds, for EVERY rank `r` simultaneously:

* `symrCoeff r α j` — the Sym^r-Satake local trace at level `j`: the complete
  homogeneous symmetric function of the `r+1` clock weights `α^{r−2i}`, defined as
  the house's literal local Euler coefficient (`radialLocalEulerCoeff` of
  `symClockWeight r α`) — the same object the CPS banks read, at every rank.
* `symrBank H r` — **the global Sym^r bank**: the multiplicative arithmetic function
  whose local factors are the Sym^r-Satake traces of the lifted seed,
  `symrBank H r (p^j) = symrCoeff r (α_p) j` (`symrBank_prime_pow`), multiplicative
  (`symrBank_isMultiplicative`) — the coefficient side of the rank-`r` rung, for all
  `r`, from one structure.
* `symrCoeff_one_eq` / `symrBank_one_rank` — **the rank-1 anchor**: the local traces
  at `r = 1` are the seed clock (`U_j`), and the rank-1 slice of the bank IS the
  Deligne-normalized seed itself: `symrBank H 1 = seedNorm f` — the bank family
  begins at the seed, as functoriality demands.

Proven in this file: everything above, unconditionally given the structure.  Not in
this file: the rank-2 bank-level identification `symrBank H 2 = sym2Bank f` — its two
inputs are multiplicativity of `sym2Bank` and the `Fin 3`-antidiagonal/triangle
reindex tying `symrCoeff 2` to `Sym2Identification.sym2Coeff` (whose triangle form is
Brick 1's `sym2Coeff_eq_clockWeight_homogeneous`); both are finite algebra over the
compiled corpus.  Analytic statements (summability half-planes, Euler products, the
per-rank registration) are likewise not touched here.
-/

open ArithmeticFunction Finset Complex UpperHalfPlane
open scoped MatrixGroups

namespace CriticalLinePhasor.SymrBank

open CriticalLinePhasor.Sym2Identification
open CriticalLinePhasor.Sym2Wire
open CriticalLinePhasor.GlobalHelix

variable {k : ℤ} {f : CuspForm 𝒮ℒ k}

/-! ## The local traces at every rank -/

/-- The Sym^r-Satake local trace at level `j`: the complete homogeneous symmetric
function of the `r+1` clock weights — the house's literal local Euler coefficient of
the Sym^r clock bank. -/
noncomputable def symrCoeff (r : ℕ) (α : ℂ) (j : ℕ) : ℂ :=
  radialLocalEulerCoeff (fun i : Fin (r + 1) => symClockWeight r α (i : ℕ)) j

@[simp] theorem symrCoeff_zero (r : ℕ) (α : ℂ) : symrCoeff r α 0 = 1 := by
  classical
  unfold symrCoeff CriticalLinePhasor.GlobalHelix.radialLocalEulerCoeff
  simp

/-- **The rank-1 anchor, local layer**: the Sym¹ traces are the seed clock,
`symrCoeff 1 α j = U_j(α)`. -/
theorem symrCoeff_one_eq (α : ℂ) (hα : α ≠ 0) (j : ℕ) :
    symrCoeff 1 α j = seedCoeff α j := by
  classical
  unfold symrCoeff CriticalLinePhasor.GlobalHelix.radialLocalEulerCoeff seedCoeff
  refine Finset.sum_nbij' (fun l => l 1)
    (fun i => Finsupp.single 0 (j - i) + Finsupp.single 1 i) ?_ ?_ ?_ ?_ ?_
  · intro l hl
    simp only [Finset.mem_finsuppAntidiag] at hl
    have hsum : l 0 + l 1 = j := by
      have := hl.1
      rwa [Fin.sum_univ_two] at this
    simp only [Finset.mem_range]
    omega
  · intro i hi
    simp only [Finset.mem_finsuppAntidiag]
    have hij : i ≤ j := by
      have := Finset.mem_range.mp hi
      omega
    refine ⟨?_, Finset.subset_univ _⟩
    rw [Fin.sum_univ_two]
    simp only [Finsupp.add_apply, Finsupp.single_apply]
    norm_num
    omega
  · intro l hl
    simp only [Finset.mem_finsuppAntidiag] at hl
    have hsum : l 0 + l 1 = j := by
      have := hl.1
      rwa [Fin.sum_univ_two] at this
    ext i
    fin_cases i <;>
      simp only [Finsupp.add_apply, Finsupp.single_apply] <;>
      norm_num <;>
      omega
  · intro i hi
    simp only [Finsupp.add_apply, Finsupp.single_apply]
    norm_num
  · intro l hl
    simp only [Finset.mem_finsuppAntidiag] at hl
    have hsum : l 0 + l 1 = j := by
      have := hl.1
      rwa [Fin.sum_univ_two] at this
    rw [Fin.prod_univ_two]
    show symClockWeight 1 α 0 ^ l 0 * symClockWeight 1 α 1 ^ l 1 = _
    unfold symClockWeight
    rw [show ((1 : ℕ) : ℤ) - 2 * ((0 : ℕ) : ℤ) = 1 from by norm_num,
      show ((1 : ℕ) : ℤ) - 2 * ((1 : ℕ) : ℤ) = -1 from by norm_num]
    rw [← zpow_natCast (α ^ (1 : ℤ)) (l 0), ← zpow_natCast (α ^ (-1 : ℤ)) (l 1),
      ← zpow_mul, ← zpow_mul, ← zpow_add₀ hα]
    congr 1
    push_cast
    omega

/-! ## The global bank at every rank -/

/-- **The Sym^r bank**: the multiplicative extension of the Sym^r-Satake local traces
of the lifted seed — one seed structure, every rank. -/
noncomputable def symrBank (H : HeckeEigenData f) (r : ℕ) : ArithmeticFunction ℂ :=
  ⟨fun n => if n = 0 then 0 else
    ∏ p ∈ n.primeFactors,
      (if hp : p.Prime then symrCoeff r (H.satake hp) (n.factorization p) else 1),
   by simp⟩

theorem symrBank_apply (H : HeckeEigenData f) (r : ℕ) {n : ℕ} (hn : n ≠ 0) :
    symrBank H r n = ∏ p ∈ n.primeFactors,
      (if hp : p.Prime then symrCoeff r (H.satake hp) (n.factorization p) else 1) := by
  show (if n = 0 then 0 else _) = _
  rw [if_neg hn]

@[simp] theorem symrBank_one (H : HeckeEigenData f) (r : ℕ) :
    symrBank H r 1 = 1 := by
  rw [symrBank_apply H r one_ne_zero]
  simp

/-- The local factors of the bank are the Sym^r-Satake traces, at every rank and
every prime power. -/
theorem symrBank_prime_pow (H : HeckeEigenData f) (r : ℕ) {p : ℕ} (hp : p.Prime)
    (j : ℕ) :
    symrBank H r (p ^ j) = symrCoeff r (H.satake hp) j := by
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · simp
  · have hpj : (p : ℕ) ^ j ≠ 0 := pow_ne_zero _ hp.pos.ne'
    rw [symrBank_apply H r hpj]
    have hpf : ((p : ℕ) ^ j).primeFactors = {p} :=
      Nat.primeFactors_prime_pow hj.ne' hp
    rw [hpf, Finset.prod_singleton, dif_pos hp, Nat.Prime.factorization_pow hp,
      Finsupp.single_apply]
    simp

/-- **The bank is multiplicative at every rank** — coprime factorizations split the
prime-factor product. -/
theorem symrBank_isMultiplicative (H : HeckeEigenData f) (r : ℕ) :
    (symrBank H r).IsMultiplicative := by
  constructor
  · exact symrBank_one H r
  · intro m n hmn
    rcases eq_or_ne m 0 with rfl | hm
    · have hn1 : n = 1 := by
        have := hmn
        rwa [Nat.coprime_zero_left] at this
      subst hn1
      simp
    rcases eq_or_ne n 0 with rfl | hn
    · have hm1 : m = 1 := by
        have := hmn
        rwa [Nat.coprime_zero_right] at this
      subst hm1
      simp
    have hmn0 : m * n ≠ 0 := mul_ne_zero hm hn
    rw [symrBank_apply H r hmn0, symrBank_apply H r hm, symrBank_apply H r hn,
      Nat.primeFactors_mul hm hn]
    have hdisj : Disjoint m.primeFactors n.primeFactors :=
      Nat.Coprime.disjoint_primeFactors hmn
    rw [Finset.prod_union hdisj]
    refine congrArg₂ (· * ·) ?_ ?_
    · refine Finset.prod_congr rfl fun p hpm => ?_
      have hp : p.Prime := Nat.prime_of_mem_primeFactors hpm
      rw [dif_pos hp, dif_pos hp]
      congr 1
      rw [Nat.factorization_mul hm hn]
      have hnp : n.factorization p = 0 := by
        rw [← Nat.support_factorization] at hpm
        have hpn : p ∉ n.primeFactors := Finset.disjoint_left.mp hdisj
          (by rwa [Nat.support_factorization] at hpm)
        rw [← Nat.support_factorization] at hpn
        exact Finsupp.notMem_support_iff.mp hpn
      simp [hnp]
    · refine Finset.prod_congr rfl fun p hpn => ?_
      have hp : p.Prime := Nat.prime_of_mem_primeFactors hpn
      rw [dif_pos hp, dif_pos hp]
      congr 1
      rw [Nat.factorization_mul hm hn]
      have hmp : m.factorization p = 0 := by
        have hpm : p ∉ m.primeFactors := Finset.disjoint_right.mp hdisj hpn
        rw [← Nat.support_factorization] at hpm
        exact Finsupp.notMem_support_iff.mp hpm
      simp [hmp]

/-! ## The rank-1 anchor: the bank family begins at the seed -/

/-- The Deligne-normalized seed: `λ_n = a_n / n^{(k−1)/2}`, as an arithmetic
function. -/
noncomputable def seedNorm (f : CuspForm 𝒮ℒ k) : ArithmeticFunction ℂ :=
  toArithmeticFunction fun n =>
    (qExpansion 1 f).coeff n / (((n : ℝ) ^ (((k : ℝ) - 1) / 2) : ℝ) : ℂ)

theorem seedNorm_apply {n : ℕ} (hn : n ≠ 0) :
    seedNorm f n =
      (qExpansion 1 f).coeff n / (((n : ℝ) ^ (((k : ℝ) - 1) / 2) : ℝ) : ℂ) := by
  rw [seedNorm, toArithmeticFunction]
  simp only [ArithmeticFunction.coe_mk, if_neg hn]

/-- The normalized seed at prime powers is the seed clock: `λ_{p^j} = U_j(α_p)`. -/
theorem seedNorm_prime_pow (H : HeckeEigenData f) {p : ℕ} (hp : p.Prime) (j : ℕ) :
    seedNorm f (p ^ j) = seedCoeff (H.satake hp) j := by
  have hpj : (p : ℕ) ^ j ≠ 0 := pow_ne_zero _ hp.pos.ne'
  have hppos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.pos
  rw [seedNorm_apply hpj, H.coeff_prime_pow hp j]
  have hscale : ((((p ^ j : ℕ) : ℝ) ^ (((k : ℝ) - 1) / 2) : ℝ) : ℂ) =
      primeScale k p ^ j := by
    unfold primeScale
    rw [← Complex.ofReal_pow]
    congr 1
    rw [show (((p ^ j : ℕ) : ℝ)) = (p : ℝ) ^ (j : ℕ) from by push_cast; rfl,
      ← Real.rpow_natCast ((p : ℝ)) j, ← Real.rpow_mul hppos.le,
      ← Real.rpow_natCast ((p : ℝ) ^ (((k : ℝ) - 1) / 2)) j,
      ← Real.rpow_mul hppos.le]
    congr 1
    ring
  rw [hscale, mul_div_assoc, mul_comm,
    div_mul_cancel₀ _ (pow_ne_zero _ (primeScale_ne_zero hp))]

/-- The normalized seed is multiplicative — coprime Hecke multiplicativity through
the normalization. -/
theorem seedNorm_isMultiplicative (H : HeckeEigenData f) :
    (seedNorm f).IsMultiplicative := by
  constructor
  · rw [seedNorm_apply one_ne_zero, H.one]
    norm_num
  · intro m n hmn
    rcases eq_or_ne m 0 with rfl | hm
    · have hn1 : n = 1 := by rwa [Nat.coprime_zero_left] at hmn
      subst hn1
      simp
    rcases eq_or_ne n 0 with rfl | hn
    · have hm1 : m = 1 := by rwa [Nat.coprime_zero_right] at hmn
      subst hm1
      simp
    have hmn0 : m * n ≠ 0 := mul_ne_zero hm hn
    have hmr : (0 : ℝ) < (m : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero hm
    have hnr : (0 : ℝ) < (n : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero hn
    rw [seedNorm_apply hmn0, seedNorm_apply hm, seedNorm_apply hn,
      H.coprime_mul m n hmn]
    have hsplit : (((m * n : ℕ) : ℝ) ^ (((k : ℝ) - 1) / 2) : ℝ) =
        ((m : ℝ) ^ (((k : ℝ) - 1) / 2)) * ((n : ℝ) ^ (((k : ℝ) - 1) / 2)) := by
      rw [show (((m * n : ℕ) : ℝ)) = (m : ℝ) * (n : ℝ) from by push_cast; rfl]
      exact Real.mul_rpow hmr.le hnr.le
    rw [hsplit]
    push_cast
    ring

/-- **The rank-1 anchor**: the rank-1 slice of the bank family IS the normalized
seed — `symrBank H 1 = seedNorm f`.  Two multiplicative functions agreeing on prime
powers agree; the prime-power agreement is the Satake lift. -/
theorem symrBank_one_rank (H : HeckeEigenData f) :
    symrBank H 1 = seedNorm f := by
  rw [IsMultiplicative.eq_iff_eq_on_prime_powers _ (symrBank_isMultiplicative H 1)
    _ (seedNorm_isMultiplicative H)]
  intro p i hp
  rw [symrBank_prime_pow H 1 hp i, seedNorm_prime_pow H hp i,
    symrCoeff_one_eq _ (H.satake_ne_zero hp) i]

end CriticalLinePhasor.SymrBank

#print axioms CriticalLinePhasor.SymrBank.symrCoeff_zero
#print axioms CriticalLinePhasor.SymrBank.symrCoeff_one_eq
#print axioms CriticalLinePhasor.SymrBank.symrBank_prime_pow
#print axioms CriticalLinePhasor.SymrBank.symrBank_isMultiplicative
#print axioms CriticalLinePhasor.SymrBank.seedNorm_prime_pow
#print axioms CriticalLinePhasor.SymrBank.seedNorm_isMultiplicative
#print axioms CriticalLinePhasor.SymrBank.symrBank_one_rank