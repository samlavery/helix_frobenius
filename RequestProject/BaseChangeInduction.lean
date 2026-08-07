import RequestProject.TransportClosure

/-!
# Base change and automorphic induction: the quadratic rungs

Rungs 1 and 2 of the benchmark ladder, on one engine: **the parity law**
`h_j(w ⊕ (−w)) = [2 ∣ j]·h_{j/2}(w²)` — difference of squares at the Euler-coefficient
level, proven at every rank by induction over the transport-closure Cauchy law.

* `radialLocalEulerCoeff_smul` — homogeneity: scaling the weights by `c` scales level `j`
  by `c^j`; `radialLocalEulerCoeff_single` — one channel of weight `α` carries `α^j`;
* `parity_rank_one` / `parity_law` — the engine, rank one and every rank;
* `radialLocalEulerCoeff_snoc` — a `Fin (d+1)` system is its first-`d` system Cauchy one
  extra channel (the induction step's regrouping, with `sum_even_pairs` the even-support
  contraction);

**Base change** (rung 1), quadratic: `bcBank w χ` is the convolution of the bank with its
`χ`-twisted bank — the coefficients of `L(π,s)·L(π⊗χ,s)`, which is `L(BC_{E/ℚ}π, s)` for
the quadratic extension cut out by `χ`:

* `bcBank_split` — at `χ p = 1` the local factor is the doubled system (two places above
  `p`, each with the original parameter);
* `bcBank_inert` — at `χ p = −1` the local factor is supported on even levels and carries
  the Frobenius-squared system: the original factor at `p^{2s}` with squared parameters —
  the two sides of the Artin factorization, per prime, unconditionally.

**Automorphic induction** (rung 2), quadratic: `aiWeight`/`aiBank` induce a rank-2 system
from a rank-1 quadratic datum (split pair `(γ₁,γ₂)`, inert square roots `(β,−β)`):

* `aiBank_inert` — the induced inert factor is `[2∣j]·(β²)^{j/2}`: the single place's
  rank-1 factor read at the norm grading;
* `aiBank_root_choice` — the bank depends only on `β²`, not the chosen square root;
* `aiBank_twist_invariant` — **the recognition law** `AI(ψ) ⊗ χ = AI(ψ)`: twisting by the
  quadratic sign fixes the bank (split places untouched, inert places swap the roots) —
  the classical fingerprint of an induced representation, at the bank level.

**The eigenform instance**: `seedSystem`/`bankArithmetic_seedSystem` — the rank-1 clock
system of a level-one eigenform carries the Deligne-normalized coefficient bank
(`seedNorm`), and `bcBank_seed_inert` reads off the local data of `BC_{E/ℚ}(f)` at inert
primes: the Frobenius-squared Satake pair `(α_p², α_p⁻²)` on even levels.

No `axiom`, no `sorry`.
-/

open Finset ArithmeticFunction Complex UpperHalfPlane
open scoped MatrixGroups

namespace CriticalLinePhasor.BaseChangeInduction

open CriticalLinePhasor.GlobalHelix CriticalLinePhasor.TransportClosure
open CriticalLinePhasor.CarrierTheta CriticalLinePhasor.Sym2Wire CriticalLinePhasor.SymrBank

variable {ι : Type*} [Fintype ι]
variable {k : ℤ} {f : CuspForm 𝒮ℒ k}


/-- Homogeneity: scaling every weight by `c` scales the level-`j` coefficient by `c^j`. -/
theorem radialLocalEulerCoeff_smul {ι : Type*} [Fintype ι] (c : ℂ) (w : ι → ℂ) (j : ℕ) :
    radialLocalEulerCoeff (fun i => c * w i) j = c ^ j * radialLocalEulerCoeff w j := by
  classical
  unfold radialLocalEulerCoeff
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun l hl => ?_
  simp only [Finset.mem_finsuppAntidiag] at hl
  calc ∏ i, (c * w i) ^ l i
      = ∏ i, c ^ l i * w i ^ l i := by
        refine Finset.prod_congr rfl fun i _ => mul_pow c (w i) (l i)
    _ = (∏ i, c ^ l i) * ∏ i, w i ^ l i := Finset.prod_mul_distrib
    _ = c ^ (∑ i, l i) * ∏ i, w i ^ l i := by
        rw [Finset.prod_pow_eq_pow_sum]
    _ = c ^ j * ∏ i, w i ^ l i := by rw [hl.1]

/-- One channel of weight `α` has level-`j` coefficient `α^j`. -/
theorem radialLocalEulerCoeff_single (α : ℂ) (j : ℕ) :
    radialLocalEulerCoeff (fun _ : Fin 1 => α) j = α ^ j := by
  have h := radialLocalEulerCoeff_smul α (fun _ : Fin 1 => (1 : ℂ)) j
  simp only [mul_one] at h
  rw [h, radialLocalEulerCoeff_unit, mul_one]

/-- The alternating geometric sum. -/
theorem sum_neg_one_pow (j : ℕ) :
    ∑ b ∈ range (j + 1), ((-1 : ℂ)) ^ b = if 2 ∣ j then 1 else 0 := by
  induction j with
  | zero => simp
  | succ j ih =>
      rw [Finset.sum_range_succ, ih]
      rcases Nat.even_or_odd j with ⟨m, hm⟩ | ⟨m, hm⟩
      · rw [if_pos ⟨m, by omega⟩, if_neg (by omega),
          Odd.neg_one_pow ⟨m, by omega⟩]
        ring
      · rw [if_neg (by omega), if_pos ⟨m + 1, by omega⟩,
          Even.neg_one_pow ⟨m + 1, by omega⟩]
        ring

/-- **The rank-1 parity law**: the channel pair `(α, −α)` supports only even levels, with
value `α^j` there — the difference-of-squares law for one Euler factor. -/
theorem parity_rank_one (α : ℂ) (j : ℕ) :
    radialLocalEulerCoeff
        (Sum.elim (fun _ : Fin 1 => α) (fun _ : Fin 1 => -α)) j
      = if 2 ∣ j then α ^ j else 0 := by
  rw [radialLocalEulerCoeff_sumElim]
  have hterm : ∀ a ∈ range (j + 1),
      radialLocalEulerCoeff (fun _ : Fin 1 => α) a *
        radialLocalEulerCoeff (fun _ : Fin 1 => -α) (j - a)
      = α ^ j * ((-1 : ℂ)) ^ (j - a) := by
    intro a ha
    rw [radialLocalEulerCoeff_single, radialLocalEulerCoeff_single, neg_pow]
    have : α ^ a * ((-1 : ℂ) ^ (j - a) * α ^ (j - a))
        = ((-1 : ℂ)) ^ (j - a) * (α ^ a * α ^ (j - a)) := by ring
    rw [this, ← pow_add, Nat.add_sub_cancel' (Nat.lt_succ_iff.mp (mem_range.mp ha))]
    ring
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
  have hrev : ∑ a ∈ range (j + 1), ((-1 : ℂ)) ^ (j - a)
      = ∑ b ∈ range (j + 1), ((-1 : ℂ)) ^ b := by
    refine Finset.sum_nbij' (fun a => j - a) (fun b => j - b) ?_ ?_ ?_ ?_ ?_ <;>
      intro a ha <;> simp only [mem_range] at ha ⊢ <;> omega
  rw [hrev, sum_neg_one_pow]
  split_ifs <;> ring

/-- The empty system: level `0` carries `1`, everything else `0`. -/
theorem radialLocalEulerCoeff_isEmpty {ι : Type*} [Fintype ι] [IsEmpty ι] (j : ℕ) :
    radialLocalEulerCoeff (fun _ : ι => (0 : ℂ)) j = if j = 0 then 1 else 0 := by
  classical
  unfold radialLocalEulerCoeff
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · simp
  · rw [if_neg hj.ne']
    convert Finset.sum_empty
    rw [Finset.eq_empty_iff_forall_notMem]
    intro l hl
    simp only [Finset.mem_finsuppAntidiag] at hl
    have : j = 0 := by rw [← hl.1]; simp
    omega


/-- Even-supported Cauchy sums contract to the half-level Cauchy sum. -/
theorem sum_even_pairs (X Y : ℕ → ℂ) (j : ℕ) :
    ∑ a ∈ range (j + 1),
        (if 2 ∣ a then X (a / 2) else 0) * (if 2 ∣ (j - a) then Y ((j - a) / 2) else 0)
      = if 2 ∣ j then ∑ a' ∈ range (j / 2 + 1), X a' * Y (j / 2 - a') else 0 := by
  rcases Nat.even_or_odd j with ⟨m, hm⟩ | ⟨m, hm⟩
  · have hj2 : 2 ∣ j := ⟨m, by omega⟩
    rw [if_pos hj2]
    have hfilter : ∀ x ∈ range (j + 1),
        (if 2 ∣ x then X (x / 2) else 0) * (if 2 ∣ (j - x) then Y ((j - x) / 2) else 0) ≠ 0
        → 2 ∣ x := by
      intro x _ hne
      by_contra hodd
      rw [if_neg hodd, zero_mul] at hne
      exact hne rfl
    rw [← Finset.sum_filter_of_ne hfilter]
    refine Finset.sum_nbij' (fun a => a / 2) (fun a' => 2 * a') ?_ ?_ ?_ ?_ ?_
    · intro a ha
      simp only [Finset.mem_filter, Finset.mem_range] at ha ⊢
      omega
    · intro a' ha'
      simp only [Finset.mem_filter, Finset.mem_range] at ha' ⊢
      omega
    · intro a ha
      simp only [Finset.mem_filter, Finset.mem_range] at ha
      omega
    · intro a' _
      omega
    · intro a ha
      simp only [Finset.mem_filter, Finset.mem_range] at ha
      obtain ⟨-, ⟨c, hc⟩⟩ := ha
      rw [if_pos ⟨c, hc⟩, if_pos (by omega : 2 ∣ (j - a))]
      congr 2
      omega
  · rw [if_neg (by omega)]
    refine Finset.sum_eq_zero fun a ha => ?_
    simp only [Finset.mem_range] at ha
    rcases Nat.even_or_odd a with ⟨c, hc⟩ | ⟨c, hc⟩
    · rw [if_neg (by omega : ¬ 2 ∣ (j - a)), mul_zero]
    · rw [if_neg (by omega : ¬ 2 ∣ a), zero_mul]

/-- The snoc equivalence with its value law: a system on `Fin (d+1)` is the first-`d`
system together with one extra channel. -/
theorem radialLocalEulerCoeff_snoc (d : ℕ) (w : Fin (d + 1) → ℂ) (j : ℕ) :
    radialLocalEulerCoeff w j
      = ∑ a ∈ range (j + 1),
          radialLocalEulerCoeff (fun i : Fin d => w i.castSucc) a *
            (w (Fin.last d)) ^ (j - a) := by
  have hval : w ∘ (finSumFinEquiv : Fin d ⊕ Fin 1 ≃ Fin (d + 1))
      = Sum.elim (fun i : Fin d => w i.castSucc) (fun _ : Fin 1 => w (Fin.last d)) := by
    funext x
    rcases x with x | x
    · simp [finSumFinEquiv, Fin.castSucc, Function.comp]
    · have h0 : x = 0 := Subsingleton.elim x 0
      subst h0
      have : (finSumFinEquiv : Fin d ⊕ Fin 1 ≃ Fin (d + 1)) (Sum.inr 0) = Fin.last d := by
        apply Fin.ext
        simp [finSumFinEquiv]
      simp [this]
  rw [← radialLocalEulerCoeff_equiv (finSumFinEquiv : Fin d ⊕ Fin 1 ≃ Fin (d + 1)) w j,
    hval, radialLocalEulerCoeff_sumElim]
  exact Finset.sum_congr rfl fun a _ => by rw [radialLocalEulerCoeff_single]

/-- **The parity law at every rank**: the signed double `w ⊕ (−w)` supports only even
levels, where it carries the squared system — difference of squares for Euler data. -/
theorem parity_law (d : ℕ) (w : Fin d → ℂ) (j : ℕ) :
    radialLocalEulerCoeff (Sum.elim w (fun i => -(w i))) j
      = if 2 ∣ j then radialLocalEulerCoeff (fun i => (w i) ^ 2) (j / 2) else 0 := by
  induction d generalizing j with
  | zero =>
      have hLHS : (Sum.elim w (fun i => -(w i))) = (fun _ : Fin 0 ⊕ Fin 0 => (0 : ℂ)) := by
        funext x
        rcases x with x | x <;> exact absurd x.2 (by omega)
      have hRHS : (fun i : Fin 0 => (w i) ^ 2) = (fun _ : Fin 0 => (0 : ℂ)) := by
        funext x
        exact absurd x.2 (by omega)
      rw [hLHS, hRHS, radialLocalEulerCoeff_isEmpty, radialLocalEulerCoeff_isEmpty]
      split_ifs with h1 h2 h3 <;> first | rfl | omega
  | succ d ih =>
      set α := w (Fin.last d) with hαdef
      set w' := (fun i : Fin d => w i.castSucc) with hw'def
      -- regroup the doubled system through the double snoc
      have hgroup : radialLocalEulerCoeff (Sum.elim w (fun i => -(w i))) j
          = ∑ a ∈ range (j + 1),
              radialLocalEulerCoeff (Sum.elim w' (fun i => -(w' i))) a *
                radialLocalEulerCoeff
                  (Sum.elim (fun _ : Fin 1 => α) (fun _ : Fin 1 => -α)) (j - a) := by
        have hval : (Sum.elim w (fun i => -(w i))) ∘
            ((Equiv.sumSumSumComm (Fin d) (Fin 1) (Fin d) (Fin 1)).symm.trans
              (Equiv.sumCongr (finSumFinEquiv : Fin d ⊕ Fin 1 ≃ Fin (d + 1))
                (finSumFinEquiv : Fin d ⊕ Fin 1 ≃ Fin (d + 1))))
            = Sum.elim (Sum.elim w' (fun i => -(w' i)))
                (Sum.elim (fun _ : Fin 1 => α) (fun _ : Fin 1 => -α)) := by
          funext x
          rcases x with (x | x) | (x | x)
          · simp [Equiv.sumSumSumComm, finSumFinEquiv, Fin.castSucc, hw'def]
          · simp [Equiv.sumSumSumComm, finSumFinEquiv, Fin.castSucc, hw'def]
          · have h0 : x = 0 := Subsingleton.elim x 0
            subst h0
            have hlast : (finSumFinEquiv : Fin d ⊕ Fin 1 ≃ Fin (d + 1)) (Sum.inr 0)
                = Fin.last d := by
              apply Fin.ext
              simp [finSumFinEquiv]
            simp [Equiv.sumSumSumComm, hlast, hαdef]
          · have h0 : x = 0 := Subsingleton.elim x 0
            subst h0
            have hlast : (finSumFinEquiv : Fin d ⊕ Fin 1 ≃ Fin (d + 1)) (Sum.inr 0)
                = Fin.last d := by
              apply Fin.ext
              simp [finSumFinEquiv]
            simp [Equiv.sumSumSumComm, hlast, hαdef]
        rw [← radialLocalEulerCoeff_equiv
          ((Equiv.sumSumSumComm (Fin d) (Fin 1) (Fin d) (Fin 1)).symm.trans
            (Equiv.sumCongr (finSumFinEquiv : Fin d ⊕ Fin 1 ≃ Fin (d + 1))
              (finSumFinEquiv : Fin d ⊕ Fin 1 ≃ Fin (d + 1))))
          (Sum.elim w (fun i => -(w i))) j, hval, radialLocalEulerCoeff_sumElim]
      rw [hgroup]
      have hterm : ∀ a ∈ range (j + 1),
          radialLocalEulerCoeff (Sum.elim w' (fun i => -(w' i))) a *
            radialLocalEulerCoeff
              (Sum.elim (fun _ : Fin 1 => α) (fun _ : Fin 1 => -α)) (j - a)
          = (if 2 ∣ a then radialLocalEulerCoeff (fun i => (w' i) ^ 2) (a / 2) else 0) *
            (if 2 ∣ (j - a) then (α ^ 2) ^ ((j - a) / 2) else 0) := by
        intro a ha
        rw [ih w' a, parity_rank_one α (j - a)]
        congr 1
        split_ifs with h
        · obtain ⟨c, hc⟩ := h
          rw [← pow_mul]
          congr 1
          omega
        · rfl
      rw [Finset.sum_congr rfl hterm,
        sum_even_pairs (fun m => radialLocalEulerCoeff (fun i => (w' i) ^ 2) m)
          (fun m => (α ^ 2) ^ m) j]
      split_ifs with hj
      · rw [radialLocalEulerCoeff_snoc d (fun i => (w i) ^ 2) (j / 2)]
      · rfl



/-- **The quadratic base-change bank**: the convolution of the bank with its sign-twisted
bank — the coefficient sequence of `L(π,s)·L(π⊗χ,s)`. -/
noncomputable def bcBank (w : Nat.Primes → ι → ℂ) (χ : Nat.Primes → ℂ) :
    ArithmeticFunction ℂ :=
  coefficientArithmetic (radialGlobalSatakeCoeff w) *
    coefficientArithmetic (radialGlobalSatakeCoeff (fun p i => χ p * w p i))

/-- **Split law**: at a split prime (`χ p = 1`) the base-change factor is the doubled
system — two places above `p`, each carrying the original parameter. -/
theorem bcBank_split (w : Nat.Primes → ι → ℂ) (χ : Nat.Primes → ℂ)
    {p : ℕ} (hp : p.Prime) (hχ : χ ⟨p, hp⟩ = 1) (j : ℕ) :
    bcBank w χ (p ^ j)
      = radialLocalEulerCoeff
          (Sum.elim (w ⟨p, hp⟩) (w ⟨p, hp⟩)) j := by
  unfold bcBank
  rw [mul_apply_prime_pow _ _ hp, radialLocalEulerCoeff_sumElim]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [bankArithmetic_prime_pow _ hp, bankArithmetic_prime_pow _ hp,
    show (fun i => χ ⟨p, hp⟩ * w ⟨p, hp⟩ i) = w ⟨p, hp⟩ from
      funext fun i => by rw [hχ, one_mul]]

/-- **Inert law**: at an inert prime (`χ p = −1`) the base-change factor is supported on
even levels and carries the Frobenius-squared system there — the local factor is the
original factor evaluated at `p^{2s}` with squared Satake parameters. -/
theorem bcBank_inert (w : Nat.Primes → ι → ℂ) (χ : Nat.Primes → ℂ)
    {p : ℕ} (hp : p.Prime) (hχ : χ ⟨p, hp⟩ = -1) (j : ℕ) :
    bcBank w χ (p ^ j)
      = if 2 ∣ j then
          radialLocalEulerCoeff (fun i => (w ⟨p, hp⟩ i) ^ 2) (j / 2) else 0 := by
  classical
  unfold bcBank
  rw [mul_apply_prime_pow _ _ hp]
  -- realize the Cauchy product as the signed double, then apply the parity law
  have hstep : ∀ a ∈ range (j + 1),
      (coefficientArithmetic (radialGlobalSatakeCoeff w)) (p ^ a) *
        (coefficientArithmetic (radialGlobalSatakeCoeff (fun q i => χ q * w q i)))
          (p ^ (j - a))
      = radialLocalEulerCoeff (w ⟨p, hp⟩) a *
          radialLocalEulerCoeff (fun i => -(w ⟨p, hp⟩ i)) (j - a) := by
    intro a _
    rw [bankArithmetic_prime_pow _ hp, bankArithmetic_prime_pow _ hp,
      show (fun i => χ ⟨p, hp⟩ * w ⟨p, hp⟩ i) = fun i => -(w ⟨p, hp⟩ i) from
        funext fun i => by rw [hχ]; ring]
  rw [Finset.sum_congr rfl hstep, ← radialLocalEulerCoeff_sumElim]
  -- reindex the abstract ι-double through an equiv to `Fin card ⊕ Fin card`
  obtain ⟨e⟩ := Fintype.truncEquivFin ι
  have hLHS : (Sum.elim (w ⟨p, hp⟩) (fun i => -(w ⟨p, hp⟩ i)))
      = (Sum.elim (fun i : Fin (Fintype.card ι) => w ⟨p, hp⟩ (e.symm i))
          (fun i : Fin (Fintype.card ι) => -(w ⟨p, hp⟩ (e.symm i)))) ∘
        (Equiv.sumCongr e e) := by
    funext x
    rcases x with x | x <;> simp
  have hRHS : (fun i : ι => (w ⟨p, hp⟩ i) ^ 2)
      = (fun i : Fin (Fintype.card ι) => (w ⟨p, hp⟩ (e.symm i)) ^ 2) ∘ e := by
    funext i
    simp
  rw [hLHS, radialLocalEulerCoeff_equiv (Equiv.sumCongr e e), parity_law, hRHS,
    radialLocalEulerCoeff_equiv e]


/-- **The induced rank-2 weight system** of a quadratic datum: at split primes the two
places' parameters `(γ₁, γ₂)`; at inert primes the two square roots `(β, −β)` of the
single place's parameter. -/
noncomputable def aiWeight (χ : Nat.Primes → ℂ) (γ₁ γ₂ β : Nat.Primes → ℂ) :
    Nat.Primes → Fin 2 → ℂ :=
  fun p => if χ p = 1 then ![γ₁ p, γ₂ p] else ![β p, -(β p)]

/-- **The induced bank.** -/
noncomputable def aiBank (χ : Nat.Primes → ℂ) (γ₁ γ₂ β : Nat.Primes → ℂ) :
    ArithmeticFunction ℂ :=
  coefficientArithmetic (radialGlobalSatakeCoeff (aiWeight χ γ₁ γ₂ β))

/-- **The inert dilation law**: at an inert prime the induced factor is supported on even
levels with value `(β²)^{j/2}` — the rank-1 factor of the quadratic place, read at the
norm grading.  The value depends only on `β²`, the place's parameter. -/
theorem aiBank_inert (χ : Nat.Primes → ℂ) (γ₁ γ₂ β : Nat.Primes → ℂ)
    {p : ℕ} (hp : p.Prime) (hχ : χ ⟨p, hp⟩ ≠ 1) (j : ℕ) :
    aiBank χ γ₁ γ₂ β (p ^ j)
      = if 2 ∣ j then ((β ⟨p, hp⟩) ^ 2) ^ (j / 2) else 0 := by
  unfold aiBank
  rw [bankArithmetic_prime_pow _ hp]
  have hw : aiWeight χ γ₁ γ₂ β ⟨p, hp⟩ = ![β ⟨p, hp⟩, -(β ⟨p, hp⟩)] := by
    unfold aiWeight
    rw [if_neg hχ]
  rw [hw]
  have hpair : (![β ⟨p, hp⟩, -(β ⟨p, hp⟩)] : Fin 2 → ℂ)
      = (Sum.elim (fun _ : Fin 1 => β ⟨p, hp⟩) (fun _ : Fin 1 => -(β ⟨p, hp⟩))) ∘
        (finSumFinEquiv : Fin 1 ⊕ Fin 1 ≃ Fin 2).symm := by
    funext x
    fin_cases x <;> rfl
  rw [hpair, radialLocalEulerCoeff_equiv, parity_rank_one]
  split_ifs with h
  · obtain ⟨c, hc⟩ := h
    rw [← pow_mul]
    congr 1
    omega
  · rfl

/-- **Root-choice invariance**: replacing `β` by `−β` leaves the induced bank unchanged —
only the place parameter `β²` enters. -/
theorem aiBank_root_choice (χ : Nat.Primes → ℂ) (γ₁ γ₂ β : Nat.Primes → ℂ) :
    aiBank χ γ₁ γ₂ (fun p => -(β p)) = aiBank χ γ₁ γ₂ β := by
  unfold aiBank
  congr 1
  funext n
  unfold radialGlobalSatakeCoeff
  refine Finset.prod_congr rfl fun p _ => ?_
  by_cases hχ : χ ⟨p.1, Nat.prime_of_mem_primeFactors p.2⟩ = 1
  · unfold aiWeight
    rw [if_pos hχ, if_pos hχ]
  · have hswap : aiWeight χ γ₁ γ₂ (fun q => -(β q))
        ⟨p.1, Nat.prime_of_mem_primeFactors p.2⟩
        = (aiWeight χ γ₁ γ₂ β ⟨p.1, Nat.prime_of_mem_primeFactors p.2⟩) ∘
          (Equiv.swap (0 : Fin 2) 1) := by
      funext x
      unfold aiWeight
      rw [if_neg hχ, if_neg hχ]
      fin_cases x
      · simp
      · simp
    rw [hswap, radialLocalEulerCoeff_equiv]

/-- **The recognition law `AI(ψ) ⊗ χ = AI(ψ)`**: twisting the induced system by the
quadratic sign fixes the bank — split places are untouched, inert places swap the two
square roots.  This is the classical fingerprint of an induced representation, at the
bank level. -/
theorem aiBank_twist_invariant (χ : Nat.Primes → ℂ) (γ₁ γ₂ β : Nat.Primes → ℂ)
    (hquad : ∀ p, χ p = 1 ∨ χ p = -1) :
    coefficientArithmetic (radialGlobalSatakeCoeff
      (fun p i => χ p * aiWeight χ γ₁ γ₂ β p i))
      = aiBank χ γ₁ γ₂ β := by
  unfold aiBank
  congr 1
  funext n
  unfold radialGlobalSatakeCoeff
  refine Finset.prod_congr rfl fun p _ => ?_
  set q : Nat.Primes := ⟨p.1, Nat.prime_of_mem_primeFactors p.2⟩ with hq
  show radialLocalEulerCoeff (fun i => χ q * aiWeight χ γ₁ γ₂ β q i) _
      = radialLocalEulerCoeff (aiWeight χ γ₁ γ₂ β q) _
  rcases hquad q with hχ | hχ
  · rw [show (fun i => χ q * aiWeight χ γ₁ γ₂ β q i) = aiWeight χ γ₁ γ₂ β q from
      funext fun i => by rw [hχ, one_mul]]
  · have hne : χ q ≠ 1 := by rw [hχ]; norm_num
    have hswap : (fun i => χ q * aiWeight χ γ₁ γ₂ β q i)
        = (aiWeight χ γ₁ γ₂ β q) ∘ (Equiv.swap (0 : Fin 2) 1) := by
      funext x
      unfold aiWeight
      simp only [if_neg hne]
      fin_cases x <;>
        simp [Equiv.swap_apply_left, Equiv.swap_apply_right, hχ]
    rw [hswap, radialLocalEulerCoeff_equiv]



/-- The seed system of the eigenform: the rank-1 clock `(α_p, α_p⁻¹)`. -/
noncomputable def seedSystem (H : HeckeEigenData f) : Nat.Primes → Fin 2 → ℂ :=
  fun p i => symClockWeight 1 (H.satake p.2) (i : ℕ)

/-- The seed system's bank is the Deligne-normalized eigenform coefficients. -/
theorem bankArithmetic_seedSystem (H : HeckeEigenData f) :
    coefficientArithmetic (radialGlobalSatakeCoeff (seedSystem H)) = seedNorm f := by
  ext m
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp [coefficientArithmetic]
  · show (if m = 0 then 0 else _) = _
    rw [if_neg hm.ne']
    show radialGlobalSatakeCoeff (seedSystem H) (m - 1) = _
    rw [show radialGlobalSatakeCoeff (seedSystem H) (m - 1)
        = symrBank H 1 (m - 1 + 1) from
      CriticalLinePhasor.Sym2Join.radialGlobal_eq_symrBank H 1 (m - 1),
      Nat.sub_add_cancel hm, symrBank_one_rank H]

/-- **Quadratic base change of the eigenform, inert law**: at an inert prime the
base-change bank of the seed carries the Frobenius-squared Satake pair `(α_p², α_p⁻²)`
on even levels — the local datum of `BC_{E/ℚ}(f)` at the single place above `p`. -/
theorem bcBank_seed_inert (H : HeckeEigenData f) (χ : Nat.Primes → ℂ)
    {p : ℕ} (hp : p.Prime) (hχ : χ ⟨p, hp⟩ = -1) (j : ℕ) :
    bcBank (seedSystem H) χ (p ^ j)
      = if 2 ∣ j then
          radialLocalEulerCoeff
            (fun i : Fin 2 => (symClockWeight 1 (H.satake hp) (i : ℕ)) ^ 2) (j / 2)
        else 0 :=
  bcBank_inert (seedSystem H) χ hp hχ j

end CriticalLinePhasor.BaseChangeInduction

#print axioms CriticalLinePhasor.BaseChangeInduction.radialLocalEulerCoeff_smul
#print axioms CriticalLinePhasor.BaseChangeInduction.radialLocalEulerCoeff_single
#print axioms CriticalLinePhasor.BaseChangeInduction.parity_rank_one
#print axioms CriticalLinePhasor.BaseChangeInduction.parity_law
#print axioms CriticalLinePhasor.BaseChangeInduction.radialLocalEulerCoeff_snoc
#print axioms CriticalLinePhasor.BaseChangeInduction.bcBank_split
#print axioms CriticalLinePhasor.BaseChangeInduction.bcBank_inert
#print axioms CriticalLinePhasor.BaseChangeInduction.aiBank_inert
#print axioms CriticalLinePhasor.BaseChangeInduction.aiBank_root_choice
#print axioms CriticalLinePhasor.BaseChangeInduction.aiBank_twist_invariant
#print axioms CriticalLinePhasor.BaseChangeInduction.bankArithmetic_seedSystem
#print axioms CriticalLinePhasor.BaseChangeInduction.bcBank_seed_inert
