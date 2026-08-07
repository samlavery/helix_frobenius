import RequestProject.RepMechanism

/-!
# The general seed: the ladder decoupled from the holomorphic level-one eigenform

The scope read of the benchmark ladder shows one fact: everything downstream of the
seed — transport, mechanism, packages, charts, standing waves, the crossing's fiber
layer — consumes the seed only through three fields: a nonzero Satake value at every
prime and a polynomial bound on it and its inverse.  This file types that surface and
rebuilds the rank-uniform transport on it, so the ladder rides **any** seed:

* `SatakeSeed` — the three-field surface;
* `SatakeSeed.ofHecke` — the holomorphic level-one instance, from the compiled
  eigenform package;
* `SatakeSeed.unit` — the trivial seed (non-vacuity; its banks are the `ζ`-family);
* `satake_root_bound` — any root of the Satake quadratic `α + α⁻¹ = c` obeys
  `‖α‖ ≤ ‖c‖ + 1`, and its inverse is the other root: bounds are free from the
  equation;
* `MaassEigenData` — **the Maass seed, typed**: analytically normalized real
  multiplicative coefficients with the det-one Hecke recursion and a polynomial
  coefficient bound — the classical package of a level-one Maass–Hecke eigenform,
  the same status as `HeckeEigenData` (classical Hecke theory; not in Mathlib);
* `MaassEigenData.coeff_prime_pow` — the join: the seed's prime-power coefficients
  are the Chebyshev clock values of its chosen Satake parameter;
* `SatakeSeed.ofMaass` — the Maass instance;
* `symrSatakePairOf` / `symrPairOf_dual_eq_primal` / `symrBankOf_summable` — the
  `Sym^r` transport at every rank over any seed, self-dual by the clock reversal;
* `symr_package_of_theta_of` / `symr_general_package_of_theta_of` — **the mechanism
  at every rank over every seed, at every admissible chart**: one theta identity
  yields the complete analytic package.

Register: the Maass completed chart is the pure-`Γℝ` pair `Γℝ(s+it)Γℝ(s−it)`; the
compiled kernel family covers `∏Γℝ·∏Γℂ` with nonempty complex part, and the
pure-real-chain kernel is the named next brick (a mechanical mirror of the compiled
real-clock machinery).  Level-`N` seeds add ramified degenerate clocks (rank-varying
Euler factors) — the named extension after that.  No `axiom`, no `sorry`.
-/

open Complex Finset
open scoped MatrixGroups

namespace CriticalLinePhasor.GeneralSeed

open CriticalLinePhasor.GlobalHelix CriticalLinePhasor.Sym2Wire
open CriticalLinePhasor.SymCubeQuartic CriticalLinePhasor.ThetaMechanism
open CriticalLinePhasor.RepMechanism CriticalLinePhasor.NiceClosure
open CriticalLinePhasor.GenuineGL2Carrier CriticalLinePhasor.Sym2Identification
open CriticalLinePhasor.CarrierTheta

/-! ## The seed surface -/

/-- **The general seed**: the exact surface the rank-uniform transport consumes — a
nonzero Satake value at every prime with one polynomial bound for it and its
inverse. -/
structure SatakeSeed where
  satake : Nat.Primes → ℂ
  satake_ne_zero : ∀ p : Nat.Primes, satake p ≠ 0
  E : ℕ
  satake_bound : ∀ p : Nat.Primes, ‖satake p‖ ≤ (p.1 : ℝ) ^ E
  satake_inv_bound : ∀ p : Nat.Primes, ‖(satake p)⁻¹‖ ≤ (p.1 : ℝ) ^ E

/-- The holomorphic level-one instance: the compiled eigenform package is a seed. -/
noncomputable def SatakeSeed.ofHecke {k : ℤ} {f : CuspForm 𝒮ℒ k}
    (H : HeckeEigenData f) : SatakeSeed where
  satake := fun p => H.satake p.2
  satake_ne_zero := fun p => H.satake_ne_zero p.2
  E := (satake_single_bound H).choose
  satake_bound := fun p => ((satake_single_bound H).choose_spec p).1
  satake_inv_bound := fun p => ((satake_single_bound H).choose_spec p).2

/-- The trivial seed (non-vacuity): Satake value `1` at every prime. -/
noncomputable def SatakeSeed.unit : SatakeSeed where
  satake := fun _ => 1
  satake_ne_zero := fun _ => one_ne_zero
  E := 0
  satake_bound := fun p => by
    norm_num
  satake_inv_bound := fun p => by
    norm_num

/-! ## Roots of the Satake quadratic are bounded by the trace -/

/-- Any root of `α + α⁻¹ = c` obeys `‖α‖ ≤ ‖c‖ + 1`: from `α² = cα − 1`,
`‖α‖² ≤ ‖c‖·‖α‖ + 1`, and the dichotomy `‖α‖ ≤ 1` or not. -/
theorem satake_root_bound {α c : ℂ} (hα : α ≠ 0) (h : α + α⁻¹ = c) :
    ‖α‖ ≤ ‖c‖ + 1 := by
  have hsq : α ^ 2 = c * α - 1 := by
    have h1 := congrArg (· * α) h
    simp only [add_mul, inv_mul_cancel₀ hα] at h1
    linear_combination h1
  have h3 : ‖α‖ ^ 2 ≤ ‖c‖ * ‖α‖ + 1 := by
    calc ‖α‖ ^ 2 = ‖α ^ 2‖ := (norm_pow α 2).symm
      _ = ‖c * α - 1‖ := by rw [hsq]
      _ ≤ ‖c * α‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = ‖c‖ * ‖α‖ + 1 := by rw [norm_mul, norm_one]
  rcases le_total ‖α‖ 1 with h1 | h1
  · have := norm_nonneg c
    linarith
  · by_contra hcon
    rw [not_le] at hcon
    have h4 : (‖c‖ + 1) * ‖α‖ < ‖α‖ * ‖α‖ :=
      mul_lt_mul_of_pos_right hcon (by linarith)
    have h5 : ‖c‖ * ‖α‖ + 1 ≤ (‖c‖ + 1) * ‖α‖ := by nlinarith
    nlinarith [sq_nonneg ‖α‖]

/-- The inverse of a Satake root is the other root: same equation, same bound. -/
theorem satake_root_inv_bound {α c : ℂ} (hα : α ≠ 0) (h : α + α⁻¹ = c) :
    ‖α⁻¹‖ ≤ ‖c‖ + 1 := by
  refine satake_root_bound (inv_ne_zero hα) ?_
  rw [inv_inv, add_comm]
  exact h

/-! ## The Maass seed, typed -/

/-- **The level-one Maass–Hecke eigenform package, typed**: analytically normalized
coefficients — `λ(1) = 1`, coprime multiplicativity, the det-one Hecke recursion
`λ(p^{j+2}) = λ(p)·λ(p^{j+1}) − λ(p^j)`, real coefficients — together with a
polynomial coefficient bound.  Classical spectral Hecke theory (not in Mathlib),
consumed as a structure exactly as `HeckeEigenData` is for the holomorphic seed. -/
structure MaassEigenData where
  lam : ℕ → ℂ
  one : lam 1 = 1
  coprime_mul : ∀ m n : ℕ, Nat.Coprime m n → lam (m * n) = lam m * lam n
  prime_rec : ∀ p : ℕ, p.Prime → ∀ j : ℕ,
    lam (p ^ (j + 2)) = lam p * lam (p ^ (j + 1)) - lam (p ^ j)
  conj_eq : ∀ n : ℕ, (starRingEnd ℂ) (lam n) = lam n
  E₀ : ℕ
  lam_bound : ∀ p : ℕ, p.Prime → ‖lam p‖ ≤ (p : ℝ) ^ E₀

namespace MaassEigenData

/-- The chosen Satake parameter of the Maass seed at a prime. -/
noncomputable def satake (M : MaassEigenData) (p : Nat.Primes) : ℂ :=
  (exists_satake (M.lam p.1)).choose

theorem satake_ne_zero (M : MaassEigenData) (p : Nat.Primes) : M.satake p ≠ 0 :=
  (exists_satake (M.lam p.1)).choose_spec.1

theorem satake_trace (M : MaassEigenData) (p : Nat.Primes) :
    M.satake p + (M.satake p)⁻¹ = M.lam p.1 :=
  (exists_satake (M.lam p.1)).choose_spec.2

/-- Powers of the prime dominate the trace bound plus one. -/
theorem bound_step (M : MaassEigenData) (p : Nat.Primes) :
    ‖M.lam p.1‖ + 1 ≤ (p.1 : ℝ) ^ (M.E₀ + 1) := by
  have hp2 : (2 : ℝ) ≤ (p.1 : ℝ) := by exact_mod_cast p.2.two_le
  have h1 : (1 : ℝ) ≤ (p.1 : ℝ) ^ M.E₀ := one_le_pow₀ (by linarith)
  calc ‖M.lam p.1‖ + 1 ≤ (p.1 : ℝ) ^ M.E₀ + (p.1 : ℝ) ^ M.E₀ := by
        have := M.lam_bound p.1 p.2
        linarith
    _ = 2 * (p.1 : ℝ) ^ M.E₀ := by ring
    _ ≤ (p.1 : ℝ) * (p.1 : ℝ) ^ M.E₀ := by
        have := pow_nonneg (by linarith : (0:ℝ) ≤ (p.1 : ℝ)) M.E₀
        nlinarith
    _ = (p.1 : ℝ) ^ (M.E₀ + 1) := by ring

/-- **The join**: the Maass seed's prime-power coefficients are the Chebyshev clock
values of its Satake parameter — `λ(p^j) = U_j(α_p)`. -/
theorem coeff_prime_pow (M : MaassEigenData) (p : Nat.Primes) (j : ℕ) :
    M.lam (p.1 ^ j) = seedCoeff (M.satake p) j := by
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    match j with
    | 0 => simpa [seedCoeff_zero] using M.one
    | 1 => rw [pow_one, seedCoeff_one, M.satake_trace p]
    | (j + 2) =>
        rw [M.prime_rec p.1 p.2 j, ih (j + 1) (by omega), ih j (by omega),
          seedCoeff_rec (M.satake p) (M.satake_ne_zero p) j, ← M.satake_trace p]

end MaassEigenData

/-- **The Maass seed**: the typed Maass package is a `SatakeSeed`, with the root
bounds free from the Satake quadratic. -/
noncomputable def _root_.CriticalLinePhasor.GeneralSeed.SatakeSeed.ofMaass
    (M : MaassEigenData) : SatakeSeed where
  satake := M.satake
  satake_ne_zero := M.satake_ne_zero
  E := M.E₀ + 1
  satake_bound := fun p =>
    le_trans (satake_root_bound (M.satake_ne_zero p) (M.satake_trace p))
      (M.bound_step p)
  satake_inv_bound := fun p =>
    le_trans (satake_root_inv_bound (M.satake_ne_zero p) (M.satake_trace p))
      (M.bound_step p)

/-! ## The `Sym^r` transport over any seed -/

/-- Norm bound for every channel of the `Sym^r` clock of a seed. -/
theorem symClockWeightOf_norm_bound (S : SatakeSeed) (r : ℕ) (p : Nat.Primes)
    (i : Fin (r + 1)) :
    ‖symClockWeight r (S.satake p) (i : ℕ)‖ ≤ (p.1 : ℝ) ^ (S.E * r) := by
  have hp1 : (1 : ℝ) ≤ (p.1 : ℝ) := by exact_mod_cast p.2.one_lt.le
  have hpE : (1 : ℝ) ≤ (p.1 : ℝ) ^ S.E := one_le_pow₀ hp1
  unfold symClockWeight
  set m : ℤ := (r : ℤ) - 2 * ((i : ℕ) : ℤ) with hmdef
  have hm : m.natAbs ≤ r := by
    have := i.2
    omega
  have hkey : ∀ (β : ℝ), 0 ≤ β → β ≤ (p.1 : ℝ) ^ S.E →
      β ^ m.natAbs ≤ (p.1 : ℝ) ^ (S.E * r) := by
    intro β hβ0 hβ
    calc β ^ m.natAbs ≤ ((p.1 : ℝ) ^ S.E) ^ m.natAbs := pow_le_pow_left₀ hβ0 hβ _
      _ = (p.1 : ℝ) ^ (S.E * m.natAbs) := by rw [← pow_mul]
      _ ≤ (p.1 : ℝ) ^ (S.E * r) :=
          pow_le_pow_right₀ hp1 (Nat.mul_le_mul_left _ hm)
  rcases Int.natAbs_eq m with hcase | hcase
  · rw [hcase, zpow_natCast, norm_pow]
    exact hkey _ (norm_nonneg _) (S.satake_bound p)
  · rw [hcase, zpow_neg, zpow_natCast, ← inv_pow, norm_pow]
    exact hkey _ (norm_nonneg _) (S.satake_inv_bound p)

/-- Inverse-channel bound. -/
theorem symClockWeightOf_inv_norm_bound (S : SatakeSeed) (r : ℕ) (p : Nat.Primes)
    (i : Fin (r + 1)) :
    ‖(symClockWeight r (S.satake p) (i : ℕ))⁻¹‖ ≤ (p.1 : ℝ) ^ (S.E * r) := by
  have hp1 : (1 : ℝ) ≤ (p.1 : ℝ) := by exact_mod_cast p.2.one_lt.le
  have hpE : (1 : ℝ) ≤ (p.1 : ℝ) ^ S.E := one_le_pow₀ hp1
  unfold symClockWeight
  set m : ℤ := (r : ℤ) - 2 * ((i : ℕ) : ℤ) with hmdef
  have hm : m.natAbs ≤ r := by
    have := i.2
    omega
  have hkey : ∀ (β : ℝ), 0 ≤ β → β ≤ (p.1 : ℝ) ^ S.E →
      β ^ m.natAbs ≤ (p.1 : ℝ) ^ (S.E * r) := by
    intro β hβ0 hβ
    calc β ^ m.natAbs ≤ ((p.1 : ℝ) ^ S.E) ^ m.natAbs := pow_le_pow_left₀ hβ0 hβ _
      _ = (p.1 : ℝ) ^ (S.E * m.natAbs) := by rw [← pow_mul]
      _ ≤ (p.1 : ℝ) ^ (S.E * r) :=
          pow_le_pow_right₀ hp1 (Nat.mul_le_mul_left _ hm)
  rcases Int.natAbs_eq m with hcase | hcase
  · rw [hcase, zpow_natCast, ← inv_pow, norm_pow]
    exact hkey _ (norm_nonneg _) (S.satake_inv_bound p)
  · rw [hcase, zpow_neg, zpow_natCast, inv_inv, norm_pow]
    exact hkey _ (norm_nonneg _) (S.satake_bound p)

/-- **The `Sym^r` Satake pair of any seed**: the rank-uniform transport, decoupled
from the holomorphic eigenform. -/
noncomputable def symrSatakePairOf (S : SatakeSeed) (r : ℕ) :
    PolynomialSatakeDualPair (Fin (r + 1)) where
  primal := fun p i => symClockWeight r (S.satake p) (i : ℕ)
  dual := fun p i => (symClockWeight r (S.satake p) (i : ℕ))⁻¹
  primalExponent := S.E * r
  dualExponent := S.E * r
  primal_ne_zero := fun p _ => zpow_ne_zero _ (S.satake_ne_zero p)
  dual_eq_inv := fun _ _ => rfl
  primal_bound := symClockWeightOf_norm_bound S r
  dual_bound := symClockWeightOf_inv_norm_bound S r

/-- **Self-duality at every seed and rank**: the contragredient coefficients equal the
primal — the clock reversal, seed-free. -/
theorem symrPairOf_dual_eq_primal (S : SatakeSeed) (r : ℕ) (j : ℕ) :
    cpsPolynomialDualCoeff (symrSatakePairOf S r) j
      = cpsPolynomialPrimalCoeff (symrSatakePairOf S r) j := by
  unfold CriticalLinePhasor.GlobalHelix.cpsPolynomialDualCoeff
    CriticalLinePhasor.GlobalHelix.cpsPolynomialPrimalCoeff
  have hswap : (symrSatakePairOf S r).dual
      = fun p => (symrSatakePairOf S r).primal p ∘ (Fin.revPerm : Equiv.Perm (Fin (r + 1))) := by
    funext p i
    show (symClockWeight r (S.satake p) (i : ℕ))⁻¹
      = symClockWeight r (S.satake p) ((Fin.rev i : Fin (r + 1)) : ℕ)
    unfold symClockWeight
    rw [← zpow_neg]
    congr 1
    have hrev : ((Fin.rev i : Fin (r + 1)) : ℕ) = r - (i : ℕ) := by
      simp [Fin.rev]
    rw [hrev]
    have hle : (i : ℕ) ≤ r := Nat.lt_succ_iff.mp i.2
    push_cast [Nat.cast_sub hle]
    ring
  rw [hswap]
  exact CriticalLinePhasor.GenuineGL2Carrier.radialGlobalSatakeCoeff_comp_equiv
    (Fin.revPerm) (symrSatakePairOf S r).primal j

/-! ## The mechanism at every rank over every seed -/

/-- **The mechanism over any seed, complex chart**: one theta identity of the
prescribed `Sym^r` readouts of any seed yields the complete package. -/
noncomputable def symr_package_of_theta_of (S : SatakeSeed) (r : ℕ)
    (μs : List ℂ) (hne : μs ≠ []) (hμpos : ∀ μ ∈ μs, 0 ≤ μ.re)
    (ε : ℂ) (hε : ε ≠ 0)
    (hrefl : ∀ x : ℝ, 0 < x →
      cpsPolynomialFullPrimal3DBankReadout (symrSatakePairOf S r) 1 μs (1 / x) =
        (ε * ((x ^ (1 : ℝ) : ℝ) : ℂ)) •
          cpsPolynomialFullDual3DTransformedReadout (symrSatakePairOf S r) 1 μs (1 / x)) :
    NicePackage (coefficientArithmetic (cpsPolynomialPrimalCoeff (symrSatakePairOf S r)))
      μs (mechB (symrSatakePairOf S r)) ε :=
  mechanism (symrSatakePairOf S r) (symrPairOf_dual_eq_primal S r) μs hne hμpos ε hε hrefl

/-- **The mechanism over any seed, general Deligne chart** `∏Γℝ·∏Γℂ`. -/
noncomputable def symr_general_package_of_theta_of (S : SatakeSeed) (r : ℕ)
    (dlts : List ℂ) (hdlts : ∀ dlt ∈ dlts, 0 ≤ dlt.re)
    (μs : List ℂ) (hne : μs ≠ []) (hμpos : ∀ μ ∈ μs, 0 ≤ μ.re)
    (ε : ℂ) (hε : ε ≠ 0)
    (hrefl : ∀ x : ℝ, 0 < x →
      generalPrimal3DBankReadout (symrSatakePairOf S r) dlts μs (1 / x) =
        (ε * ((x ^ (1 : ℝ) : ℝ) : ℂ)) •
          generalDual3DTransformedReadout (symrSatakePairOf S r) dlts μs (1 / x)) :
    GeneralNicePackage (coefficientArithmetic (cpsPolynomialPrimalCoeff (symrSatakePairOf S r)))
      dlts μs (mechB (symrSatakePairOf S r)) ε :=
  mechanismG (symrSatakePairOf S r) (symrPairOf_dual_eq_primal S r) dlts hdlts μs hne hμpos
    ε hε hrefl

end CriticalLinePhasor.GeneralSeed

#print axioms CriticalLinePhasor.GeneralSeed.SatakeSeed.ofHecke
#print axioms CriticalLinePhasor.GeneralSeed.satake_root_bound
#print axioms CriticalLinePhasor.GeneralSeed.MaassEigenData.coeff_prime_pow
#print axioms CriticalLinePhasor.GeneralSeed.SatakeSeed.ofMaass
#print axioms CriticalLinePhasor.GeneralSeed.symrSatakePairOf
#print axioms CriticalLinePhasor.GeneralSeed.symrPairOf_dual_eq_primal
#print axioms CriticalLinePhasor.GeneralSeed.symr_package_of_theta_of
#print axioms CriticalLinePhasor.GeneralSeed.symr_general_package_of_theta_of
