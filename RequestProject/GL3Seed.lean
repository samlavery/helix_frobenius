import RequestProject.RealChainCompletion

/-!
# GL(3) seeds: the standard rank-three surface and the `Sym²` lift instance

`GeneralSeed` typed the GL(2) surface (`SatakeSeed`) and transported it to every
symmetric power.  This file types the rank-three standard surface directly:

* `GL3Seed` — two Satake functions with polynomial bounds; the third root is the
  det-one cofactor `(a·b)⁻¹`, so the local ledger `∏ weights = 1` holds by
  construction;
* `gl3PairOf` — the standard `PolynomialSatakeDualPair (Fin 3)` of a seed;
* `gl3PairOf_dual_eq_primal` — self-duality **as a typed hypothesis**: a
  permutation `σ` of the three channels carrying each weight to its inverse.
  Rank three is odd, so (unlike `Sym^r` of GL(2)) the standard bank is not
  automatically self-dual; the hypothesis is exactly the classical `Π ≅ Π^∨`;
* `gl3_package_of_theta_of` / `gl3_general_package_of_theta_of` /
  `gl3_real_package_of_theta_of` — **the mechanism on any self-dual GL(3) seed at
  every admissible chart** (`∏Γℂ`, `∏Γℝ·∏Γℂ`, pure-`Γℝ` chain — the last is the
  self-dual GL(3) Maass chart type);
* `GL3Seed.ofSym2` / `ofSym2_selfdual` — the `Sym²` lift of any GL(2) seed is a
  GL(3) seed and satisfies the self-duality hypothesis (the channel reversal
  `0 ↔ 2` — discharged, not assumed);
* `ofSym2_coeff_eq_sym2` — **the recognition**: the GL(3) standard coefficients of
  the lift are literally the `Sym²` transport coefficients of the seed — the
  Gelbart–Jacquet identification at seed level;
* `gl3_sym2_package_of_theta` — the mechanism firing unconditionally on the lift.

No `axiom`, no `sorry`.
-/

open Complex Finset

namespace CriticalLinePhasor.GeneralSeed

open CriticalLinePhasor.GlobalHelix CriticalLinePhasor.ThetaMechanism
open CriticalLinePhasor.RepMechanism CriticalLinePhasor.GenuineGL2Carrier
open CriticalLinePhasor.RealChainMechanism CriticalLinePhasor.CarrierTheta
open CriticalLinePhasor.Sym2Wire CriticalLinePhasor.SymCubeQuartic
open CriticalLinePhasor.NiceClosure CriticalLinePhasor.Sym2Identification

/-! ## The rank-three surface -/

/-- **The GL(3) seed**: two nonzero Satake functions with one polynomial bound each
way; the third root is the det-one cofactor. -/
structure GL3Seed where
  a : Nat.Primes → ℂ
  b : Nat.Primes → ℂ
  a_ne_zero : ∀ p : Nat.Primes, a p ≠ 0
  b_ne_zero : ∀ p : Nat.Primes, b p ≠ 0
  E : ℕ
  a_bound : ∀ p : Nat.Primes, ‖a p‖ ≤ (p.1 : ℝ) ^ E
  a_inv_bound : ∀ p : Nat.Primes, ‖(a p)⁻¹‖ ≤ (p.1 : ℝ) ^ E
  b_bound : ∀ p : Nat.Primes, ‖b p‖ ≤ (p.1 : ℝ) ^ E
  b_inv_bound : ∀ p : Nat.Primes, ‖(b p)⁻¹‖ ≤ (p.1 : ℝ) ^ E

/-- The three standard channel weights: `a`, `b`, and the det-one cofactor. -/
noncomputable def gl3Weight (T : GL3Seed) (p : Nat.Primes) (i : Fin 3) : ℂ :=
  if i = 0 then T.a p else if i = 1 then T.b p else (T.a p * T.b p)⁻¹

theorem gl3Weight_ne_zero (T : GL3Seed) (p : Nat.Primes) (i : Fin 3) :
    gl3Weight T p i ≠ 0 := by
  fin_cases i
  · simpa [gl3Weight] using T.a_ne_zero p
  · simpa [gl3Weight] using T.b_ne_zero p
  · simpa [gl3Weight] using inv_ne_zero (mul_ne_zero (T.a_ne_zero p) (T.b_ne_zero p))

/-- The det-one ledger: the three weights multiply to `1` by construction. -/
theorem gl3Weight_det_one (T : GL3Seed) (p : Nat.Primes) :
    gl3Weight T p 0 * gl3Weight T p 1 * gl3Weight T p 2 = 1 := by
  have h0 : gl3Weight T p 0 = T.a p := by simp [gl3Weight]
  have h1 : gl3Weight T p 1 = T.b p := by simp [gl3Weight]
  have h2 : gl3Weight T p 2 = (T.a p * T.b p)⁻¹ := by simp [gl3Weight]
  rw [h0, h1, h2]
  exact mul_inv_cancel₀ (mul_ne_zero (T.a_ne_zero p) (T.b_ne_zero p))

theorem gl3Weight_norm_bound (T : GL3Seed) (p : Nat.Primes) (i : Fin 3) :
    ‖gl3Weight T p i‖ ≤ (p.1 : ℝ) ^ (2 * T.E) := by
  have hp1 : (1 : ℝ) ≤ (p.1 : ℝ) := by exact_mod_cast p.2.one_lt.le
  have hEle : (p.1 : ℝ) ^ T.E ≤ (p.1 : ℝ) ^ (2 * T.E) :=
    pow_le_pow_right₀ hp1 (by omega)
  fin_cases i
  · simpa [gl3Weight] using (T.a_bound p).trans hEle
  · simpa [gl3Weight] using (T.b_bound p).trans hEle
  · show ‖gl3Weight T p 2‖ ≤ (p.1 : ℝ) ^ (2 * T.E)
    have h2 : gl3Weight T p 2 = (T.a p * T.b p)⁻¹ := by
      simp [gl3Weight]
    rw [h2, mul_inv, norm_mul, two_mul, pow_add]
    exact mul_le_mul (T.a_inv_bound p) (T.b_inv_bound p) (norm_nonneg _)
      (by positivity)

theorem gl3Weight_inv_norm_bound (T : GL3Seed) (p : Nat.Primes) (i : Fin 3) :
    ‖(gl3Weight T p i)⁻¹‖ ≤ (p.1 : ℝ) ^ (2 * T.E) := by
  have hp1 : (1 : ℝ) ≤ (p.1 : ℝ) := by exact_mod_cast p.2.one_lt.le
  have hEle : (p.1 : ℝ) ^ T.E ≤ (p.1 : ℝ) ^ (2 * T.E) :=
    pow_le_pow_right₀ hp1 (by omega)
  fin_cases i
  · simpa [gl3Weight] using (T.a_inv_bound p).trans hEle
  · simpa [gl3Weight] using (T.b_inv_bound p).trans hEle
  · show ‖(gl3Weight T p 2)⁻¹‖ ≤ (p.1 : ℝ) ^ (2 * T.E)
    have h2 : (gl3Weight T p 2)⁻¹ = T.a p * T.b p := by
      simp [gl3Weight]
    rw [h2, norm_mul, two_mul, pow_add]
    exact mul_le_mul (T.a_bound p) (T.b_bound p) (norm_nonneg _) (by positivity)

/-- **The standard pair of a GL(3) seed.** -/
noncomputable def gl3PairOf (T : GL3Seed) : PolynomialSatakeDualPair (Fin 3) where
  primal := gl3Weight T
  dual := fun p i => (gl3Weight T p i)⁻¹
  primalExponent := 2 * T.E
  dualExponent := 2 * T.E
  primal_ne_zero := gl3Weight_ne_zero T
  dual_eq_inv := fun _ _ => rfl
  primal_bound := gl3Weight_norm_bound T
  dual_bound := gl3Weight_inv_norm_bound T

/-- **Self-duality as a typed hypothesis**: a permutation of the three channels
carrying each weight to its inverse makes the contragredient coefficients equal the
primal.  This is the classical `Π ≅ Π^∨`; rank three does not supply it for free. -/
theorem gl3PairOf_dual_eq_primal (T : GL3Seed) (σ : Equiv.Perm (Fin 3))
    (hσ : ∀ (p : Nat.Primes) (i : Fin 3),
      (gl3Weight T p i)⁻¹ = gl3Weight T p (σ i)) (j : ℕ) :
    cpsPolynomialDualCoeff (gl3PairOf T) j = cpsPolynomialPrimalCoeff (gl3PairOf T) j := by
  unfold CriticalLinePhasor.GlobalHelix.cpsPolynomialDualCoeff
    CriticalLinePhasor.GlobalHelix.cpsPolynomialPrimalCoeff
  have hswap : (gl3PairOf T).dual = fun p => (gl3PairOf T).primal p ∘ σ := by
    funext p i
    exact hσ p i
  rw [hswap]
  exact radialGlobalSatakeCoeff_comp_equiv σ (gl3PairOf T).primal j

/-! ## The mechanism on any self-dual GL(3) seed, at every admissible chart -/

/-- **The mechanism on a self-dual GL(3) seed, complex chart.** -/
noncomputable def gl3_package_of_theta_of (T : GL3Seed) (σ : Equiv.Perm (Fin 3))
    (hσ : ∀ (p : Nat.Primes) (i : Fin 3),
      (gl3Weight T p i)⁻¹ = gl3Weight T p (σ i))
    (μs : List ℂ) (hne : μs ≠ []) (hμpos : ∀ μ ∈ μs, 0 ≤ μ.re)
    (ε : ℂ) (hε : ε ≠ 0)
    (hrefl : ∀ x : ℝ, 0 < x →
      cpsPolynomialFullPrimal3DBankReadout (gl3PairOf T) 1 μs (1 / x) =
        (ε * ((x ^ (1 : ℝ) : ℝ) : ℂ)) •
          cpsPolynomialFullDual3DTransformedReadout (gl3PairOf T) 1 μs (1 / x)) :
    NicePackage (coefficientArithmetic (cpsPolynomialPrimalCoeff (gl3PairOf T)))
      μs (mechB (gl3PairOf T)) ε :=
  mechanism (gl3PairOf T) (gl3PairOf_dual_eq_primal T σ hσ) μs hne hμpos ε hε hrefl

/-- **The mechanism on a self-dual GL(3) seed, general Deligne chart** `∏Γℝ·∏Γℂ`. -/
noncomputable def gl3_general_package_of_theta_of (T : GL3Seed) (σ : Equiv.Perm (Fin 3))
    (hσ : ∀ (p : Nat.Primes) (i : Fin 3),
      (gl3Weight T p i)⁻¹ = gl3Weight T p (σ i))
    (dlts : List ℂ) (hdlts : ∀ dlt ∈ dlts, 0 ≤ dlt.re)
    (μs : List ℂ) (hne : μs ≠ []) (hμpos : ∀ μ ∈ μs, 0 ≤ μ.re)
    (ε : ℂ) (hε : ε ≠ 0)
    (hrefl : ∀ x : ℝ, 0 < x →
      generalPrimal3DBankReadout (gl3PairOf T) dlts μs (1 / x) =
        (ε * ((x ^ (1 : ℝ) : ℝ) : ℂ)) •
          generalDual3DTransformedReadout (gl3PairOf T) dlts μs (1 / x)) :
    GeneralNicePackage (coefficientArithmetic (cpsPolynomialPrimalCoeff (gl3PairOf T)))
      dlts μs (mechB (gl3PairOf T)) ε :=
  mechanismG (gl3PairOf T) (gl3PairOf_dual_eq_primal T σ hσ) dlts hdlts μs hne hμpos
    ε hε hrefl

/-- **The mechanism on a self-dual GL(3) seed, pure-`Γℝ` chain chart** — the
self-dual GL(3) Maass chart type `Γℝ(s+d)·∏Γℝ(s+eⱼ)`. -/
noncomputable def gl3_real_package_of_theta_of (T : GL3Seed) (σ : Equiv.Perm (Fin 3))
    (hσ : ∀ (p : Nat.Primes) (i : Fin 3),
      (gl3Weight T p i)⁻¹ = gl3Weight T p (σ i))
    (d : ℂ) (hd : 0 ≤ d.re) (ds : List ℂ) (hds : ∀ e ∈ ds, 0 ≤ e.re)
    (ε : ℂ) (hε : ε ≠ 0)
    (hrefl : ∀ x : ℝ, 0 < x →
      realPrimal3DBankReadout (gl3PairOf T) d ds (1 / x) =
        (ε * ((x ^ (1 : ℝ) : ℝ) : ℂ)) •
          realDual3DTransformedReadout (gl3PairOf T) d ds (1 / x)) :
    RealNicePackage (coefficientArithmetic (cpsPolynomialPrimalCoeff (gl3PairOf T)))
      d ds (mechB (gl3PairOf T)) ε :=
  mechanismRR (gl3PairOf T) (gl3PairOf_dual_eq_primal T σ hσ) d hd ds hds ε hε hrefl

/-! ## The `Sym²` lift: the discharging instance -/

/-- **The `Sym²` lift of any GL(2) seed is a GL(3) seed**: channels `α², 1, α⁻²`. -/
noncomputable def GL3Seed.ofSym2 (S : SatakeSeed) : GL3Seed where
  a := fun p => S.satake p ^ 2
  b := fun _ => 1
  a_ne_zero := fun p => pow_ne_zero _ (S.satake_ne_zero p)
  b_ne_zero := fun _ => one_ne_zero
  E := 2 * S.E
  a_bound := fun p => by
    rw [norm_pow, mul_comm 2 S.E, pow_mul]
    exact pow_le_pow_left₀ (norm_nonneg _) (S.satake_bound p) 2
  a_inv_bound := fun p => by
    rw [← inv_pow, norm_pow, mul_comm 2 S.E, pow_mul]
    exact pow_le_pow_left₀ (norm_nonneg _) (S.satake_inv_bound p) 2
  b_bound := fun p => by
    have hp1 : (1 : ℝ) ≤ (p.1 : ℝ) := by exact_mod_cast p.2.one_lt.le
    simpa using one_le_pow₀ hp1
  b_inv_bound := fun p => by
    have hp1 : (1 : ℝ) ≤ (p.1 : ℝ) := by exact_mod_cast p.2.one_lt.le
    simpa using one_le_pow₀ hp1

/-- **The lift discharges the self-duality hypothesis**: the channel reversal
`0 ↔ 2` carries each weight to its inverse. -/
theorem ofSym2_selfdual (S : SatakeSeed) (p : Nat.Primes) (i : Fin 3) :
    (gl3Weight (GL3Seed.ofSym2 S) p i)⁻¹ =
      gl3Weight (GL3Seed.ofSym2 S) p (Equiv.swap (0 : Fin 3) 2 i) := by
  have h0 : gl3Weight (GL3Seed.ofSym2 S) p 0 = S.satake p ^ 2 := by
    simp [gl3Weight, GL3Seed.ofSym2]
  have h1 : gl3Weight (GL3Seed.ofSym2 S) p 1 = 1 := by
    simp [gl3Weight, GL3Seed.ofSym2]
  have h2 : gl3Weight (GL3Seed.ofSym2 S) p 2 = (S.satake p ^ 2)⁻¹ := by
    simp [gl3Weight, GL3Seed.ofSym2]
  fin_cases i
  · show (gl3Weight (GL3Seed.ofSym2 S) p 0)⁻¹ =
      gl3Weight (GL3Seed.ofSym2 S) p (Equiv.swap (0 : Fin 3) 2 0)
    rw [Equiv.swap_apply_left, h0, h2]
  · show (gl3Weight (GL3Seed.ofSym2 S) p 1)⁻¹ =
      gl3Weight (GL3Seed.ofSym2 S) p (Equiv.swap (0 : Fin 3) 2 1)
    rw [Equiv.swap_apply_of_ne_of_ne (by decide) (by decide), h1, inv_one]
  · show (gl3Weight (GL3Seed.ofSym2 S) p 2)⁻¹ =
      gl3Weight (GL3Seed.ofSym2 S) p (Equiv.swap (0 : Fin 3) 2 2)
    rw [Equiv.swap_apply_right, h2, h0, inv_inv]

/-- The lift's channel weights are the `Sym²` clock weights. -/
theorem gl3Weight_ofSym2_eq_symClock (S : SatakeSeed) (p : Nat.Primes) (i : Fin 3) :
    gl3Weight (GL3Seed.ofSym2 S) p i = symClockWeight 2 (S.satake p) (i : ℕ) := by
  have h0 : gl3Weight (GL3Seed.ofSym2 S) p 0 = S.satake p ^ 2 := by
    simp [gl3Weight, GL3Seed.ofSym2]
  have h1 : gl3Weight (GL3Seed.ofSym2 S) p 1 = 1 := by
    simp [gl3Weight, GL3Seed.ofSym2]
  have h2 : gl3Weight (GL3Seed.ofSym2 S) p 2 = (S.satake p ^ 2)⁻¹ := by
    simp [gl3Weight, GL3Seed.ofSym2]
  fin_cases i
  · show gl3Weight (GL3Seed.ofSym2 S) p 0 = symClockWeight 2 (S.satake p) 0
    rw [h0, ← zpow_natCast (S.satake p) 2]
    unfold symClockWeight
    congr 1
  · show gl3Weight (GL3Seed.ofSym2 S) p 1 = symClockWeight 2 (S.satake p) 1
    rw [h1, ← zpow_zero (S.satake p)]
    unfold symClockWeight
    congr 1
  · show gl3Weight (GL3Seed.ofSym2 S) p 2 = symClockWeight 2 (S.satake p) 2
    rw [h2, ← zpow_natCast (S.satake p) 2, ← zpow_neg]
    unfold symClockWeight
    congr 1

/-- **The recognition**: the GL(3) standard coefficients of the lift are literally
the `Sym²` transport coefficients of the seed — the Gelbart–Jacquet identification
at seed level. -/
theorem ofSym2_coeff_eq_sym2 (S : SatakeSeed) (j : ℕ) :
    cpsPolynomialPrimalCoeff (gl3PairOf (GL3Seed.ofSym2 S)) j
      = cpsPolynomialPrimalCoeff (symrSatakePairOf S 2) j := by
  unfold CriticalLinePhasor.GlobalHelix.cpsPolynomialPrimalCoeff
  have hw : (gl3PairOf (GL3Seed.ofSym2 S)).primal = (symrSatakePairOf S 2).primal := by
    funext p i
    exact gl3Weight_ofSym2_eq_symClock S p i
  rw [hw]

/-- **The mechanism fires unconditionally on the lift**: no self-duality hypothesis
remains — the reversal supplies it. -/
noncomputable def gl3_sym2_package_of_theta (S : SatakeSeed)
    (μs : List ℂ) (hne : μs ≠ []) (hμpos : ∀ μ ∈ μs, 0 ≤ μ.re)
    (ε : ℂ) (hε : ε ≠ 0)
    (hrefl : ∀ x : ℝ, 0 < x →
      cpsPolynomialFullPrimal3DBankReadout (gl3PairOf (GL3Seed.ofSym2 S)) 1 μs (1 / x) =
        (ε * ((x ^ (1 : ℝ) : ℝ) : ℂ)) •
          cpsPolynomialFullDual3DTransformedReadout (gl3PairOf (GL3Seed.ofSym2 S)) 1 μs
            (1 / x)) :
    NicePackage
      (coefficientArithmetic (cpsPolynomialPrimalCoeff (gl3PairOf (GL3Seed.ofSym2 S))))
      μs (mechB (gl3PairOf (GL3Seed.ofSym2 S))) ε :=
  gl3_package_of_theta_of (GL3Seed.ofSym2 S) (Equiv.swap 0 2) (ofSym2_selfdual S)
    μs hne hμpos ε hε hrefl

end CriticalLinePhasor.GeneralSeed

#print axioms CriticalLinePhasor.GeneralSeed.gl3PairOf
#print axioms CriticalLinePhasor.GeneralSeed.gl3PairOf_dual_eq_primal
#print axioms CriticalLinePhasor.GeneralSeed.gl3_package_of_theta_of
#print axioms CriticalLinePhasor.GeneralSeed.gl3_general_package_of_theta_of
#print axioms CriticalLinePhasor.GeneralSeed.gl3_real_package_of_theta_of
#print axioms CriticalLinePhasor.GeneralSeed.ofSym2_selfdual
#print axioms CriticalLinePhasor.GeneralSeed.ofSym2_coeff_eq_sym2
#print axioms CriticalLinePhasor.GeneralSeed.gl3_sym2_package_of_theta
