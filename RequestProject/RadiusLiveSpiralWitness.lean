import RequestProject.CPSRadiusLiveNiceness3D

/-!
# The spiral witness: temperedness is not encoded upstream

The non-circularity control the radial-limit chain calls for, compiled.  `spiralPair` is the
maximally non-tempered det-one rank-two Satake datum — `α_p = p`, radius `p` at every prime, a
genuine *spiral*, not a helix.  Three theorems separate the layers exactly:

* `spiralPair_radius` / `spiralPair_not_unitary` — the datum is genuinely non-tempered: its
  strand radius is `p`, never `1`;
* `spiralPair_twisted_entire` / `spiralPair_twisted_FE` — the **entire radius-live niceness
  payload holds verbatim on the spiral**: entirety and the global functional equation of the
  twisted completed transform, for every CPS twist degree and every polynomial twist datum.
  Niceness therefore cannot encode temperedness: it accepts the spiral;
* `spiralPair_violates_towerCeiling` — the spiral **fails the rank-uniform tower ceiling** at
  the first rung, so the radial capstone (`strand_radius_one_of_tower_ceiling`), whose only
  inputs are the two ceilings, correctly refuses it.

Register: unit modulus enters the chain exactly once — as the *conclusion* of the radial limit
from the ceilings the automorphic tower supplies — and nowhere as an input.  The unit-modulus
payload (`UnitaryPrimePhase`, `UnitarySatakeFamily`) is a specialization, off the load-bearing
chain.  No RH/GRH.
-/

open Complex

namespace CriticalLinePhasor.GlobalHelix

/-- The spiral: the det-one rank-two Satake datum with `α_p = p` — radius `p` at every prime,
maximally non-tempered within the trivial Hecke bound. -/
noncomputable def spiralPair : PolynomialSatakeDualPair (Fin 2) where
  primal := fun p i => if i = 0 then ((p.1 : ℕ) : ℂ) else (((p.1 : ℕ) : ℂ))⁻¹
  dual := fun p i => (if i = 0 then ((p.1 : ℕ) : ℂ) else (((p.1 : ℕ) : ℂ))⁻¹)⁻¹
  primalExponent := 1
  dualExponent := 1
  primal_ne_zero := by
    intro p i
    have hp : ((p.1 : ℕ) : ℂ) ≠ 0 := by
      exact_mod_cast Nat.Prime.ne_zero p.2
    by_cases h : i = 0 <;> simp [h, hp]
  dual_eq_inv := fun _ _ => rfl
  primal_bound := by
    intro p i
    have hp2 : (2 : ℝ) ≤ (p.1 : ℝ) := by exact_mod_cast p.2.two_le
    by_cases h : i = 0
    · rw [if_pos h, Complex.norm_natCast, pow_one]
    · rw [if_neg h, norm_inv, Complex.norm_natCast, pow_one]
      have h1 : ((p.1 : ℕ) : ℝ)⁻¹ ≤ 1 := by
        rw [inv_le_one_iff₀]; right; linarith
      linarith
  dual_bound := by
    intro p i
    have hp2 : (2 : ℝ) ≤ (p.1 : ℝ) := by exact_mod_cast p.2.two_le
    by_cases h : i = 0
    · rw [if_pos h, norm_inv, Complex.norm_natCast, pow_one]
      have h1 : ((p.1 : ℕ) : ℝ)⁻¹ ≤ 1 := by
        rw [inv_le_one_iff₀]; right; linarith
      linarith
    · rw [if_neg h, inv_inv, Complex.norm_natCast, pow_one]

/-- The spiral's strand radius is `p` — the radial channel maximally open. -/
theorem spiralPair_radius (p : Nat.Primes) :
    ‖spiralPair.primal p 0‖ = (p.1 : ℝ) := by
  simp [spiralPair]

/-- The spiral is genuinely non-tempered: its strand is never unit-modulus. -/
theorem spiralPair_not_unitary (p : Nat.Primes) :
    ‖spiralPair.primal p 0‖ ≠ 1 := by
  rw [spiralPair_radius]
  have hp2 : (2 : ℝ) ≤ (p.1 : ℝ) := by exact_mod_cast p.2.two_le
  linarith

/-- The spiral is det-one: the Frobenius balance holds with the radius wide open. -/
theorem spiralPair_detOne (p : Nat.Primes) :
    spiralPair.primal p 1 = (spiralPair.primal p 0)⁻¹ := by
  simp [spiralPair]

/-- **Niceness accepts the spiral: entirety.**  The completed transform of every CPS twist of
the maximally non-tempered datum is entire — the radius-live payload verbatim, so entirety
encodes no temperedness. -/
theorem spiralPair_twisted_entire (r m : ℕ) (hm : 1 ≤ m) (hmr : m < r)
    (tau : PolynomialSatakeDualPair (Fin m)) :
    Differentiable ℂ
      (cpsPolynomialStrongFEPair (arithmeticCPSPolynomialTwist r m spiralPair tau)).Λ :=
  ((cpsArithmeticTwist_radiusLive_niceness r m hm hmr spiralPair tau).2).1

/-- **Niceness accepts the spiral: the functional equation.**  The global completed functional
equation holds on the spiral's every twist — the reflection encodes no temperedness either. -/
theorem spiralPair_twisted_FE (r m : ℕ) (hm : 1 ≤ m) (hmr : m < r)
    (tau : PolynomialSatakeDualPair (Fin m)) (s : ℂ) :
    (cpsPolynomialStrongFEPair (arithmeticCPSPolynomialTwist r m spiralPair tau)).Λ
        ((cpsPolynomialStrongFEPair (arithmeticCPSPolynomialTwist r m spiralPair tau)).k - s) =
      (cpsPolynomialStrongFEPair (arithmeticCPSPolynomialTwist r m spiralPair tau)).ε •
        (cpsPolynomialStrongFEPair
          (arithmeticCPSPolynomialTwist r m spiralPair tau)).symm.Λ s :=
  ((cpsArithmeticTwist_radiusLive_niceness r m hm hmr spiralPair tau).2).2.2.2.2 s

/-- **The tower ceiling refuses the spiral.**  Already at the first rung the spiral's top
strand exceeds `p^{1/2}`, so the rank-uniform ceiling hypothesis of the radial capstone
(`strand_radius_one_of_tower_ceiling`) fails — unit radius is forced only where the automorphic
tower genuinely supplies the ceilings. -/
theorem spiralPair_violates_towerCeiling (p : Nat.Primes) :
    ¬ (∀ r : ℕ, 1 ≤ r →
        ‖spiralPair.primal p 0 ^ r‖ ≤ ((p.1 : ℝ)) ^ ((1 : ℝ) / 2)) := by
  intro h
  have h1 := h 1 le_rfl
  rw [pow_one, spiralPair_radius] at h1
  have hp2 : (2 : ℝ) ≤ (p.1 : ℝ) := by exact_mod_cast p.2.two_le
  have hlt : ((p.1 : ℝ)) ^ ((1 : ℝ) / 2) < ((p.1 : ℝ)) ^ ((1 : ℝ)) := by
    apply Real.rpow_lt_rpow_of_exponent_lt (by linarith) (by norm_num)
  rw [Real.rpow_one] at hlt
  linarith

end CriticalLinePhasor.GlobalHelix

#print axioms CriticalLinePhasor.GlobalHelix.spiralPair_radius
#print axioms CriticalLinePhasor.GlobalHelix.spiralPair_not_unitary
#print axioms CriticalLinePhasor.GlobalHelix.spiralPair_detOne
#print axioms CriticalLinePhasor.GlobalHelix.spiralPair_twisted_entire
#print axioms CriticalLinePhasor.GlobalHelix.spiralPair_twisted_FE
#print axioms CriticalLinePhasor.GlobalHelix.spiralPair_violates_towerCeiling
