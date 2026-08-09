import RequestProject.SexticCascade
import RequestProject.RSPositivity

/-!
# Joint Sato–Tate moments for Maass pairs: the compiled harvest of the vehicles

The Serre-grade twisted families produced by the vehicle identities are exactly the
inputs of the **joint** Sato–Tate program for a pair of seeds `(f, g)`: the mixed
moment `E[S_a(θ_p(f))·S_b(θ_p(g))]` is governed by `L(Sym^a f × Sym^b g, s)` on
`Re s ≥ 1`, and the unconditional reach of that control is: the block `a, b ≤ 4`
(Jacquet–Piatetski-Shapiro–Shalika on automorphic pairs), the row `b = 0, a ≤ 9`
(Kim–Shahidi), and — from this week's vehicles — the entries `(5,1)`, `(6,1)`,
`(5,2)`, beyond the naive pair list.  This file compiles the layer that ties those
analytic objects to the equidistribution summands:

* `radialLocalEulerCoeff_one` — **the `h₁` law**: the degree-one local Euler
  coefficient is the sum of the weights;
* `bank_at_prime` — **the prime-readout law**: the value of any all-place bank at a
  prime is the sum of its local weight family — so a bank's prime values are exactly
  the mixed trace products its Dirichlet series averages;
* `trace_zpow` and explicit `zpow` forms — the bridge between the trace ladder and
  the `zpow` weight literals;
* `joint_51_at_prime` / `joint_61_at_prime` / `joint_52_at_prime` — the three new
  families' banks read `S₅(f)·S₁(g)`, `S₆(f)·S₁(g)`, `S₅(f)·S₂(g)` at every prime;
* `sym5Sym2_bank` — the `(5,2)` bank factorization, an instantiation of the
  universal `quinticTau_bank` at the `Sym²` clock of the second seed;
* `jointPrimeAverage` + `jointPrimeAverage_51_eq` (and `61`, `52`) — **the
  capstone**: the joint-moment prime average is literally the prime average of the
  compiled bank.

Grade register.  Compiled: the algebra and the readout laws, hypothesis-free.
Cited (Serre grade, `Re s ≥ 1`): the control of the three banks' Dirichlet series
via the vehicle chains (Kim–Shahidi both roles, Kim, JPSS, Shahidi).  Conjectural
target: for `f, g` non-isogenous seeds the joint moments vanish (independence);
the `(5,1)`, `(6,1)`, `(5,2)` entries extend the reachable mixed-moment matrix for
Maass pairs, subject to the named record-check against the current joint-Sato–Tate
literature before any novelty claim.  On the carrier there is no convergence gate —
the `Re s ≥ 1` framing is the 1D chart's readout of natively entire objects; the
grade deficit of division chains is another face of the registration step, not a
new wall.  No `axiom`, no `sorry`.
-/

open Finset ArithmeticFunction Complex UpperHalfPlane
open scoped MatrixGroups ArithmeticFunction.zeta LSeries.notation

namespace CriticalLinePhasor.JointMoments

open CriticalLinePhasor.GlobalHelix CriticalLinePhasor.CarrierTheta
open CriticalLinePhasor.SatoTateCarrier3D
open CriticalLinePhasor.Sym2Wire CriticalLinePhasor.Sym2Rankin CriticalLinePhasor.SymrBank
open CriticalLinePhasor.TransportClosure CriticalLinePhasor.TensorTowerBanks
open CriticalLinePhasor.CapVehicle CriticalLinePhasor.QuinticTwists
open CriticalLinePhasor.SexticCascade

variable {k k' : ℤ} {f : CuspForm 𝒮ℒ k} {g : CuspForm 𝒮ℒ k'}

/-! ## The `h₁` law and the prime-readout law -/

/-- **The `h₁` law**: the degree-one local Euler coefficient is the sum of the
weights. -/
theorem radialLocalEulerCoeff_one {ι : Type*} [Fintype ι] (w : ι → ℂ) :
    radialLocalEulerCoeff w 1 = ∑ i, w i := by
  classical
  unfold radialLocalEulerCoeff
  have hbij : Finset.finsuppAntidiag (Finset.univ : Finset ι) 1
      = Finset.univ.image (fun i => Finsupp.single i 1) := by
    ext F
    simp only [Finset.mem_finsuppAntidiag, Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hsum, -⟩
      have hex : ∃ i, F i ≠ 0 := by
        by_contra h
        push Not at h
        rw [Finset.sum_congr rfl fun j _ => h j, Finset.sum_const_zero] at hsum
        exact one_ne_zero hsum.symm
      obtain ⟨i, hi0⟩ := hex
      have hfi : 1 ≤ F i := Nat.one_le_iff_ne_zero.mpr hi0
      have hle : F i ≤ 1 := by
        calc F i ≤ ∑ j, F j :=
              Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
          _ = 1 := hsum
      have hfi1 : F i = 1 := le_antisymm hle hfi
      refine ⟨i, ?_⟩
      ext j
      by_cases hji : j = i
      · subst hji
        simp [hfi1]
      · have hj0 : F j = 0 := by
          by_contra hj0
          have hj1 : 1 ≤ F j := Nat.one_le_iff_ne_zero.mpr hj0
          have hsub : ∑ x ∈ ({j, i} : Finset ι), F x ≤ ∑ x, F x :=
            Finset.sum_le_sum_of_subset_of_nonneg
              (Finset.subset_univ ({j, i} : Finset ι)) (fun _ _ _ => Nat.zero_le _)
          rw [Finset.sum_pair hji, hsum] at hsub
          omega
        rw [hj0, Finsupp.single_apply, if_neg fun h => hji h.symm]
    · rintro ⟨i, rfl⟩
      refine ⟨?_, Finset.subset_univ _⟩
      simp [Finsupp.single_apply]
  rw [hbij, Finset.sum_image (fun a _ b _ h =>
    Finsupp.single_left_injective one_ne_zero h)]
  apply Finset.sum_congr rfl
  intro i _
  show ∏ j, w j ^ (Finsupp.single i 1) j = w i
  rw [Finset.prod_eq_single i
    (fun j _ hji => by rw [Finsupp.single_apply, if_neg fun h => hji h.symm, pow_zero])
    (fun h => absurd (Finset.mem_univ i) h)]
  simp

/-- **The prime-readout law**: any all-place bank's value at a prime is the sum of
its local weight family — the bank's prime values are the trace products its
Dirichlet series averages. -/
theorem bank_at_prime {ι : Type*} [Fintype ι]
    (w : Nat.Primes → ι → ℂ) (p : Nat.Primes) :
    coefficientArithmetic (radialGlobalSatakeCoeff w) p.1 = ∑ i, w p i := by
  have h := bankArithmetic_prime_pow w p.2 1
  rw [pow_one] at h
  rw [h, radialLocalEulerCoeff_one]
  rfl

/-! ## The trace ladder in `zpow` form -/

/-- The trace ladder written with integer powers. -/
theorem trace_zpow {α : ℂ} (hα : α ≠ 0) (r : ℕ) :
    symmetricPowerSatakeTrace α r
      = ∑ j ∈ Finset.range (r + 1), α ^ ((r : ℤ) - 2 * (j : ℤ)) := by
  unfold symmetricPowerSatakeTrace
  apply Finset.sum_congr rfl
  intro j hj
  have hjr : j ≤ r := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  rw [← zpow_natCast α (r - j), ← zpow_natCast (α⁻¹) j, inv_zpow, ← zpow_neg,
    ← zpow_add₀ hα]
  congr 1
  push_cast [hjr]
  ring

theorem trace_one_zpow {α : ℂ} (hα : α ≠ 0) :
    symmetricPowerSatakeTrace α 1 = α ^ (1 : ℤ) + α ^ (-1 : ℤ) := by
  rw [trace_zpow hα]
  norm_num [Finset.sum_range_succ]

theorem trace_two_zpow {α : ℂ} (hα : α ≠ 0) :
    symmetricPowerSatakeTrace α 2 = α ^ (2 : ℤ) + α ^ (0 : ℤ) + α ^ (-2 : ℤ) := by
  rw [trace_zpow hα]
  norm_num [Finset.sum_range_succ]

theorem trace_five_zpow {α : ℂ} (hα : α ≠ 0) :
    symmetricPowerSatakeTrace α 5
      = α ^ (5 : ℤ) + α ^ (3 : ℤ) + α ^ (1 : ℤ)
        + α ^ (-1 : ℤ) + α ^ (-3 : ℤ) + α ^ (-5 : ℤ) := by
  rw [trace_zpow hα]
  norm_num [Finset.sum_range_succ]

theorem trace_six_zpow {α : ℂ} (hα : α ≠ 0) :
    symmetricPowerSatakeTrace α 6
      = α ^ (6 : ℤ) + α ^ (4 : ℤ) + α ^ (2 : ℤ) + α ^ (0 : ℤ)
        + α ^ (-2 : ℤ) + α ^ (-4 : ℤ) + α ^ (-6 : ℤ) := by
  rw [trace_zpow hα]
  norm_num [Finset.sum_range_succ]

/-! ## The three joint families read the mixed trace products at every prime -/

theorem gSym5Weight_sum (β α : ℂ) :
    ∑ i, gSym5Weight β α i
      = (β ^ (1 : ℤ) + β ^ (-1 : ℤ))
        * (α ^ (5 : ℤ) + α ^ (3 : ℤ) + α ^ (1 : ℤ)
            + α ^ (-1 : ℤ) + α ^ (-3 : ℤ) + α ^ (-5 : ℤ)) := by
  simp [gSym5Weight, Fin.sum_univ_succ]
  ring

theorem gSym6Weight_sum (β α : ℂ) :
    ∑ i, gSym6Weight β α i
      = (β ^ (1 : ℤ) + β ^ (-1 : ℤ))
        * (α ^ (6 : ℤ) + α ^ (4 : ℤ) + α ^ (2 : ℤ) + α ^ (0 : ℤ)
            + α ^ (-2 : ℤ) + α ^ (-4 : ℤ) + α ^ (-6 : ℤ)) := by
  simp [gSym6Weight, Fin.sum_univ_succ]
  ring

theorem sym5TauWeight_sum (α : ℂ) (t : Fin 3 → ℂ) :
    ∑ i, sym5TauWeight α t i
      = (α ^ (5 : ℤ) + α ^ (3 : ℤ) + α ^ (1 : ℤ)
          + α ^ (-1 : ℤ) + α ^ (-3 : ℤ) + α ^ (-5 : ℤ)) * (t 0 + t 1 + t 2) := by
  simp [sym5TauWeight, Fin.sum_univ_succ]
  ring

/-- The `Sym²` clock of the second seed, as an abstract Satake triple. -/
noncomputable def sym2Clock (β : ℂ) : Fin 3 → ℂ :=
  ![β ^ (2 : ℤ), β ^ (0 : ℤ), β ^ (-2 : ℤ)]

/-- **The `(5,1)` readout**: the bank of the `m = 2` quintic family reads
`S₅(f)·S₁(g)` at every prime. -/
theorem joint_51_at_prime (G : HeckeEigenData g) (H : HeckeEigenData f)
    (p : Nat.Primes) (hβ : G.satake p.2 ≠ 0) (hα : H.satake p.2 ≠ 0) :
    coefficientArithmetic (radialGlobalSatakeCoeff
      (fun q => gSym5Weight (G.satake q.2) (H.satake q.2))) p.1
      = symmetricPowerSatakeTrace (H.satake p.2) 5
        * symmetricPowerSatakeTrace (G.satake p.2) 1 := by
  rw [bank_at_prime, gSym5Weight_sum, trace_five_zpow hα, trace_one_zpow hβ]
  ring

/-- **The `(6,1)` readout**: the cap-vehicle bank reads `S₆(f)·S₁(g)` at every
prime. -/
theorem joint_61_at_prime (G : HeckeEigenData g) (H : HeckeEigenData f)
    (p : Nat.Primes) (hβ : G.satake p.2 ≠ 0) (hα : H.satake p.2 ≠ 0) :
    coefficientArithmetic (radialGlobalSatakeCoeff
      (fun q => gSym6Weight (G.satake q.2) (H.satake q.2))) p.1
      = symmetricPowerSatakeTrace (H.satake p.2) 6
        * symmetricPowerSatakeTrace (G.satake p.2) 1 := by
  rw [bank_at_prime, gSym6Weight_sum, trace_six_zpow hα, trace_one_zpow hβ]
  ring

/-- **The `(5,2)` readout**: the `m = 3` quintic family at the `Sym²` clock of the
second seed reads `S₅(f)·S₂(g)` at every prime. -/
theorem joint_52_at_prime (G : HeckeEigenData g) (H : HeckeEigenData f)
    (p : Nat.Primes) (hβ : G.satake p.2 ≠ 0) (hα : H.satake p.2 ≠ 0) :
    coefficientArithmetic (radialGlobalSatakeCoeff
      (fun q => sym5TauWeight (H.satake q.2) (sym2Clock (G.satake q.2)))) p.1
      = symmetricPowerSatakeTrace (H.satake p.2) 5
        * symmetricPowerSatakeTrace (G.satake p.2) 2 := by
  rw [bank_at_prime, sym5TauWeight_sum, trace_five_zpow hα, trace_two_zpow hβ]
  have h0 : sym2Clock (G.satake p.2) 0 = (G.satake p.2) ^ (2 : ℤ) := rfl
  have h1 : sym2Clock (G.satake p.2) 1 = (G.satake p.2) ^ (0 : ℤ) := rfl
  have h2 : sym2Clock (G.satake p.2) 2 = (G.satake p.2) ^ (-2 : ℤ) := rfl
  rw [h0, h1, h2]

/-- **The `(5,2)` bank factorization** — the universal `quinticTau_bank`
instantiated at the second seed's `Sym²` clock:
`L((f⊠Sym²g) × Sym⁴f) = L(Sym⁵f × Sym²g) · L(Sym³f × Sym²g)` at every `n`. -/
theorem sym5Sym2_bank (G : HeckeEigenData g) (H : HeckeEigenData f) :
    coefficientArithmetic (radialGlobalSatakeCoeff
      (fun p => quinticTauWeight (H.satake p.2) (sym2Clock (G.satake p.2))))
      = coefficientArithmetic (radialGlobalSatakeCoeff
          (fun p => sym5TauWeight (H.satake p.2) (sym2Clock (G.satake p.2))))
        * coefficientArithmetic (radialGlobalSatakeCoeff
            (fun p => sym3TauWeight (H.satake p.2) (sym2Clock (G.satake p.2)))) :=
  quinticTau_bank H (fun p => sym2Clock (G.satake p.2))

/-! ## The joint prime average is the bank's prime average -/

/-- The literal first-prime average of the mixed symmetric-power trace products —
the `(a,b)` joint Sato–Tate moment at scale `n`. -/
noncomputable def jointPrimeAverage (satF satG : Nat.Primes → ℂ) (a b n : ℕ) : ℝ :=
  (1 / ((n + 1 : ℕ) : ℝ)) *
    ∑ i : Fin (n + 1),
      (symmetricPowerSatakeTrace (satF (nthPrime i)) a
        * symmetricPowerSatakeTrace (satG (nthPrime i)) b).re

/-- **The capstone, `(5,1)`**: the joint-moment prime average is the prime average
of the compiled `m = 2` quintic bank. -/
theorem jointPrimeAverage_51_eq (G : HeckeEigenData g) (H : HeckeEigenData f)
    (n : ℕ) (hall : ∀ q : Nat.Primes, H.satake q.2 ≠ 0 ∧ G.satake q.2 ≠ 0) :
    jointPrimeAverage (fun q => H.satake q.2) (fun q => G.satake q.2) 5 1 n
      = (1 / ((n + 1 : ℕ) : ℝ)) *
          ∑ i : Fin (n + 1),
            (coefficientArithmetic (radialGlobalSatakeCoeff
              (fun q => gSym5Weight (G.satake q.2) (H.satake q.2)))
                (nthPrime i).1).re := by
  unfold jointPrimeAverage
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [joint_51_at_prime G H (nthPrime i) (hall _).2 (hall _).1]

/-- **The capstone, `(6,1)`**. -/
theorem jointPrimeAverage_61_eq (G : HeckeEigenData g) (H : HeckeEigenData f)
    (n : ℕ) (hall : ∀ q : Nat.Primes, H.satake q.2 ≠ 0 ∧ G.satake q.2 ≠ 0) :
    jointPrimeAverage (fun q => H.satake q.2) (fun q => G.satake q.2) 6 1 n
      = (1 / ((n + 1 : ℕ) : ℝ)) *
          ∑ i : Fin (n + 1),
            (coefficientArithmetic (radialGlobalSatakeCoeff
              (fun q => gSym6Weight (G.satake q.2) (H.satake q.2)))
                (nthPrime i).1).re := by
  unfold jointPrimeAverage
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [joint_61_at_prime G H (nthPrime i) (hall _).2 (hall _).1]

/-- **The capstone, `(5,2)`**. -/
theorem jointPrimeAverage_52_eq (G : HeckeEigenData g) (H : HeckeEigenData f)
    (n : ℕ) (hall : ∀ q : Nat.Primes, H.satake q.2 ≠ 0 ∧ G.satake q.2 ≠ 0) :
    jointPrimeAverage (fun q => H.satake q.2) (fun q => G.satake q.2) 5 2 n
      = (1 / ((n + 1 : ℕ) : ℝ)) *
          ∑ i : Fin (n + 1),
            (coefficientArithmetic (radialGlobalSatakeCoeff
              (fun q => sym5TauWeight (H.satake q.2) (sym2Clock (G.satake q.2))))
                (nthPrime i).1).re := by
  unfold jointPrimeAverage
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [joint_52_at_prime G H (nthPrime i) (hall _).2 (hall _).1]

end CriticalLinePhasor.JointMoments

#print axioms CriticalLinePhasor.JointMoments.radialLocalEulerCoeff_one
#print axioms CriticalLinePhasor.JointMoments.bank_at_prime
#print axioms CriticalLinePhasor.JointMoments.trace_zpow
#print axioms CriticalLinePhasor.JointMoments.joint_51_at_prime
#print axioms CriticalLinePhasor.JointMoments.joint_61_at_prime
#print axioms CriticalLinePhasor.JointMoments.joint_52_at_prime
#print axioms CriticalLinePhasor.JointMoments.sym5Sym2_bank
#print axioms CriticalLinePhasor.JointMoments.jointPrimeAverage_51_eq
#print axioms CriticalLinePhasor.JointMoments.jointPrimeAverage_52_eq
