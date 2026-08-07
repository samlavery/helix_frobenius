import RequestProject.SymCubeQuartic
import RequestProject.CPSGenuineGL2StandardRung3D
import RequestProject.CarrierTargetIdentification

/-!
# The seed standard rung, inhabited — and the tensor walls collapsed

Mining `CPSGenuineGL2StandardRung3D`: the standard rung's reflection is **derived from
Hecke's inversion** (the modular slash law on the vertical line), its pair is strong
(masses zero, entire `Λ`), and its sole arithmetic field is the Euler certificate
`coeff_eq`.  This file provides the first inhabitant — the eigenform seed itself — and
uses the resulting compiled functional equation to collapse the tensor walls of the
symmetric cube and quartic to their irreducible single-object cores.

* `seedRungData` — **the inhabitant**: for a weight-`2n` level-one eigenform, the form
  `2•f` with the rank-1 clock pair `symrSatakePair H 1` satisfies the certificate: the
  det-one field is the clock algebra, and `coeff_eq` is the compiled rank-uniform
  coefficient identification (`radialGlobal_eq_symrBank` at `r = 1` and
  `symrBank_one_rank`) unwound through the Deligne normalization;
* `seed_symm_Lambda_eq` — the pair is its own contragredient: both completed transforms
  equal the standard completion on the open initial half-plane, and entirety plus the
  identity theorem globalize the equality;
* `seed_selfdual_FE` — **Hecke's completed functional equation, genuinely compiled**:
  `Λ(1−s) = (−1)ⁿ·Λ(s)`, with `Λ` entire and equal to
  `Γℂ(s + (n−½))·D(s)` on the initial half-plane — the `r = 1` standard-side wall,
  crossed from modularity alone;
* `wall_collapse` — the generic scalar-cancellation equivalence: for a self-dual cofactor
  with nonzero root number, the product functional equation is equivalent to the
  cofactor-weighted cross equation of the remaining factor;
* `sym3_wall_collapse` / `sym4_wall_collapse` — **the dissolution**: the symmetric-cube
  tensor wall is equivalent to the `Sym³` single-object self-duality (cofactor the
  compiled seed `Λ`), and the quartic tensor wall to the `Sym⁴` single-object
  self-duality (cofactor the compiled `Λζ·Λ̄`, both reflections already landed).

No `axiom`, no `sorry`.
-/

open Finset ArithmeticFunction Complex UpperHalfPlane
open scoped MatrixGroups

namespace CriticalLinePhasor.SeedStandardRung

open CriticalLinePhasor.GlobalHelix CriticalLinePhasor.GenuineGL2Carrier
open CriticalLinePhasor.Sym2Wire CriticalLinePhasor.SymrBank
open CriticalLinePhasor.SymCubeQuartic CriticalLinePhasor.Unfolding
open CriticalLinePhasor.Sym2Rankin

/-- The rank-1 clock pair is det-one: the two channels are `α` and `α⁻¹`. -/
theorem symrSatakePair_one_detOne {n : ℕ} {f : CuspForm 𝒮ℒ (2 * n : ℤ)}
    (H : HeckeEigenData f) (p : Nat.Primes) :
    (symrSatakePair H 1).primal p 1 = ((symrSatakePair H 1).primal p 0)⁻¹ := by
  show symClockWeight 1 (H.satake p.2) 1 = (symClockWeight 1 (H.satake p.2) 0)⁻¹
  unfold symClockWeight
  norm_num

/-- **The Euler certificate of the seed**, discharged: the q-expansion of `2•f` is twice
the det-one-normalized rank-1 clock bank at the standard shift. -/
theorem seed_coeff_eq {n : ℕ} {f : CuspForm 𝒮ℒ (2 * n : ℤ)}
    (H : HeckeEigenData f) (j : ℕ) :
    (UpperHalfPlane.qExpansion 1 ⇑((2 : ℂ) • f)).coeff (j + 1) =
      2 * cpsPolynomialPrimalCoeff (symrSatakePair H 1) j *
        ((j + 1 : ℕ) : ℂ) ^ standardShift n := by
  have hsmul : (UpperHalfPlane.qExpansion 1 ⇑((2 : ℂ) • f)).coeff (j + 1)
      = 2 * (UpperHalfPlane.qExpansion 1 ⇑f).coeff (j + 1) := by
    rw [show (⇑((2 : ℂ) • f) : ℍ → ℂ) = (2 : ℂ) • ⇑f from rfl,
      ModularForm.qExpansion_smul one_pos one_mem_strictPeriods_SL 2 f]
    simp
  have hbank : cpsPolynomialPrimalCoeff (symrSatakePair H 1) j
      = seedNorm f (j + 1) := by
    show radialGlobalSatakeCoeff (fun p => fun i : Fin 2 =>
      symClockWeight 1 (H.satake p.2) (i : ℕ)) j = _
    rw [show radialGlobalSatakeCoeff (fun p => fun i : Fin 2 =>
        symClockWeight 1 (H.satake p.2) (i : ℕ)) j = symrBank H 1 (j + 1) from
      CriticalLinePhasor.Sym2Join.radialGlobal_eq_symrBank H 1 j,
      symrBank_one_rank H]
  have hpow : (0 : ℝ) < ((j + 1 : ℕ) : ℝ) ^ ((((2 * n : ℤ) : ℝ) - 1) / 2) :=
    Real.rpow_pos_of_pos (by positivity) _
  have hrecover : (UpperHalfPlane.qExpansion 1 ⇑f).coeff (j + 1)
      = seedNorm f (j + 1) *
        ((((j + 1 : ℕ) : ℝ) ^ ((((2 * n : ℤ) : ℝ) - 1) / 2) : ℝ) : ℂ) := by
    rw [seedNorm_apply (Nat.succ_ne_zero j), div_mul_cancel₀]
    exact_mod_cast hpow.ne'
  have hshift : ((((j + 1 : ℕ) : ℝ) ^ ((((2 * n : ℤ) : ℝ) - 1) / 2) : ℝ) : ℂ)
      = ((j + 1 : ℕ) : ℂ) ^ standardShift n := by
    rw [show ((((2 * n : ℤ) : ℝ)) - 1) / 2 = standardShiftR n by
      unfold standardShiftR
      push_cast
      ring]
    rw [Complex.ofReal_cpow (by positivity)]
    norm_cast
  rw [hsmul, hbank, hrecover, hshift]
  ring

/-- **The seed standard rung, inhabited.** -/
noncomputable def seedRungData {n : ℕ} (hn : 0 < n) {f : CuspForm 𝒮ℒ (2 * n : ℤ)}
    (H : HeckeEigenData f) :
    StandardRungEulerData n (symrSatakePair H 1) :=
  StandardRungEulerData.ofDetOne ((2 : ℂ) • f) hn (seed_coeff_eq H)
    (symrSatakePair_one_detOne H)

/-- The open initial half-plane of the rank-1 pair. -/
noncomputable def seedBound {n : ℕ} {f : CuspForm 𝒮ℒ (2 * n : ℤ)}
    (H : HeckeEigenData f) : ℝ :=
  ((2 + (symrSatakePair H 1).primalExponent : ℕ) : ℝ) + 1

/-- A point of the open half-plane is a completion point of the standard clock. -/
noncomputable def seedPoint {n : ℕ} (hn : 0 < n) {f : CuspForm 𝒮ℒ (2 * n : ℤ)}
    (H : HeckeEigenData f) {s : ℂ} (hs : seedBound H < s.re) :
    CPSCompletionPoint (symrSatakePair H 1) (standardClock n) where
  s := s
  shifts_pos := by
    intro μ hμ
    simp only [standardClock, List.mem_singleton] at hμ
    subst hμ
    have h0 : (0 : ℝ) ≤ seedBound H := by
      unfold seedBound
      positivity
    have hshift : (0 : ℝ) ≤ standardShiftR n := by
      unfold standardShiftR
      have : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      linarith
    simp only [standardShift, Complex.add_re, Complex.ofReal_re]
    linarith
  primal_dirichlet := by
    unfold seedBound at hs
    simpa using hs
  dual_dirichlet := by
    unfold seedBound at hs
    have hdual : (symrSatakePair H 1).dualExponent
        = (symrSatakePair H 1).primalExponent := rfl
    rw [show (Fintype.card (Fin (1 + 1)) + (symrSatakePair H 1).dualExponent : ℕ)
        = (2 + (symrSatakePair H 1).primalExponent : ℕ) by simp [hdual]]
    exact hs
  
/-- **The pair is its own contragredient**: the two completed transforms agree on the
open initial half-plane through the standard completion, hence everywhere by entirety
and the identity theorem. -/
theorem seed_symm_Lambda_eq {n : ℕ} (hn : 0 < n) {f : CuspForm 𝒮ℒ (2 * n : ℤ)}
    (H : HeckeEigenData f) :
    (seedRungData hn H).toReflectedThetaSource.pair.symm.Λ
      = (seedRungData hn H).toReflectedThetaSource.pair.Λ := by
  refine CriticalLinePhasor.CarrierTargetIdentification.entire_eq_of_eqOn_isOpen
    (seedRungData hn H).toReflectedThetaSource.pair.symm.differentiable_Λ
    (seedRungData hn H).toReflectedThetaSource.pair.differentiable_Λ
    (U := {s : ℂ | seedBound H < s.re})
    (IsOpen.preimage Complex.continuous_re isOpen_Ioi)
    (z₀ := ((seedBound H + 1 : ℝ) : ℂ))
    (by
      simp only [Set.mem_setOf_eq, Complex.ofReal_re]
      linarith)
    ?_
  intro s hs
  simp only [Set.mem_setOf_eq] at hs
  exact (standardRung_dualLambda_eq_standardCompletion (seedRungData hn H)
      (seedPoint hn H hs)).trans
    (standardRung_Lambda_eq_standardCompletion (seedRungData hn H)
      (seedPoint hn H hs)).symm

/-- **Hecke's completed functional equation, compiled**: `Λ(1−s) = (−1)ⁿ·Λ(s)` for the
seed standard rung — the `r = 1` standard-side self-duality, from modularity alone. -/
theorem seed_selfdual_FE {n : ℕ} (hn : 0 < n) {f : CuspForm 𝒮ℒ (2 * n : ℤ)}
    (H : HeckeEigenData f) (s : ℂ) :
    (seedRungData hn H).toReflectedThetaSource.pair.Λ (1 - s)
      = ((-1 : ℂ) ^ n) * (seedRungData hn H).toReflectedThetaSource.pair.Λ s := by
  have h := standardRung_functional_equation (seedRungData hn H) s
  rw [seed_symm_Lambda_eq hn H] at h
  rw [h, smul_eq_mul]
  congr 1
  rw [pow_mul, Complex.I_sq]

/-- **The generic wall collapse**: for a self-dual cofactor with nonzero root number,
the product functional equation is equivalent to the cofactor-weighted cross equation
of the remaining factor. -/
theorem wall_collapse {Z G : ℂ → ℂ} {εZ εG : ℂ} (hεZ : εZ ≠ 0)
    (hZ : ∀ s : ℂ, Z (1 - s) = εZ * Z s) :
    (∀ s : ℂ, Z (1 - s) * G (1 - s) = (εZ * εG) * (Z s * G s)) ↔
      (∀ s : ℂ, Z s * G (1 - s) = εG * (Z s * G s)) := by
  constructor <;> intro h s
  · have hs := h s
    rw [hZ s] at hs
    have hcancel : εZ * (Z s * G (1 - s)) = εZ * (εG * (Z s * G s)) := by
      linear_combination hs
    exact mul_left_cancel₀ hεZ hcancel
  · rw [hZ s]
    linear_combination εZ * h s

/-- **The symmetric-cube wall, collapsed**: for any completed `Sym³` candidate `G`, the
degree-6 tensor functional equation (cofactor the compiled seed `Λ`) is equivalent to
the `Sym³` single-object self-duality weighted by the seed transform. -/
theorem sym3_wall_collapse {n : ℕ} (hn : 0 < n) {f : CuspForm 𝒮ℒ (2 * n : ℤ)}
    (H : HeckeEigenData f) (G : ℂ → ℂ) (εG : ℂ) :
    (∀ s : ℂ, (seedRungData hn H).toReflectedThetaSource.pair.Λ (1 - s) * G (1 - s)
        = (((-1 : ℂ) ^ n) * εG) *
          ((seedRungData hn H).toReflectedThetaSource.pair.Λ s * G s)) ↔
      (∀ s : ℂ, (seedRungData hn H).toReflectedThetaSource.pair.Λ s * G (1 - s)
        = εG * ((seedRungData hn H).toReflectedThetaSource.pair.Λ s * G s)) :=
  wall_collapse (by
    intro h0
    exact absurd h0 (pow_ne_zero n (by norm_num : (-1 : ℂ) ≠ 0)))
    (seed_selfdual_FE hn H)

/-- **The symmetric-quartic wall, collapsed**: for any completed `Sym⁴` candidate `G`,
the degree-9 tensor functional equation (cofactor the compiled `Λζ·Λ̄`, both reflections
landed) is equivalent to the `Sym⁴` single-object self-duality weighted by that
cofactor. -/
theorem sym4_wall_collapse {k : ℤ} (f : CuspForm 𝒮ℒ k) (hk : 0 ≤ k)
    (G : ℂ → ℂ) (εG : ℂ) :
    (∀ s : ℂ, (completedRiemannZeta (1 - s) * (rsAveragedWeakFEPair f hk).Λ (1 - s))
        * G (1 - s)
        = ((1 : ℂ) * εG) * ((completedRiemannZeta s * (rsAveragedWeakFEPair f hk).Λ s)
          * G s)) ↔
      (∀ s : ℂ, (completedRiemannZeta s * (rsAveragedWeakFEPair f hk).Λ s) * G (1 - s)
        = εG * ((completedRiemannZeta s * (rsAveragedWeakFEPair f hk).Λ s) * G s)) :=
  wall_collapse (Z := fun s => completedRiemannZeta s * (rsAveragedWeakFEPair f hk).Λ s)
    (εZ := 1) one_ne_zero (fun s => by
      rw [completedRiemannZeta_one_sub, rsAveraged_selfdual_FE f hk s, one_mul])

end CriticalLinePhasor.SeedStandardRung

#print axioms CriticalLinePhasor.SeedStandardRung.symrSatakePair_one_detOne
#print axioms CriticalLinePhasor.SeedStandardRung.seed_coeff_eq
#print axioms CriticalLinePhasor.SeedStandardRung.seedRungData
#print axioms CriticalLinePhasor.SeedStandardRung.seed_symm_Lambda_eq
#print axioms CriticalLinePhasor.SeedStandardRung.seed_selfdual_FE
#print axioms CriticalLinePhasor.SeedStandardRung.wall_collapse
#print axioms CriticalLinePhasor.SeedStandardRung.sym3_wall_collapse
#print axioms CriticalLinePhasor.SeedStandardRung.sym4_wall_collapse
