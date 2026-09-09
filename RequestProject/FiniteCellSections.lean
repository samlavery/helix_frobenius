import Mathlib.RingTheory.Polynomial.DegreeLT
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

/-!
Finite section-count step for the carrier/anti-carrier surface route, ledger 639.

Unfolded target: for distinct nodes a_i and nonnegative integers m_i, the space of
polynomials P of degree < N with (taylor a_i P).coeff j = 0 for every j < m_i
has complex dimension N - sum_i m_i (truncated subtraction). Multiplicities are
constraints on jets; they are not replaced by a count of distinct nodes.

Construction A: `let D := ∏ i, (X - C (a i)) ^ m i`; multiplication by D identifies
the space with polynomials of degree < N - degree D.
Construction B: `let E := ...` the simultaneous Taylor-evaluation map; compute its
kernel by the coprime-factor criterion. Both descriptions are identified below.
The bank is finite; there is no zero census or arithmetic function in its definition.

Searches: `rg -n 'section.*count|finrank.*vanish|vanishing.*space|Riemann.*Roch'
RequestProject`; `rg -n 'degreeLT|divMod.*Equiv|finrank_range_of_inj|X_sub_C_pow_dvd|
X_pow_dvd_iff|pairwise_coprime_X_sub_C|prod_dvd_of_coprime|natDegree_prod_of_monic'
.lake/packages/mathlib/Mathlib`. LeanSearch: polynomial degree-bounded spaces and
vanishing Taylor coefficients; Loogle: `Polynomial.degreeLT, Module.finrank` and
`"finrank", "range", "injective"`.
-/

open Polynomial Module

namespace CriticalLinePhasor.FiniteCellSections

variable {K : Type*} [Field K]

/-- Sections with N available modes and prescribed divisor D. -/
def sections (D : K[X]) (N : ℕ) : Submodule K K[X] where
  carrier := {P | P ∈ Polynomial.degreeLT K N ∧ D ∣ P}
  zero_mem' := ⟨Submodule.zero_mem _, dvd_zero _⟩
  add_mem' := fun ha hb => ⟨Submodule.add_mem _ ha.1 hb.1, dvd_add ha.2 hb.2⟩
  smul_mem' := by
    intro a P hP
    refine ⟨Submodule.smul_mem _ a hP.1, ?_⟩
    rw [Polynomial.smul_eq_C_mul]
    exact dvd_mul_of_dvd_right hP.2 _

theorem mul_mem_degreeLT_iff {D : K[X]} (hD : D ≠ 0) (Q : K[X]) (N : ℕ) :
    D * Q ∈ Polynomial.degreeLT K N ↔
      Q ∈ Polynomial.degreeLT K (N - D.natDegree) := by
  by_cases hQ : Q = 0
  · simp [hQ]
  · rw [Polynomial.mem_degreeLT, Polynomial.mem_degreeLT,
      ← Polynomial.natDegree_lt_iff_degree_lt (mul_ne_zero hD hQ),
      ← Polynomial.natDegree_lt_iff_degree_lt hQ, Polynomial.natDegree_mul hD hQ]
    omega

/-- Multiply the free remaining modes by the prescribed divisor. -/
noncomputable def multiplyInto (D : K[X]) (hD : D ≠ 0) (N : ℕ) :
    Polynomial.degreeLT K (N - D.natDegree) →ₗ[K] sections D N where
  toFun Q := ⟨D * Q, (mul_mem_degreeLT_iff hD Q N).mpr Q.property, dvd_mul_right _ _⟩
  map_add' Q R := by apply Subtype.ext; simp [mul_add]
  map_smul' a Q := by apply Subtype.ext; simp

theorem multiplyInto_injective (D : K[X]) (hD : D ≠ 0) (N : ℕ) :
    Function.Injective (multiplyInto D hD N) := by
  intro Q R h
  apply Subtype.ext
  exact mul_left_cancel₀ hD (congrArg Subtype.val h)

theorem multiplyInto_surjective (D : K[X]) (hD : D ≠ 0) (N : ℕ) :
    Function.Surjective (multiplyInto D hD N) := by
  intro P
  obtain ⟨Q, hQ⟩ := P.property.2
  have hmem : Q ∈ Polynomial.degreeLT K (N - D.natDegree) :=
    (mul_mem_degreeLT_iff hD Q N).mp (hQ ▸ P.property.1)
  exact ⟨⟨Q, hmem⟩, Subtype.ext hQ.symm⟩

noncomputable def sectionEquiv (D : K[X]) (hD : D ≠ 0) (N : ℕ) :
    Polynomial.degreeLT K (N - D.natDegree) ≃ₗ[K] sections D N :=
  LinearEquiv.ofBijective (multiplyInto D hD N)
    ⟨multiplyInto_injective D hD N, multiplyInto_surjective D hD N⟩

theorem finrank_sections (D : K[X]) (hD : D ≠ 0) (N : ℕ) :
    Module.finrank K (sections D N) = N - D.natDegree := by
  rw [← (sectionEquiv D hD N).finrank_eq, (Polynomial.degreeLTEquiv K _).finrank_eq]
  simp

variable {ι : Type*} [Fintype ι]

/-- A finite cell configuration, with the full prescribed multiplicity at each node. -/
noncomputable def cellDivisor (a : ι → K) (m : ι → ℕ) : K[X] :=
  ∏ i, (X - C (a i)) ^ m i

theorem cellDivisor_monic (a : ι → K) (m : ι → ℕ) : (cellDivisor a m).Monic := by
  exact Polynomial.monic_prod_of_monic _ _ (fun i _ => (Polynomial.monic_X_sub_C (a i)).pow _)

theorem cellDivisor_natDegree (a : ι → K) (m : ι → ℕ) :
    (cellDivisor a m).natDegree = ∑ i, m i := by
  rw [cellDivisor, Polynomial.natDegree_prod_of_monic _ _
    (fun i _ => (Polynomial.monic_X_sub_C (a i)).pow _)]
  simp

theorem finrank_cellSections (a : ι → K) (m : ι → ℕ) (N : ℕ) :
    Module.finrank K (sections (cellDivisor a m) N) = N - ∑ i, m i := by
  rw [finrank_sections _ (cellDivisor_monic a m).ne_zero, cellDivisor_natDegree]

theorem cellDivisor_dvd_iff (a : ι → K) (ha : Function.Injective a) (m : ι → ℕ)
    (P : K[X]) : cellDivisor a m ∣ P ↔ ∀ i, (X - C (a i)) ^ m i ∣ P := by
  constructor
  · intro h i
    exact (Finset.dvd_prod_of_mem (fun j => (X - C (a j)) ^ m j) (Finset.mem_univ i)).trans h
  · intro h
    exact Fintype.prod_dvd_of_coprime
      (fun i j hij => (Polynomial.pairwise_coprime_X_sub_C ha hij).pow) h

theorem cellDivisor_dvd_iff_taylor (a : ι → K) (ha : Function.Injective a) (m : ι → ℕ)
    (P : K[X]) : cellDivisor a m ∣ P ↔ ∀ i j, j < m i → (Polynomial.taylor (a i) P).coeff j = 0 := by
  rw [cellDivisor_dvd_iff a ha]
  apply forall_congr'
  intro i
  rw [Polynomial.X_sub_C_pow_dvd_iff, Polynomial.X_pow_dvd_iff]
  rfl

/-- The actual simultaneous Taylor constraints on the N-mode bank. -/
noncomputable def jetEvaluation (a : ι → K) (m : ι → ℕ) (N : ℕ) :
    Polynomial.degreeLT K N →ₗ[K] ((i : ι) → Fin (m i) → K) where
  toFun P i j := (Polynomial.taylor (a i) (P : K[X])).coeff j
  map_add' P Q := by ext i j; simp
  map_smul' b P := by ext i j; simp

omit [Fintype ι] in
theorem mem_ker_jetEvaluation (a : ι → K) (m : ι → ℕ) (N : ℕ)
    (P : Polynomial.degreeLT K N) :
    P ∈ LinearMap.ker (jetEvaluation a m N) ↔
      ∀ i j, j < m i → (Polynomial.taylor (a i) (P : K[X])).coeff j = 0 := by
  rw [LinearMap.mem_ker]
  constructor
  · intro h i j hj
    exact congrFun (congrFun h i) ⟨j, hj⟩
  · intro h
    funext i j
    exact h i j j.isLt

/-- The evaluation-kernel and divisor descriptions are the same section space. -/
noncomputable def jetKernelEquiv (a : ι → K) (ha : Function.Injective a)
    (m : ι → ℕ) (N : ℕ) :
    LinearMap.ker (jetEvaluation a m N) ≃ₗ[K] sections (cellDivisor a m) N where
  toFun P := ⟨P.val.val, P.val.property,
    (cellDivisor_dvd_iff_taylor a ha m P.val.val).mpr
      ((mem_ker_jetEvaluation a m N P.val).mp P.property)⟩
  invFun P := ⟨⟨P.val, P.property.1⟩,
    (mem_ker_jetEvaluation a m N _).mpr
      ((cellDivisor_dvd_iff_taylor a ha m P.val).mp P.property.2)⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Exact finite section count, including all prescribed multiplicities. -/
theorem finrank_jetKernel (a : ι → K) (ha : Function.Injective a)
    (m : ι → ℕ) (N : ℕ) :
    Module.finrank K (LinearMap.ker (jetEvaluation a m N)) = N - ∑ i, m i := by
  rw [(jetKernelEquiv a ha m N).finrank_eq, finrank_cellSections]

theorem finrank_jetRange (a : ι → K) (ha : Function.Injective a)
    (m : ι → ℕ) (N : ℕ) :
    Module.finrank K (LinearMap.range (jetEvaluation a m N)) = min N (∑ i, m i) := by
  have h := (jetEvaluation a m N).finrank_range_add_finrank_ker
  rw [finrank_jetKernel a ha, (Polynomial.degreeLTEquiv K N).finrank_eq] at h
  simp only [Module.finrank_pi, Fintype.card_fin] at h
  omega

/-- Any prescribed jets can be interpolated once the bank has enough modes. -/
theorem jetEvaluation_surjective (a : ι → K) (ha : Function.Injective a)
    (m : ι → ℕ) (N : ℕ) (hN : ∑ i, m i ≤ N) :
    Function.Surjective (jetEvaluation a m N) := by
  apply LinearMap.range_eq_top.mp
  apply Submodule.eq_top_of_finrank_eq
  rw [finrank_jetRange a ha, min_eq_right hN, Module.finrank_pi_fintype]
  simp

/-- Below the total multiplicity no nonzero section can vanish to all the prescribed orders. -/
theorem vanishing_forces_zero (a : ι → K) (ha : Function.Injective a)
    (m : ι → ℕ) (N : ℕ) (hN : N ≤ ∑ i, m i) (P : K[X])
    (hP : P ∈ Polynomial.degreeLT K N)
    (hjets : ∀ i j, j < m i → (Polynomial.taylor (a i) P).coeff j = 0) : P = 0 := by
  by_contra hne
  have hdvd := (cellDivisor_dvd_iff_taylor a ha m P).mpr hjets
  have hdeg := Polynomial.natDegree_le_of_dvd hdvd hne
  rw [cellDivisor_natDegree] at hdeg
  have hlt := (Polynomial.natDegree_lt_iff_degree_lt hne).mpr
    (Polynomial.mem_degreeLT.mp hP)
  omega

/-- A section exists precisely when the bank has a mode beyond the full jet budget.
In the forward construction the section is the explicit product `cellDivisor a m`. -/
theorem exists_nonzero_section_iff (a : ι → K) (ha : Function.Injective a)
    (m : ι → ℕ) (N : ℕ) :
    (∃ P : K[X], P ≠ 0 ∧ P ∈ Polynomial.degreeLT K N ∧
      ∀ i j, j < m i → (Polynomial.taylor (a i) P).coeff j = 0) ↔
      ∑ i, m i < N := by
  constructor
  · rintro ⟨P, hne, hP, hjets⟩
    by_contra h
    exact hne (vanishing_forces_zero a ha m N (Nat.le_of_not_gt h) P hP hjets)
  · intro h
    refine ⟨cellDivisor a m, (cellDivisor_monic a m).ne_zero, ?_, ?_⟩
    · apply Polynomial.mem_degreeLT.mpr
      apply (Polynomial.natDegree_lt_iff_degree_lt (cellDivisor_monic a m).ne_zero).mp
      rwa [cellDivisor_natDegree]
    · exact (cellDivisor_dvd_iff_taylor a ha m _).mp (dvd_refl _)

#print axioms finrank_jetKernel
#print axioms finrank_jetRange
#print axioms jetEvaluation_surjective
#print axioms vanishing_forces_zero
#print axioms exists_nonzero_section_iff

end CriticalLinePhasor.FiniteCellSections
