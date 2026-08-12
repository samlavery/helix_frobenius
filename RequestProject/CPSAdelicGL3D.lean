import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.NumberTheory.Padics.WithVal
import Mathlib.Topology.Algebra.RestrictedProduct.TopologicalSpace

/-!
# The genuine adelic general linear group over `ℚ`

This file replaces the one-place finite model used by `CPSLatticeInstance3D` with the actual
archimedean-times-finite restricted product underlying the CPS converse theorem over `ℚ`.

At a finite prime `p`, the distinguished subgroup is the image of `GL n ℤ_[p]` inside
`GL n ℚ_[p]`.  The finite adelic group is Mathlib's restricted product with respect to these
subgroups, and the full adelic group includes the real factor `GL n ℝ`.
-/

open scoped RestrictedProduct

namespace CriticalLinePhasor.ThreeDConverse

open Matrix

/-- A prime subtype supplies the `Fact` instance required by Mathlib's `p`-adic types. -/
instance primeFact (p : Nat.Primes) : Fact p.1.Prime := ⟨p.2⟩

/-- The local general linear group over `ℚ_p`. -/
abbrev PadicGL (n : ℕ) (p : Nat.Primes) :=
  Matrix.GeneralLinearGroup (Fin n) ℚ_[p.1]

/-- The integral local general linear group over `ℤ_p`. -/
abbrev PadicIntegralGL (n : ℕ) (p : Nat.Primes) :=
  Matrix.GeneralLinearGroup (Fin n) ℤ_[p.1]

/-- The canonical inclusion `GL n ℤ_p → GL n ℚ_p`. -/
noncomputable def padicIntegralGLMap (n : ℕ) (p : Nat.Primes) :
    PadicIntegralGL n p →* PadicGL n p :=
  Matrix.GeneralLinearGroup.map (algebraMap ℤ_[p.1] ℚ_[p.1])

/-- The canonical inclusion of the integral local group is injective. -/
theorem padicIntegralGLMap_injective (n : ℕ) (p : Nat.Primes) :
    Function.Injective (padicIntegralGLMap n p) := by
  intro g h hgh
  apply Units.ext
  ext i j
  have hij := congrArg (fun u : PadicGL n p => u i j) hgh
  apply Subtype.coe_injective
  simpa [padicIntegralGLMap, PadicInt.algebraMap_apply] using hij

/-- The standard integral subgroup `GL n ℤ_p` inside `GL n ℚ_p`.

Its openness and compactness are separate topological theorems; the restricted product below only
uses the subgroup structure at this stage. -/
noncomputable def padicIntegralSubgroup (n : ℕ) (p : Nat.Primes) : Subgroup (PadicGL n p) :=
  (padicIntegralGLMap n p).range

/-- The finite adelic general linear group `GL n 𝔸_f`. -/
abbrev FiniteAdelicGL (n : ℕ) :=
  Πʳ p : Nat.Primes, [PadicGL n p, (padicIntegralSubgroup n p : Set (PadicGL n p))]

/-- The adelic general linear group `GL n 𝔸_ℚ = GL n ℝ × GL n 𝔸_f`. -/
abbrev AdelicGL (n : ℕ) := Matrix.GeneralLinearGroup (Fin n) ℝ × FiniteAdelicGL n

/-! ## Rational local embeddings -/

/-- The real component of the diagonal embedding `GL n ℚ → GL n 𝔸_ℚ`. -/
noncomputable def rationalToRealGLMap (n : ℕ) :
    Matrix.GeneralLinearGroup (Fin n) ℚ →*
      Matrix.GeneralLinearGroup (Fin n) ℝ :=
  Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ)

/-- The `p`-adic component of the diagonal embedding `GL n ℚ → GL n 𝔸_ℚ`. -/
noncomputable def rationalToPadicGLMap (n : ℕ) (p : Nat.Primes) :
    Matrix.GeneralLinearGroup (Fin n) ℚ →* PadicGL n p :=
  Matrix.GeneralLinearGroup.map (algebraMap ℚ ℚ_[p.1])

/-- The real component of the rational diagonal embedding is injective. -/
theorem rationalToRealGLMap_injective (n : ℕ) :
    Function.Injective (rationalToRealGLMap n) := by
  intro g h hgh
  apply Units.ext
  ext i j
  have hij := congrArg
    (fun u : Matrix.GeneralLinearGroup (Fin n) ℝ => u i j) hgh
  exact Rat.cast_injective hij

/-- Every `p`-adic component of the rational diagonal embedding is injective. -/
theorem rationalToPadicGLMap_injective (n : ℕ) (p : Nat.Primes) :
    Function.Injective (rationalToPadicGLMap n p) := by
  intro g h hgh
  apply Units.ext
  ext i j
  have hij := congrArg (fun u : PadicGL n p => u i j) hgh
  exact Rat.cast_injective hij

/-- Every integral local matrix lands in the distinguished restricted-product subgroup. -/
theorem padicIntegralGLMap_mem_integralSubgroup (n : ℕ) (p : Nat.Primes)
    (g : PadicIntegralGL n p) :
    padicIntegralGLMap n p g ∈ padicIntegralSubgroup n p :=
  ⟨g, rfl⟩

/-! ## The rational diagonal in the restricted product -/

/-- A rational number is a `p`-adic integer away from the finitely many prime divisors of its
denominator. -/
theorem rational_eventually_padicInt (q : ℚ) :
    ∀ᶠ p : Nat.Primes in Filter.cofinite, ‖(q : ℚ_[p.1])‖ ≤ 1 := by
  rw [Filter.eventually_cofinite]
  apply Set.Finite.of_finite_image
  · apply Set.Finite.subset (Set.finite_Iic q.den)
    rintro x ⟨p, hp, rfl⟩
    have hdiv : p.1 ∣ q.den := by
      have hp' : ¬ ‖(q : ℚ_[p.1])‖ ≤ 1 := by
        simpa only [Set.mem_setOf_eq] using hp
      rw [Padic.norm_rat_le_one_iff_padicValuation_le_one,
        Rat.padicValuation_le_one_iff] at hp'
      simpa using hp'
    exact Nat.le_of_dvd q.den_pos hdiv
  · exact (Subtype.val_injective : Function.Injective
      (fun p : Nat.Primes ↦ p.1)).injOn

/-- If a rational invertible matrix and its inverse are entrywise `p`-integral, its local image
lies in `GL n ℤ_p`. -/
theorem rationalToPadicGLMap_mem_integralSubgroup_of_entries
    (n : ℕ) (g : Matrix.GeneralLinearGroup (Fin n) ℚ) (p : Nat.Primes)
    (hg : ∀ i j, ‖(g i j : ℚ_[p.1])‖ ≤ 1)
    (hginv : ∀ i j, ‖((g⁻¹) i j : ℚ_[p.1])‖ ≤ 1) :
    rationalToPadicGLMap n p g ∈ padicIntegralSubgroup n p := by
  let A : Matrix (Fin n) (Fin n) ℤ_[p.1] := fun i j ↦
    ⟨(g i j : ℚ_[p.1]), hg i j⟩
  let B : Matrix (Fin n) (Fin n) ℤ_[p.1] := fun i j ↦
    ⟨((g⁻¹) i j : ℚ_[p.1]), hginv i j⟩
  let u : PadicIntegralGL n p :=
    { val := A
      inv := B
      val_inv := by
        let f : ℤ_[p.1] →+* ℚ_[p.1] := algebraMap ℤ_[p.1] ℚ_[p.1]
        have hf : Function.Injective f := by
          intro x y hxy
          exact PadicInt.ext hxy
        have hfm : Function.Injective
            (f.mapMatrix : Matrix (Fin n) (Fin n) ℤ_[p.1] →+*
              Matrix (Fin n) (Fin n) ℚ_[p.1]) := by
          intro X Y hXY
          ext i j
          apply hf
          exact congrFun (congrFun hXY i) j
        apply hfm
        rw [map_mul, map_one]
        have hA : f.mapMatrix A =
            (↑(rationalToPadicGLMap n p g) : Matrix (Fin n) (Fin n) ℚ_[p.1]) := by
          ext i j
          rfl
        have hB : f.mapMatrix B =
            (↑(rationalToPadicGLMap n p (g⁻¹)) : Matrix (Fin n) (Fin n) ℚ_[p.1]) := by
          ext i j
          rfl
        rw [hA, hB, map_inv]
        exact Units.val_inv _
      inv_val := by
        let f : ℤ_[p.1] →+* ℚ_[p.1] := algebraMap ℤ_[p.1] ℚ_[p.1]
        have hf : Function.Injective f := by
          intro x y hxy
          exact PadicInt.ext hxy
        have hfm : Function.Injective
            (f.mapMatrix : Matrix (Fin n) (Fin n) ℤ_[p.1] →+*
              Matrix (Fin n) (Fin n) ℚ_[p.1]) := by
          intro X Y hXY
          ext i j
          apply hf
          exact congrFun (congrFun hXY i) j
        apply hfm
        rw [map_mul, map_one]
        have hA : f.mapMatrix A =
            (↑(rationalToPadicGLMap n p g) : Matrix (Fin n) (Fin n) ℚ_[p.1]) := by
          ext i j
          rfl
        have hB : f.mapMatrix B =
            (↑(rationalToPadicGLMap n p (g⁻¹)) : Matrix (Fin n) (Fin n) ℚ_[p.1]) := by
          ext i j
          rfl
        rw [hA, hB, map_inv]
        exact Units.inv_val _ }
  refine ⟨u, ?_⟩
  apply Units.ext
  ext i j
  rfl

/-- All entries of a rational matrix are `p`-integral for all but finitely many primes. -/
theorem rationalMatrix_eventually_padicInt (n : ℕ)
    (M : Matrix (Fin n) (Fin n) ℚ) :
    ∀ᶠ p : Nat.Primes in Filter.cofinite,
      ∀ i j, ‖(M i j : ℚ_[p.1])‖ ≤ 1 := by
  rw [Filter.eventually_all]
  intro i
  rw [Filter.eventually_all]
  intro j
  exact rational_eventually_padicInt (M i j)

/-- The rational local components of an invertible matrix are integral at almost every prime. -/
theorem rationalGL_eventually_integral (n : ℕ)
    (g : Matrix.GeneralLinearGroup (Fin n) ℚ) :
    ∀ᶠ p : Nat.Primes in Filter.cofinite,
      rationalToPadicGLMap n p g ∈ padicIntegralSubgroup n p := by
  filter_upwards [rationalMatrix_eventually_padicInt n (↑g),
    rationalMatrix_eventually_padicInt n (↑(g⁻¹))] with p hp hpinv
  exact rationalToPadicGLMap_mem_integralSubgroup_of_entries n g p hp hpinv

/-- The finite component of the rational diagonal embedding. -/
noncomputable def rationalToFiniteAdelicGLMap (n : ℕ) :
    Matrix.GeneralLinearGroup (Fin n) ℚ →* FiniteAdelicGL n where
  toFun g := RestrictedProduct.mk
    (fun p ↦ rationalToPadicGLMap n p g)
    (rationalGL_eventually_integral n g)
  map_one' := by
    apply Subtype.ext
    funext p
    exact map_one (rationalToPadicGLMap n p)
  map_mul' g h := by
    apply Subtype.ext
    funext p
    exact map_mul (rationalToPadicGLMap n p) g h

/-- The genuine rational diagonal `GL n ℚ → GL n 𝔸_ℚ`. -/
noncomputable def rationalDiagonalGLMap (n : ℕ) :
    Matrix.GeneralLinearGroup (Fin n) ℚ →* AdelicGL n where
  toFun g := (rationalToRealGLMap n g, rationalToFiniteAdelicGLMap n g)
  map_one' := by simp
  map_mul' g h := by simp

/-- The rational diagonal embedding is faithful. -/
theorem rationalDiagonalGLMap_injective (n : ℕ) :
    Function.Injective (rationalDiagonalGLMap n) := by
  intro g h hgh
  apply rationalToRealGLMap_injective n
  exact congrArg Prod.fst hgh

/-- The rational points `GL n ℚ` as the diagonal subgroup of `GL n 𝔸_ℚ`. -/
noncomputable def rationalDiagonalSubgroup (n : ℕ) : Subgroup (AdelicGL n) :=
  (rationalDiagonalGLMap n).range

/-- Every rational point belongs to the rational diagonal subgroup. -/
theorem rationalDiagonalGLMap_mem (n : ℕ)
    (g : Matrix.GeneralLinearGroup (Fin n) ℚ) :
    rationalDiagonalGLMap n g ∈ rationalDiagonalSubgroup n :=
  ⟨g, rfl⟩

end CriticalLinePhasor.ThreeDConverse

#print axioms CriticalLinePhasor.ThreeDConverse.padicIntegralGLMap_mem_integralSubgroup
#print axioms CriticalLinePhasor.ThreeDConverse.padicIntegralGLMap_injective
#print axioms CriticalLinePhasor.ThreeDConverse.rationalToRealGLMap_injective
#print axioms CriticalLinePhasor.ThreeDConverse.rationalToPadicGLMap_injective
#print axioms CriticalLinePhasor.ThreeDConverse.rational_eventually_padicInt
#print axioms CriticalLinePhasor.ThreeDConverse.rationalToPadicGLMap_mem_integralSubgroup_of_entries
#print axioms CriticalLinePhasor.ThreeDConverse.rationalMatrix_eventually_padicInt
#print axioms CriticalLinePhasor.ThreeDConverse.rationalGL_eventually_integral
#print axioms CriticalLinePhasor.ThreeDConverse.rationalDiagonalGLMap_injective
#print axioms CriticalLinePhasor.ThreeDConverse.rationalDiagonalGLMap_mem
