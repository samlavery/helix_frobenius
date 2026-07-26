import Mathlib.LinearAlgebra.TensorPower.Symmetric
import Mathlib.RepresentationTheory.Basic

/-!
# Symmetric powers of linear representations

Mathlib defines the symmetric tensor quotient but does not yet provide its functorial map.  This
file constructs that map, proves identity and composition, and therefore constructs the genuine
`r`th symmetric-power representation from any base linear representation.
-/

open scoped TensorProduct

universe u v w

namespace SymmetricPower

open TensorProduct

variable {R ι : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M]

private lemma map_rel (f : M →ₗ[R] M) (x y : ⨂[R] (_ : ι), M)
    (h : addConGen (Rel R ι M) x y) :
    addConGen (Rel R ι M)
      (PiTensorProduct.map (fun _ ↦ f) x)
      (PiTensorProduct.map (fun _ ↦ f) y) := by
  induction h with
  | of x y h =>
      cases h with
      | perm e g =>
          simp only [PiTensorProduct.map_tprod]
          exact AddConGen.Rel.of _ _ (Rel.perm e (fun i ↦ f (g i)))
  | refl => exact AddCon.refl _ _
  | symm _ ih =>
      apply AddCon.symm
      exact ih
  | trans _ _ ih₁ ih₂ =>
      apply AddCon.trans
      · exact ih₁
      · exact ih₂
  | add _ _ ih₁ ih₂ =>
      simpa only [LinearMap.map_add] using
        (AddCon.add (addConGen (Rel R ι M)) ih₁ ih₂)

/-- A linear endomorphism acts functorially on the symmetric tensor power. -/
noncomputable def map (f : M →ₗ[R] M) : Sym[R] ι M →ₗ[R] Sym[R] ι M where
  toFun := AddCon.lift _
    (AddMonoidHom.comp (AddCon.mk' _)
      (PiTensorProduct.map (fun _ ↦ f)).toAddMonoidHom)
    (fun x y h ↦ Quotient.sound (map_rel f x y h))
  map_add' := map_add _
  map_smul' r x := by
    induction x using AddCon.induction_on with
    | _ x =>
      change
        mk R ι M (PiTensorProduct.map (fun _ ↦ f) (r • x)) =
          r • mk R ι M (PiTensorProduct.map (fun _ ↦ f) x)
      rw [map_smul]
      exact (mk R ι M).map_smul r _

@[simp] theorem map_mk (f : M →ₗ[R] M) (x : ⨂[R] (_ : ι), M) :
    map f (mk R ι M x) = mk R ι M (PiTensorProduct.map (fun _ ↦ f) x) := rfl

@[simp] theorem map_tprod (f : M →ₗ[R] M) (x : ι → M) :
    map f (⨂ₛ[R] i, x i) = ⨂ₛ[R] i, f (x i) := by
  rw [tprod, LinearMap.compMultilinearMap_apply, map_mk, PiTensorProduct.map_tprod]
  rfl

theorem map_id :
    map (R := R) (M := M) (ι := ι) (LinearMap.id (R := R) (M := M)) = LinearMap.id := by
  apply LinearMap.ext
  intro x
  induction x using AddCon.induction_on with
  | _ x =>
    change map (R := R) (M := M) (ι := ι) LinearMap.id (mk R ι M x) = mk R ι M x
    rw [map_mk, PiTensorProduct.map_id, LinearMap.id_apply]

theorem map_comp (f g : M →ₗ[R] M) :
    map (R := R) (M := M) (ι := ι) (f.comp g) =
      (map (R := R) (M := M) (ι := ι) f).comp (map (R := R) (M := M) (ι := ι) g) := by
  apply LinearMap.ext
  intro x
  induction x using AddCon.induction_on with
  | _ x =>
    change map (R := R) (M := M) (ι := ι) (f.comp g) (mk R ι M x) =
      map (R := R) (M := M) (ι := ι) f
        (map (R := R) (M := M) (ι := ι) g (mk R ι M x))
    simp only [map_mk]
    rw [PiTensorProduct.map_comp]
    rfl

/-- Functoriality as a monoid homomorphism on endomorphism monoids. -/
noncomputable def mapMonoidHom :
    Module.End R M →* Module.End R (Sym[R] ι M) where
  toFun := map
  map_one' := by
    change map (R := R) (M := M) (ι := ι) LinearMap.id = LinearMap.id
    exact map_id (R := R) (M := M) (ι := ι)
  map_mul' f g := by
    change map (R := R) (M := M) (ι := ι) (f.comp g) =
      (map (R := R) (M := M) (ι := ι) f).comp (map (R := R) (M := M) (ι := ι) g)
    exact map_comp (R := R) (M := M) (ι := ι) f g

end SymmetricPower

namespace Representation

open scoped TensorProduct

variable {R : Type u} {G : Type v} {M : Type w}
  [CommRing R] [Monoid G] [AddCommGroup M] [Module R M]

/-- The multiplicative action carried by a representation itself.  This lets constructions use
the representation action definitionally, without asking for a second external `MulAction`. -/
@[reducible] def mulAction (rho : Representation R G M) : MulAction G M where
  smul g x := rho g x
  one_smul x := by
    change rho 1 x = x
    rw [map_one]
    rfl
  mul_smul g h x := by
    change rho (g * h) x = rho g (rho h x)
    rw [map_mul]
    rfl

@[simp] theorem mulAction_smul (rho : Representation R G M) (g : G) (x : M) :
    @SMul.smul G M rho.mulAction.toSMul g x = rho g x := rfl

/-- The genuine symmetric-power representation induced from a base representation. -/
noncomputable def symmetricPower (ι : Type u) (rho : Representation R G M) :
    Representation R G (Sym[R] ι M) :=
  (SymmetricPower.mapMonoidHom (R := R) (M := M) (ι := ι)).comp rho

@[simp] theorem symmetricPower_apply (ι : Type u) (rho : Representation R G M)
    (g : G) (x : Sym[R] ι M) :
    symmetricPower ι rho g x = SymmetricPower.map (rho g) x := rfl

end Representation

#print axioms SymmetricPower.map_mk
#print axioms SymmetricPower.map_tprod
#print axioms SymmetricPower.map_id
#print axioms SymmetricPower.map_comp
#print axioms Representation.mulAction_smul
#print axioms Representation.symmetricPower
#print axioms Representation.symmetricPower_apply
