import RequestProject.CPSFiniteFieldMellinConverse3D
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.Topology.Algebra.Group.Matrix
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup

/-!
# Local p-adic transvection descent

The rational parameters are dense in each p-adic field.  Since one-parameter transvections and the
3D readout action are continuous, invariance on all rational winding parameters extends to every
p-adic transvection parameter.
-/

namespace CriticalLinePhasor.ThreeDConverse

/-- The one-parameter transvection map into `GL(n)` is continuous over a topological field. -/
theorem continuous_transvectionGL
    {n K : Type*} [Fintype n] [DecidableEq n] [Field K]
    [TopologicalSpace K] [IsTopologicalRing K]
    (i j : n) (hij : i ≠ j) :
    Continuous (transvectionGL i j hij : K → Matrix.GeneralLinearGroup n K) := by
  have hSL : Continuous
      (fun c : K => Matrix.SpecialLinearGroup.transvection hij c) := by
    apply continuous_induced_rng.mpr
    refine continuous_matrix fun a b => ?_
    by_cases hai : a = i
    · subst a
      by_cases hbj : b = j
      · subst b
        simp [Matrix.SpecialLinearGroup.transvection_coe]
        fun_prop
      · simpa [Matrix.SpecialLinearGroup.transvection_coe, Matrix.single_apply, Ne.symm hbj]
          using (continuous_const : Continuous (fun _ : K => (1 : Matrix n n K) i b))
    · simpa [Matrix.SpecialLinearGroup.transvection_coe, Matrix.single_apply, Ne.symm hai]
        using (continuous_const : Continuous (fun _ : K => (1 : Matrix n n K) a b))
  have htoGL : Continuous
      (Matrix.SpecialLinearGroup.toGL :
        Matrix.SpecialLinearGroup n K → Matrix.GeneralLinearGroup n K) :=
    Matrix.SpecialLinearGroup.continuous_toGL
  have heq :
      (transvectionGL i j hij : K → Matrix.GeneralLinearGroup n K) =
        (fun c : K => Matrix.SpecialLinearGroup.toGL
          (Matrix.SpecialLinearGroup.transvection hij c)) := by
    funext c
    ext a b
    rfl
  exact heq.symm ▸ htoGL.comp hSL

/-- Rational-parameter invariance extends to every p-adic transvection parameter. -/
theorem padic_transvection_readout_invariant_of_rational
    {p : ℕ} [Fact p.Prime]
    {n X : Type*} [Fintype n] [DecidableEq n]
    [TopologicalSpace X]
    [MulAction (Matrix.GeneralLinearGroup n ℚ_[p]) X]
    [ContinuousSMul (Matrix.GeneralLinearGroup n ℚ_[p]) X]
    (readout : X → ℂ) (hreadout : Continuous readout)
    (i j : n) (hij : i ≠ j) (x : X)
    (hrational : ∀ q : ℚ,
      readout (transvectionGL i j hij (q : ℚ_[p]) • x) = readout x) :
    ∀ d : ℚ_[p], readout (transvectionGL i j hij d • x) = readout x := by
  let orbitReadout : ℚ_[p] → ℂ := fun d =>
    readout (transvectionGL i j hij d • x)
  have horbit : Continuous orbitReadout := by
    dsimp [orbitReadout]
    exact hreadout.comp
      (continuous_smul.comp
        ((continuous_transvectionGL i j hij).prodMk continuous_const))
  have hconstant : Continuous (fun _ : ℚ_[p] => readout x) := continuous_const
  have heq : orbitReadout = fun _ : ℚ_[p] => readout x :=
    horbit.ext_on (Padic.denseRange_ratCast p) hconstant (by
      intro d hd
      obtain ⟨q, rfl⟩ := hd
      exact hrational q)
  exact fun d => congrFun heq d

/-- **Local p-adic 3D converse.** Continuous readout invariance under diagonal clocks and all
rational-parameter transvections extends to invariance under `GL(n, ℚ_[p])`. -/
theorem cpsPadic3D_readout_invariant
    {p : ℕ} [Fact p.Prime]
    {n X : Type*} [Fintype n] [DecidableEq n]
    [TopologicalSpace X]
    [MulAction (Matrix.GeneralLinearGroup n ℚ_[p]) X]
    [ContinuousSMul (Matrix.GeneralLinearGroup n ℚ_[p]) X]
    (readout : X → ℂ) (hreadout : Continuous readout)
    (hdiag : ∀ (D : n → ℚ_[p])
        (hD : Matrix.det (Matrix.diagonal D) ≠ 0) (x : X),
      readout
          (Matrix.GeneralLinearGroup.mkOfDetNeZero (Matrix.diagonal D) hD • x) =
        readout x)
    (hrational : ∀ (i j : n) (hij : i ≠ j) (q : ℚ) (x : X),
      readout (transvectionGL i j hij (q : ℚ_[p]) • x) = readout x)
    (g : Matrix.GeneralLinearGroup n ℚ_[p]) (x : X) :
    readout (g • x) = readout x := by
  apply cps3D_readout_invariant readout hdiag
  intro t x
  rcases t with ⟨i, j, hij, d⟩
  exact padic_transvection_readout_invariant_of_rational
    readout hreadout i j hij x (hrational i j hij · x) d

end CriticalLinePhasor.ThreeDConverse

#print axioms CriticalLinePhasor.ThreeDConverse.continuous_transvectionGL
#print axioms CriticalLinePhasor.ThreeDConverse.padic_transvection_readout_invariant_of_rational
#print axioms CriticalLinePhasor.ThreeDConverse.cpsPadic3D_readout_invariant
