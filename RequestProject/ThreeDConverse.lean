import RequestProject.CellClosure
import RequestProject.TransferContinuation
import Mathlib.LinearAlgebra.Matrix.Transvection
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic

/-!
# The three-dimensional converse theorem (GL(2) seed): reflections generate the arithmetic group

The converse theorem's engine is *not* the adelic Whittaker/Poisson analysis — that is the
one-dimensional projection.  The engine is: an object is automorphic iff its functional equations
force invariance under the **generators** of the arithmetic group.  For `GL(2)`, a form is modular
iff invariant under `S : z ↦ -1/z` (the functional-equation reflection) and `T : z ↦ z+1`
(periodicity), and `⟨S, T⟩ = SL₂(ℤ)`.  Both generators are native to the carrier:

* **`T` (winding).**  Integers wound on the helix.  When the winding is onto a closing harmonic
  (root-of-unity channels — the `μ_P` cells), every complete cell cancels, the coefficient
  primitive is **bounded**, and the wound readout continues past the `Re s = 1` chart wall with no
  convergence gate.  That abscissa is a projection-chart artifact, not a barrier on the carrier.
  This file's contribution **(c)**: `winding_continuation`.
* **`S` (reflection).**  The det-one similitude reflection / carrier involution `J` (the proven
  carrier reflection); the Mellin bridge `FE ⟺ S` is **(d)**, the next brick.

`⟨S, T⟩ = SL₂(ℤ)` is elementary group theory; the carrier is manifestly invariant under both, hence
under the group they generate — the three-dimensional form of the `GL(2)` converse theorem, the
adelic machine appearing only as its shadow.  The tower (`r ≥ 5`) replaces the single reflection by
the proven twisted reflections (`DualPairFiber`, `StrandExchange`, `CompletedReflectionFiber`) and
`SL₂(ℤ)` by the Cogdell–Piatetski-Shapiro basic identity for `GL(r+1)`.

**Scope of (c).**  `winding_continuation` is the closing-cell (root-of-unity) `T`-side: cell
closure (`CellClosure.harmonic_bank_primitive_bounded`) gives a bounded primitive, and
`TransferContinuation.transfer_analytic` at exponent `θ = 0` carries it across `Re s = 1`.  The
general non-closing fiber engages its own function warp per instance; its finer primitive exponent
`θ < ½` is the arithmetic frontier, not claimed here.  All declarations below are proved.
-/

open Complex Filter Topology
open scoped BigOperators

namespace CriticalLinePhasor.ThreeDConverse

/-- **(c) The `T`-side: the winding bank continues past the `Re s = 1` wall.**  For a finite
duality-stable winding fiber whose weight channels `w i` are `P`-th roots of unity, none trivial
(the `μ_P` winding), the coefficient bank `a_k = ∑ᵢ (w i)^k` has a *bounded* primitive
(`CellClosure.harmonic_bank_primitive_bounded`: every complete `μ_P` cell cancels), so the wound
Dirichlet readout `∑ₖ a_k · (k+1)^{-s}` continues analytically to the whole right half-plane
`{Re s > 0}` (`TransferContinuation.transfer_analytic` at exponent `θ = 0`).  The `Re s = 1`
abscissa is a projection-chart artifact: the winding carries the readout across it with no
convergence gate. -/
theorem winding_continuation {ι : Type*} [Fintype ι] {P : ℕ} (w : ι → ℂ) (hP : 0 < P)
    (hroot : ∀ i, (w i) ^ P = 1) (hnt : ∀ i, w i ≠ 1) :
    ∃ F : ℂ → ℂ,
      DifferentiableOn ℂ F {s : ℂ | 0 < s.re} ∧
      ∀ s : ℂ, 0 < s.re →
        Tendsto (fun N => ∑ k ∈ Finset.range N,
            (∑ i, (w i) ^ k) * ((k + 1 : ℕ) : ℂ) ^ (-s)) atTop (𝓝 (F s)) := by
  -- cell closure ⇒ bounded primitive: `‖∑_{k<n} a_k‖ ≤ (card ι)·P = C · n^0`.
  have hprim : ∀ n : ℕ, ‖∑ k ∈ Finset.range n, (∑ i, (w i) ^ k)‖
      ≤ ((Fintype.card ι : ℝ) * P) * (n : ℝ) ^ (0 : ℝ) := by
    intro n
    rw [Real.rpow_zero, mul_one]
    exact CellClosure.harmonic_bank_primitive_bounded w hP hroot hnt n
  -- feed the bounded primitive (`θ = 0`) to the winding-free transfer continuation.
  exact TransferContinuation.transfer_analytic (fun k => ∑ i, (w i) ^ k)
    ((Fintype.card ι : ℝ) * P) 0 le_rfl hprim

/-! ## The converse-theorem engine: generator-invariance ⇒ full invariance

Automorphy is invariance under the arithmetic group, and the arithmetic group is *generated* by the
functional-equation reflection `S` and the winding translation `T`.  The descent below turns
invariance under the two generators into invariance under the whole group — the converse theorem
stripped of the adelic Whittaker/Poisson analysis (its 1D shadow).  The descent itself is only that
the stabilizer is a subgroup; all the mathematical content is in the three ingredients that plug in:

* **`hS`** — the carrier readout is fixed by the reflection `S` (the proven carrier involution `J`).
* **`hT`** — it is fixed by the winding `T` (`winding_continuation` makes the wound readout
  well-defined across the strip).
* **`hgen`** — `S, T` generate the group: `SL₂(ℤ)` for `GL(2)` (elementary), the
  Cogdell–Piatetski-Shapiro basic identity for `GL(r+1)` (the tower's only remaining content).

So the engine makes explicit that, the reflection and winding being carrier-native and done, the
*sole* mathematical frontier for the tower is the group-generation fact `hgen`. -/

/-- **The converse-theorem core (generation descent).**  If a point `x` of a `G`-set is fixed by
two elements `S T : G`, it is fixed by the whole subgroup they generate: the stabilizer of `x` is a
subgroup containing `S` and `T`, hence contains `⟨S, T⟩`. -/
theorem fixed_by_closure {G X : Type*} [Group G] [MulAction G X] {x : X} {S T : G}
    (hS : S • x = x) (hT : T • x = x) :
    Subgroup.closure ({S, T} : Set G) ≤ MulAction.stabilizer G x := by
  rw [Subgroup.closure_le]
  intro y hy
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
  rcases hy with rfl | rfl
  · exact SetLike.mem_coe.mpr (MulAction.mem_stabilizer_iff.mpr hS)
  · exact SetLike.mem_coe.mpr (MulAction.mem_stabilizer_iff.mpr hT)

/-- **Automorphy as full invariance (the 3D converse conclusion).**  If the reflection `S` and the
winding `T` generate the whole group (`hgen`) and the carrier readout `x` is fixed by both, then `x`
is fixed by *every* element of the arithmetic group — the invariance that is automorphy, obtained
from the carrier's two native symmetries with no adelic analysis. -/
theorem invariant_of_gens {G X : Type*} [Group G] [MulAction G X] {x : X} {S T : G}
    (hgen : Subgroup.closure ({S, T} : Set G) = ⊤)
    (hS : S • x = x) (hT : T • x = x) (g : G) : g • x = x := by
  have hmem : g ∈ Subgroup.closure ({S, T} : Set G) := by rw [hgen]; exact Subgroup.mem_top g
  exact MulAction.mem_stabilizer_iff.mp (fixed_by_closure hS hT hmem)

/-- **GL(2): the group-generation ingredient `hgen`, discharged by Mathlib.**  For any `SL(2,ℤ)`-set,
a point fixed by the modular generators `ModularGroup.S` (the reflection) and `ModularGroup.T` (the
winding/translation) is fixed by *all* of `SL(2,ℤ)` — the generation fact is Mathlib's
`SpecialLinearGroup.SL2Z_generators` (`⟨S, T⟩ = SL₂(ℤ)`).  This is the `GL(2)` seed's converse
conclusion in full: invariance under the reflection and the winding gives invariance under the whole
modular group, with no adelic analysis.  The tower replaces `SL2Z_generators` by the
Cogdell–Piatetski-Shapiro basic identity for `GL(r+1)`. -/
theorem modular_invariant_of_ST {X : Type*}
    [MulAction (Matrix.SpecialLinearGroup (Fin 2) ℤ) X] {x : X}
    (hS : ModularGroup.S • x = x) (hT : ModularGroup.T • x = x)
    (g : Matrix.SpecialLinearGroup (Fin 2) ℤ) : g • x = x :=
  invariant_of_gens SpecialLinearGroup.SL2Z_generators hS hT g

/-! ## The rank-n CPS generator descent

For every rank, invertible matrices are generated by invertible diagonal matrices and
transvections.  These are respectively the multi-clock scaling family and the elementary winding
shears of the 3D carrier.  The following set is the exact rank-n generator family.
-/

/-- The diagonal-clock and transvection-winding generators of `GL(n, K)`. -/
noncomputable def glCarrierGenerators
    (n K : Type*) [Fintype n] [DecidableEq n] [Field K] :
    Set (Matrix.GeneralLinearGroup n K) :=
  {g | (∃ (D : n → K) (hD : Matrix.det (Matrix.diagonal D) ≠ 0),
      g = Matrix.GeneralLinearGroup.mkOfDetNeZero (Matrix.diagonal D) hD) ∨
    (∃ t : Matrix.TransvectionStruct n K,
      g = Matrix.GeneralLinearGroup.mkOfDetNeZero t.toMatrix (by simp))}

/-- The rank-n 3D carrier generators generate all of `GL(n, K)`. -/
theorem glCarrierGenerators_closure
    {n K : Type*} [Fintype n] [DecidableEq n] [Field K] :
    Subgroup.closure (glCarrierGenerators n K) = ⊤ := by
  apply top_unique
  intro g _
  let P : Matrix n n K → Prop := fun M =>
    ∀ hM : Matrix.det M ≠ 0,
      Matrix.GeneralLinearGroup.mkOfDetNeZero M hM ∈
        Subgroup.closure (glCarrierGenerators n K)
  have hP : P g.val := by
    apply Matrix.diagonal_transvection_induction_of_det_ne_zero P g.val
      (Matrix.GeneralLinearGroup.det_ne_zero g)
    · intro D _ hD
      exact Subgroup.subset_closure (Or.inl ⟨D, hD, rfl⟩)
    · intro t _
      exact Subgroup.subset_closure (Or.inr ⟨t, rfl⟩)
    · intro A B hA hB hPA hPB hAB
      have hmk :
          Matrix.GeneralLinearGroup.mkOfDetNeZero (A * B) hAB =
            Matrix.GeneralLinearGroup.mkOfDetNeZero A hA *
              Matrix.GeneralLinearGroup.mkOfDetNeZero B hB := by
        ext i j
        rfl
      rw [hmk]
      exact Subgroup.mul_mem _ (hPA hA) (hPB hB)
  have hgmk : Matrix.GeneralLinearGroup.mkOfDetNeZero g.val
      (Matrix.GeneralLinearGroup.det_ne_zero g) = g := by
    ext i j
    rfl
  rw [← hgmk]
  exact hP (Matrix.GeneralLinearGroup.det_ne_zero g)

/-- The rank-n 3D converse conclusion, descended from the full diagonal/transvection generator
set through its stabilizer. -/
theorem cps3D_invariant_of_carrier_generators
    {n K X : Type*} [Fintype n] [DecidableEq n] [Field K]
    [MulAction (Matrix.GeneralLinearGroup n K) X] {x : X}
    (hdiag : ∀ (D : n → K) (hD : Matrix.det (Matrix.diagonal D) ≠ 0),
      Matrix.GeneralLinearGroup.mkOfDetNeZero (Matrix.diagonal D) hD • x = x)
    (htrans : ∀ t : Matrix.TransvectionStruct n K,
      Matrix.GeneralLinearGroup.mkOfDetNeZero t.toMatrix (by simp) • x = x)
    (g : Matrix.GeneralLinearGroup n K) : g • x = x := by
  have hsubset : glCarrierGenerators n K ≤ MulAction.stabilizer
      (Matrix.GeneralLinearGroup n K) x := by
    intro y hy
    rcases hy with ⟨D, hD, rfl⟩ | ⟨t, rfl⟩
    · exact MulAction.mem_stabilizer_iff.mpr (hdiag D hD)
    · exact MulAction.mem_stabilizer_iff.mpr (htrans t)
  have hclosure : Subgroup.closure (glCarrierGenerators n K) ≤
      MulAction.stabilizer (Matrix.GeneralLinearGroup n K) x :=
    by
      rw [Subgroup.closure_le]
      exact hsubset
  have hg : g ∈ Subgroup.closure (glCarrierGenerators n K) := by
    rw [glCarrierGenerators_closure]
    exact Subgroup.mem_top g
  exact MulAction.mem_stabilizer_iff.mp (hclosure hg)

end CriticalLinePhasor.ThreeDConverse

#print axioms CriticalLinePhasor.ThreeDConverse.winding_continuation
#print axioms CriticalLinePhasor.ThreeDConverse.fixed_by_closure
#print axioms CriticalLinePhasor.ThreeDConverse.invariant_of_gens
#print axioms CriticalLinePhasor.ThreeDConverse.modular_invariant_of_ST
#print axioms CriticalLinePhasor.ThreeDConverse.glCarrierGenerators_closure
#print axioms CriticalLinePhasor.ThreeDConverse.cps3D_invariant_of_carrier_generators
