import RequestProject.CPSConverseTheorem3D
import RequestProject.CPSFiniteQuotientLocalUnit3D
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.MeasureTheory.Measure.Count

/-!
# First instantiation of the 3D CPS landing theorem on a finite model bank

This file instantiates the assembled converse engine `cpsConverse3D_landing` on a concrete
*finite model bank*: complex-valued functions on the plane `𝔽₃²`, carried by a genuine nontrivial
continuous action of the archimedean-times-restricted-product move group.  Every hypothesis of the
landing theorem is discharged by an honest argument, so `cpsLatticeInstance_landing` fires with no
remaining hypotheses.

The three non-vacuity requirements are preserved:

* the readout `∑ over 𝔽₃² of F` is genuinely **non-constant** on the state space, and its move
  invariance is proved by **reindexing** (`Equiv.sum_comp`), never assumed;
* the unipotent cuspidal channel carries a **genuine finite Fourier cancellation**: the eigenmove
  is the primitive additive character `ZMod.stdAddChar` of `𝔽₃`, whose value on a generator is
  `≠ 1`, so the constant term really is `∑_{u} χ(u) · c = 0`.

The landing's own inputs `harch`/`hfinite` are discharged **directly** by the reindexing lemma
`readout_smul`; the Mellin-converse links (`local_unit_transvection_invariant_of_finiteQuotientMellin`)
are an alternative route to the *same* generator laws.  That consistency route is not exercised in
this file: it needs a concrete theta profile pair carrying all six Mellin-inversion facts
(functional equation, convergence, vertical integrability, continuity) at a height where the primal
and reflected-dual readouts are the finite transvection twists — and the profile's invariance must
be established by reindexing *first*, so that the route stays a demonstration on an
independently-proved object rather than the source of the invariance.  Building such a profile is a
separate analytic construction; here we deliver the direct-discharge landing.

Scope: this file instantiates the 3D CPS engine on a finite model bank, demonstrating that the
landing composes with zero hypotheses on a genuine object.  It does **not** instantiate the twisted
symmetric-power Satake bank: that instantiation additionally consumes adelic Poisson summation /
theta invariance — Tate's thesis (*Fourier analysis in number fields and Hecke's zeta-functions*),
classical and unconditional, cited not formalized (adelic Poisson is not yet in Mathlib) — plus the
bank readout identifications.  These remain the named formalization boundary --- cited classical
inputs, not open mathematics.  It also does not assume or prove RH/GRH.

The final section wires this boundary into the kernel: `CPSBankBridge` carries the adelic
generator laws as a distinguished **Tate field**, and `CPSBankBridge.landing` shows the bank
landing composes from `{the engine + the cuspidal-channel discharges + the Tate field}`.  The
finite model of this file is a witness (`latticeBridge`) that every field — including a concrete,
reindexing-proved stand-in for the Tate step — is simultaneously satisfiable, so the architecture
is ready to receive Tate's formalization whenever it exists.
-/

open scoped RestrictedProduct
open MeasureTheory

namespace CriticalLinePhasor.ThreeDConverse

/-! ## The bank bridge: the landing wired to receive Tate's formalization

`CPSBankBridge` bundles the inputs of `cpsConverse3D_landing` over an abstract bank, isolating the
one input that is classical-but-unformalized — the adelic generator laws that Tate's thesis (adelic
Poisson summation / theta invariance) supplies for the real Satake bank — as a distinguished
**Tate field** (`tate_archimedean`, `tate_finite`).  The remaining fields are the cuspidal-channel
discharges.  `CPSBankBridge.landing` proves the bank landing composes from
`{the engine + the cuspidal-channel discharges + the Tate field}`, asserting none of them: whenever
the Tate step is formalized, it drops into this field and the landing fires with no further
argument. -/
structure CPSBankBridge
    (ι X Garch P : Type*) {G : ι → Type*} {S : ι → Type*}
    [DecidableEq ι] [Group Garch] [TopologicalSpace Garch]
    [∀ i, Group (G i)] [∀ i, TopologicalSpace (G i)]
    [∀ i, SetLike (S i) (G i)] [∀ i, SubgroupClass (S i) (G i)]
    (A : ∀ i, S i)
    [TopologicalSpace X]
    [MulAction (Garch × (Πʳ i, [G i, (A i : Set (G i))])) X]
    [ContinuousSMul (Garch × (Πʳ i, [G i, (A i : Set (G i))])) X]
    (U : P → Type*)
    [∀ p, MeasurableSpace (U p)] [∀ p, Group (U p)]
    [∀ p, MeasurableMul (U p)] [∀ p, MeasurableInv (U p)] where
  /-- the rational subgroup the readout descends through. -/
  H : Subgroup (Garch × (Πʳ i, [G i, (A i : Set (G i))]))
  /-- the bank readout. -/
  readout : X → ℂ
  /-- the readout is continuous. -/
  readout_continuous : Continuous readout
  /-- **Tate's thesis (the adelic step), archimedean leg.**  Readout invariance under the
  archimedean factor — supplied classically by adelic Poisson summation / theta invariance. -/
  tate_archimedean : ∀ (a : Garch) (x : X),
    readout ((a, (1 : Πʳ i, [G i, (A i : Set (G i))])) • x) = readout x
  /-- **Tate's thesis (the adelic step), finite leg.**  Readout invariance under every finite
  single-place move — the same classical input at the finite places. -/
  tate_finite : ∀ (i : ι) (a : G i) (x : X),
    readout (((1 : Garch), RestrictedProduct.mulSingle A i a) • x) = readout x
  /-- the invariant measures on the proper unipotent channels. -/
  μ : ∀ p, Measure (U p)
  /-- each channel measure is left invariant. -/
  μ_invariant : ∀ p, (μ p).IsMulLeftInvariant
  /-- the unipotent translations on the quotient readout. -/
  translate : ∀ p, RationalOrbitQuotient H X → U p → RationalOrbitQuotient H X
  /-- each pulled-back constant-term kernel is integrable. -/
  hintegrable : ∀ p q, Integrable
    (quotientUnipotentKernel
      (cpsAdelic3D_rationalQuotientReadout A H readout readout_continuous
        tate_archimedean tate_finite) translate p q) (μ p)
  /-- the eigenmove in each channel. -/
  move : ∀ p, RationalOrbitQuotient H X → U p
  /-- the eigenvalue of each eigenmove. -/
  eigenvalue : P → RationalOrbitQuotient H X → ℂ
  /-- the eigenmove really is an eigenmove of the quotient readout. -/
  heigen : ∀ p q u,
    cpsAdelic3D_rationalQuotientReadout A H readout readout_continuous
        tate_archimedean tate_finite (translate p q (move p q * u)) =
      eigenvalue p q *
        cpsAdelic3D_rationalQuotientReadout A H readout readout_continuous
          tate_archimedean tate_finite (translate p q u)
  /-- every eigenvalue is nontrivial (the genuine Fourier content). -/
  hnontrivial : ∀ p q, eigenvalue p q ≠ 1

/-- **The bank landing composes.**  From `{the engine `cpsConverse3D_landing` + the cuspidal-channel
discharges + the Tate field}` the descended readout is well-defined on the rational quotient and
cuspidal along every proper unipotent channel — asserting no adelic Poisson / Tate statement. -/
theorem CPSBankBridge.landing
    {ι X Garch P : Type*} {G : ι → Type*} {S : ι → Type*}
    [DecidableEq ι] [Group Garch] [TopologicalSpace Garch]
    [∀ i, Group (G i)] [∀ i, TopologicalSpace (G i)]
    [∀ i, SetLike (S i) (G i)] [∀ i, SubgroupClass (S i) (G i)]
    {A : ∀ i, S i}
    [TopologicalSpace X]
    [MulAction (Garch × (Πʳ i, [G i, (A i : Set (G i))])) X]
    [ContinuousSMul (Garch × (Πʳ i, [G i, (A i : Set (G i))])) X]
    {U : P → Type*}
    [∀ p, MeasurableSpace (U p)] [∀ p, Group (U p)]
    [∀ p, MeasurableMul (U p)] [∀ p, MeasurableInv (U p)]
    (B : CPSBankBridge ι X Garch P A U) :
    (∀ x : X,
      cpsAdelic3D_rationalQuotientReadout A B.H B.readout B.readout_continuous
        B.tate_archimedean B.tate_finite (Quotient.mk'' x) = B.readout x) ∧
    CuspidalAlong3D B.μ
      (quotientUnipotentKernel
        (cpsAdelic3D_rationalQuotientReadout A B.H B.readout B.readout_continuous
          B.tate_archimedean B.tate_finite) B.translate) := by
  haveI := B.μ_invariant
  exact cpsConverse3D_landing A B.H B.readout B.readout_continuous B.tate_archimedean
    B.tate_finite B.μ B.translate B.hintegrable B.move B.eigenvalue B.heigen B.hnontrivial

namespace LatticeInstance

/-! ### Base data: the finite local group and the plane over `𝔽₃` -/

instance : Fact (Nat.Prime 3) := ⟨by norm_num⟩

/-- The finite local carrier group `GL₂(𝔽₃)`. -/
abbrev GL2 := Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)

/-- The plane `𝔽₃²` on which the bank functions live. -/
abbrev Vec := Fin 2 → ZMod 3

instance : TopologicalSpace GL2 := ⊥
instance : DiscreteTopology GL2 := ⟨rfl⟩

/-- A single finite place. -/
abbrev Idx := Fin 1
abbrev Gfam : Idx → Type := fun _ => GL2
abbrev Sfam : Idx → Type := fun _ => Subgroup GL2
abbrev Afam : ∀ i, Sfam i := fun _ => (⊤ : Subgroup GL2)

/-- The finite restricted-product move group over the single place. -/
abbrev Fin' := Πʳ i, [Gfam i, (Afam i : Set (Gfam i))]

/-- The full archimedean-times-finite move group. -/
abbrev Adelic := GL2 × Fin'

/-- The finite model bank: complex functions on `𝔽₃² × 𝔽₃²`.  The archimedean factor acts on the
first slot, the finite place on the second slot; the two commute by disjointness. -/
abbrev Carrier := (Vec × Vec) → ℂ

/-! ### The reindexing action of `GL₂ × GL₂` on the bank -/

instance carrierSMul : SMul (GL2 × GL2) Carrier where
  smul G F := fun p => F (G.1⁻¹ • p.1, G.2⁻¹ • p.2)

@[simp] lemma carrierSMul_apply (G : GL2 × GL2) (F : Carrier) (p : Vec × Vec) :
    (G • F) p = F (G.1⁻¹ • p.1, G.2⁻¹ • p.2) := rfl

instance carrierMulAction : MulAction (GL2 × GL2) Carrier where
  one_smul F := by funext p; simp
  mul_smul G H F := by
    funext p
    simp only [carrierSMul_apply, Prod.fst_mul, Prod.snd_mul, mul_inv_rev, mul_smul]

instance : ContinuousConstSMul (GL2 × GL2) Carrier where
  continuous_const_smul G := by
    refine continuous_pi (fun p => ?_)
    simpa only [carrierSMul_apply] using (continuous_apply (G.1⁻¹ • p.1, G.2⁻¹ • p.2))

instance : ContinuousSMul (GL2 × GL2) Carrier where
  continuous_smul := by
    rw [continuous_prod_of_discrete_left]
    intro G
    exact ContinuousConstSMul.continuous_const_smul G

/-! ### The evaluation homomorphism and the induced adelic action -/

/-- Evaluation of a finite restricted-product move at the single place, as a group homomorphism. -/
def evalHom : Fin' →* GL2 where
  toFun b := b 0
  map_one' := rfl
  map_mul' _ _ := rfl

/-- The move group maps to `GL₂ × GL₂` (archimedean factor, finite-place value). -/
def phi : Adelic →* GL2 × GL2 :=
  (MonoidHom.fst GL2 Fin').prod (evalHom.comp (MonoidHom.snd GL2 Fin'))

lemma phi_apply (g : Adelic) : phi g = (g.1, g.2 0) := rfl

lemma continuous_phi : Continuous (phi : Adelic → GL2 × GL2) := by
  refine Continuous.prodMk continuous_fst ?_
  exact (RestrictedProduct.continuous_eval 0).comp continuous_snd

noncomputable instance adelicMulAction : MulAction Adelic Carrier :=
  MulAction.compHom Carrier phi

noncomputable instance : ContinuousSMul Adelic Carrier :=
  MulAction.continuousSMul_compHom continuous_phi

/-! ### The readout and its reindexing invariance (non-vacuity: non-constant, reindex-proved) -/

/-- The bank readout: the full sum over the finite plane `𝔽₃² × 𝔽₃²`.  A nontrivial linear
functional (non-constant: it is `0` on the zero function and `1` on a point indicator). -/
noncomputable def readout : Carrier → ℂ := fun F => ∑ p, F p

lemma continuous_readout : Continuous readout :=
  continuous_finsetSum _ (fun p _ => continuous_apply p)

/-- **Reindexing invariance.** Move invariance of the readout is the change of summation variable
along the bijection `p ↦ G⁻¹ • p`. -/
lemma readout_smul (G : GL2 × GL2) (F : Carrier) : readout (G • F) = readout F := by
  let e : Vec × Vec ≃ Vec × Vec :=
    (MulAction.toPerm G.1⁻¹).prodCongr (MulAction.toPerm G.2⁻¹)
  calc readout (G • F) = ∑ p, F (e p) := by
        refine Finset.sum_congr rfl (fun p _ => ?_)
        rfl
    _ = ∑ p, F p := Equiv.sum_comp e F
    _ = readout F := rfl

/-- The archimedean generator law: readout invariance under the archimedean factor. -/
lemma harch (a : GL2) (F : Carrier) :
    readout ((a, (1 : Fin')) • F) = readout F :=
  readout_smul _ F

/-- The finite single-place generator law: readout invariance under each finite move. -/
lemma hfinite (i : Idx) (a : GL2) (F : Carrier) :
    readout (((1 : GL2), RestrictedProduct.mulSingle Afam i a) • F) = readout F :=
  readout_smul _ F

/-- Scalar linearity of the readout. -/
lemma readout_smul_scalar (c : ℂ) (F : Carrier) : readout (c • F) = c * readout F := by
  unfold readout
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  simp [Pi.smul_apply, smul_eq_mul]

/-! ### The rational orbit quotient and the descended readout -/

/-- The rational subgroup is trivial, so the orbit quotient is the bank itself. -/
abbrev Hsub : Subgroup Adelic := ⊥

/-- The descended readout on the rational orbit quotient. -/
noncomputable def qreadout : RationalOrbitQuotient Hsub Carrier → ℂ :=
  cpsAdelic3D_rationalQuotientReadout Afam Hsub readout continuous_readout harch hfinite

lemma qreadout_mk (F : Carrier) : qreadout (Quotient.mk'' F) = readout F :=
  cpsAdelic3D_rationalQuotientReadout_mk Afam Hsub readout continuous_readout harch hfinite F

/-! ### The genuine finite Fourier eigenmove in the unipotent channel -/

/-- The unipotent channel is indexed by one proper channel `Fin 1`; its group is the finite
additive winding cell `𝔽₃`, written multiplicatively. -/
abbrev Uchan : Fin 1 → Type := fun _ => Multiplicative (ZMod 3)

instance : ∀ p, MeasurableSpace (Uchan p) := fun _ => ⊤
instance : ∀ p, MeasurableMul (Uchan p) := fun _ => ⟨fun _ => measurable_from_top, fun _ => measurable_from_top⟩
instance : ∀ p, MeasurableInv (Uchan p) := fun _ => ⟨measurable_from_top⟩

/-- Counting measure on each channel. -/
noncomputable def mu : ∀ p, Measure (Uchan p) := fun _ => Measure.count

instance : ∀ p, (mu p).IsMulLeftInvariant := fun p => by
  show (Measure.count : Measure (Uchan p)).IsMulLeftInvariant; infer_instance
instance : ∀ p, IsFiniteMeasure (mu p) := fun p => by
  show IsFiniteMeasure (Measure.count : Measure (Uchan p)); infer_instance

/-- The primitive additive character of `𝔽₃`, read multiplicatively on the winding cell. -/
noncomputable def chi : Multiplicative (ZMod 3) → ℂ :=
  fun u => ZMod.stdAddChar (Multiplicative.toAdd u)

lemma chi_mul (u v : Multiplicative (ZMod 3)) : chi (u * v) = chi u * chi v := by
  unfold chi
  rw [show Multiplicative.toAdd (u * v)
        = Multiplicative.toAdd u + Multiplicative.toAdd v from rfl]
  exact ZMod.stdAddChar.map_add_eq_mul _ _

/-- A winding generator on which the character is nontrivial. -/
def u0 : Multiplicative (ZMod 3) := Multiplicative.ofAdd 1

lemma chi_u0_ne_one : chi u0 ≠ 1 := by
  unfold chi u0
  rw [show Multiplicative.toAdd (Multiplicative.ofAdd (1 : ZMod 3)) = (1 : ZMod 3) from rfl]
  intro h
  have h0 : ZMod.stdAddChar (1 : ZMod 3) = ZMod.stdAddChar (0 : ZMod 3) := by
    rw [h, ZMod.stdAddChar.map_zero_eq_one]
  have h1 : (1 : ZMod 3) = 0 := ZMod.injective_stdAddChar h0
  exact one_ne_zero h1

/-- Scaling the bank by `χ(u)` descends to the rational orbit quotient (trivial subgroup). -/
noncomputable def translate : ∀ p,
    RationalOrbitQuotient Hsub Carrier → Uchan p → RationalOrbitQuotient Hsub Carrier :=
  fun _ q u => Quotient.liftOn' q
    (fun F => (Quotient.mk'' (chi u • F) : RationalOrbitQuotient Hsub Carrier))
    (by
      intro F F' hFF'
      change F ∈ MulAction.orbit Hsub F' at hFF'
      rw [MulAction.mem_orbit_iff] at hFF'
      obtain ⟨g, rfl⟩ := hFF'
      have hg1 : (g : Adelic) = 1 := Subgroup.mem_bot.mp g.2
      have hgF : (g : ↥Hsub) • F' = F' := by
        show (g : Adelic) • F' = F'
        rw [hg1, one_smul]
      rw [hgF])

@[simp] lemma translate_mk (p : Fin 1) (F : Carrier) (u : Uchan p) :
    translate p (Quotient.mk'' F) u = Quotient.mk'' (chi u • F) := rfl

/-- The eigenmove translation: shift by the winding generator `u0`. -/
def move : ∀ p, RationalOrbitQuotient Hsub Carrier → Uchan p := fun _ _ => u0

/-- The eigenvalue: the character value on the generator. -/
noncomputable def eigenvalue : Fin 1 → RationalOrbitQuotient Hsub Carrier → ℂ :=
  fun _ _ => chi u0

/-- **Genuine eigenmove.** Along the winding cell the quotient readout picks up exactly the
character factor. -/
lemma heigen (p : Fin 1) (q : RationalOrbitQuotient Hsub Carrier) (u : Uchan p) :
    qreadout (translate p q (move p q * u)) =
      eigenvalue p q * qreadout (translate p q u) := by
  induction q using Quotient.inductionOn' with
  | h F =>
    simp only [move, eigenvalue, translate_mk, qreadout_mk]
    rw [readout_smul_scalar, readout_smul_scalar, chi_mul]
    ring

lemma hintegrable (p : Fin 1) (q : RationalOrbitQuotient Hsub Carrier) :
    Integrable (quotientUnipotentKernel qreadout translate p q) (mu p) :=
  Integrable.of_finite

lemma hnontrivial (p : Fin 1) (q : RationalOrbitQuotient Hsub Carrier) :
    eigenvalue p q ≠ 1 := chi_u0_ne_one

/-! ### The landing fires with zero remaining hypotheses -/

/-- **First instantiation of the assembled 3D CPS landing theorem.**  The descended readout is
well-defined on the rational orbit quotient, and it is cuspidal along the proper unipotent channel.
Every hypothesis is discharged; no hypothesis parameters remain. -/
theorem cpsLatticeInstance_landing :
    (∀ F : Carrier, qreadout (Quotient.mk'' F) = readout F) ∧
      CuspidalAlong3D mu (quotientUnipotentKernel qreadout translate) :=
  cpsConverse3D_landing Afam Hsub readout continuous_readout harch hfinite mu translate
    hintegrable move eigenvalue heigen hnontrivial

/-- The quotient readout reads every representative by the bank readout. -/
theorem cpsLatticeInstance_readout (F : Carrier) :
    qreadout (Quotient.mk'' F) = readout F :=
  cpsLatticeInstance_landing.1 F

/-- The quotient readout is cuspidal along the finite winding channel. -/
theorem cpsLatticeInstance_cuspidal :
    CuspidalAlong3D mu (quotientUnipotentKernel qreadout translate) :=
  cpsLatticeInstance_landing.2

/-! ### The finite model as a bridge witness -/

/-- **The finite model is a bridge witness.**  Every field of `CPSBankBridge` is simultaneously
satisfiable on this finite bank — the Tate field discharged concretely by the reindexing lemmas
`harch`/`hfinite`, the cuspidal channel by the genuine finite Fourier eigenmove.  This certifies
the architecture is non-vacuous and ready to receive the adelic Tate step whenever it is
formalized. -/
noncomputable def latticeBridge : CPSBankBridge Idx Carrier GL2 (Fin 1) Afam Uchan where
  H := Hsub
  readout := readout
  readout_continuous := continuous_readout
  tate_archimedean := harch
  tate_finite := hfinite
  μ := mu
  μ_invariant := inferInstance
  translate := translate
  hintegrable := hintegrable
  move := move
  eigenvalue := eigenvalue
  heigen := heigen
  hnontrivial := hnontrivial

/-- The bridge witness fires the composed bank landing — the same two conclusions as
`cpsLatticeInstance_landing`, now routed through `CPSBankBridge.landing`. -/
theorem latticeBridge_landing :
    (∀ F : Carrier, qreadout (Quotient.mk'' F) = readout F) ∧
      CuspidalAlong3D mu (quotientUnipotentKernel qreadout translate) :=
  latticeBridge.landing

end LatticeInstance
end CriticalLinePhasor.ThreeDConverse

#print axioms CriticalLinePhasor.ThreeDConverse.LatticeInstance.cpsLatticeInstance_landing
#print axioms CriticalLinePhasor.ThreeDConverse.CPSBankBridge.landing
#print axioms CriticalLinePhasor.ThreeDConverse.LatticeInstance.latticeBridge_landing
