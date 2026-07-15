import RequestProject.BoundaryNull

/-!
# The coset tiling: translates of the modular domain assemble a translation domain

Slice three (b) of the Rankin–Selberg unfolding chain (brick (iv)).  Choosing one
representative per coset of `±⟨T⟩` in `SL(2,ℤ)` (`CosetQ`, `rep`), the union of the translated
closed fundamental domains `⋃ q, rep q • 𝒟` is a genuine measure-theoretic fundamental domain
for the translation subgroup `Γ∞ = ⟨T⟩` (`isFundamentalDomain_fdUnion`): covering comes from
moving any point into `𝒟` and reading its mover's coset, and a.e.-disjointness reduces to the
Second Fundamental Domain Lemma (`eq_one_or_neg_one_of_mem_fdo_mem_fd`) plus the null boundary
(`fd_boundary_null`), with the `±1`-kernel of the action absorbed into the coset relation.
Together with `isFundamentalDomain_strip` this puts two fundamental domains of the *same*
group on the table; integrals of `Γ∞`-invariant functions transfer between them — that
transfer is the unfolding.  No RH/GRH.
-/

open MeasureTheory Complex UpperHalfPlane ModularGroup
open scoped Real MatrixGroups Pointwise

namespace CriticalLinePhasor.Unfolding

/-- `T`-powers are `1` only at exponent zero. -/
lemma T_zpow_eq_one_iff (k : ℤ) : ModularGroup.T ^ k = 1 ↔ k = 0 := by
  constructor
  · intro h
    have hc := congrArg (fun g : SL(2, ℤ) => g.1 0 1) h
    simpa [ModularGroup.coe_T_zpow] using hc
  · rintro rfl
    simp

/-- `T`-powers are never `-1`. -/
lemma T_zpow_ne_neg_one (k : ℤ) : ModularGroup.T ^ k ≠ -1 := by
  intro h
  have hc := congrArg (fun g : SL(2, ℤ) => g.1 0 0) h
  simp [ModularGroup.coe_T_zpow] at hc

/-- The coset relation: two modular matrices lie in the same `±⟨T⟩`-coset. -/
def cosetSetoid : Setoid SL(2, ℤ) where
  r δ δ' := ∃ n : ℤ, δ' = ModularGroup.T ^ n * δ ∨ δ' = -(ModularGroup.T ^ n * δ)
  iseqv := by
    constructor
    · intro δ
      exact ⟨0, Or.inl (by rw [zpow_zero, one_mul])⟩
    · rintro δ δ' ⟨n, h | h⟩
      · exact ⟨-n, Or.inl (by rw [h, ← mul_assoc, ← zpow_add, neg_add_cancel,
          zpow_zero, one_mul])⟩
      · exact ⟨-n, Or.inr (by rw [h, mul_neg, neg_neg, ← mul_assoc, ← zpow_add,
          neg_add_cancel, zpow_zero, one_mul])⟩
    · rintro δ δ' δ'' ⟨n, h | h⟩ ⟨m, h' | h'⟩
      · exact ⟨m + n, Or.inl (by rw [h', h, ← mul_assoc, ← zpow_add])⟩
      · exact ⟨m + n, Or.inr (by rw [h', h, ← mul_assoc, ← zpow_add])⟩
      · exact ⟨m + n, Or.inr (by rw [h', h, mul_neg, ← mul_assoc, ← zpow_add])⟩
      · exact ⟨m + n, Or.inl (by rw [h', h, mul_neg, neg_neg, ← mul_assoc, ← zpow_add])⟩

/-- The coset space `±⟨T⟩ \ SL(2,ℤ)`: the index of the tiling, and later the index of the
Eisenstein sum. -/
def CosetQ : Type := Quotient cosetSetoid

instance : Countable CosetQ := by
  have h1 : Countable (Matrix (Fin 2) (Fin 2) ℤ) :=
    Countable.of_equiv (Fin 2 → Fin 2 → ℤ) Matrix.of
  have : Countable SL(2, ℤ) := Subtype.countable
  exact Quotient.countable

/-- A representative of each coset. -/
noncomputable def rep (q : CosetQ) : SL(2, ℤ) := Quotient.out q

lemma rep_spec (γ : SL(2, ℤ)) :
    ∃ n : ℤ, γ = ModularGroup.T ^ n * rep (Quotient.mk cosetSetoid γ) ∨
      γ = -(ModularGroup.T ^ n * rep (Quotient.mk cosetSetoid γ)) :=
  Quotient.exact (Quotient.out_eq (Quotient.mk cosetSetoid γ))

/-- The tiling set: one translated closed domain per coset. -/
def fdUnion : Set ℍ := ⋃ q : CosetQ, rep q • ModularGroup.fd

/-- The closed modular domain is measurable. -/
lemma measurableSet_fd : MeasurableSet ModularGroup.fd := by
  have h1 : IsClosed {z : ℍ | 1 ≤ Complex.normSq ↑z} :=
    isClosed_Ici.preimage (Complex.continuous_normSq.comp UpperHalfPlane.continuous_coe)
  have h2 : IsClosed {z : ℍ | |z.re| ≤ (1 : ℝ) / 2} :=
    isClosed_Iic.preimage (UpperHalfPlane.continuous_re.abs)
  exact (h1.inter h2).measurableSet

/-- Translates of the closed domain are measurable: the action is by homeomorphisms. -/
lemma measurableSet_smul_fd (δ : SL(2, ℤ)) : MeasurableSet (δ • ModularGroup.fd) := by
  have h : δ • ModularGroup.fd = (fun z : ℍ => δ⁻¹ • z) ⁻¹' ModularGroup.fd := by
    ext w
    rw [Set.mem_smul_set_iff_inv_smul_mem]
    rfl
  rw [h]
  have hc : Continuous (fun z : ℍ => δ⁻¹ • z) := by
    show Continuous (fun z : ℍ => (Matrix.SpecialLinearGroup.mapGL ℝ δ⁻¹) • z)
    exact continuous_const_smul _
  exact measurableSet_fd.preimage hc.measurable

/-- Hyperbolic measure is invariant under the modular action (through `GL(2,ℝ)`). -/
lemma volume_smul_eq (δ : SL(2, ℤ)) (A : Set ℍ) :
    (volume : Measure ℍ) (δ • A) = volume A := by
  show volume ((Matrix.SpecialLinearGroup.mapGL ℝ δ) • A) = volume A
  exact measure_smul (μ := (volume : Measure ℍ)) (Matrix.SpecialLinearGroup.mapGL ℝ δ) A

/-- **Distinct-coset translates of the closed domain overlap in a null set** — the Second
Fundamental Domain Lemma plus the null boundary. -/
lemma fd_smul_inter_null {δ₁ δ₂ : SL(2, ℤ)} (h1 : δ₁ ≠ δ₂) (h2 : δ₁ ≠ -δ₂) :
    (volume : Measure ℍ) ((δ₁ • ModularGroup.fd) ∩ (δ₂ • ModularGroup.fd)) = 0 := by
  have hrw : (δ₁ • ModularGroup.fd) ∩ (δ₂ • ModularGroup.fd) =
      δ₁ • (ModularGroup.fd ∩ (δ₁⁻¹ * δ₂) • ModularGroup.fd) := by
    rw [Set.smul_set_inter, smul_smul, mul_inv_cancel_left]
  rw [hrw, volume_smul_eq]
  have hα1 : δ₁⁻¹ * δ₂ ≠ 1 := by
    intro h
    exact h1 (inv_mul_eq_one.mp h)
  have hα2 : δ₁⁻¹ * δ₂ ≠ -1 := by
    intro h
    apply h2
    have h3 := congrArg (fun g : SL(2, ℤ) => δ₁ * g) h
    simp only [mul_inv_cancel_left, mul_neg_one] at h3
    rw [h3, neg_neg]
  have hsub : ModularGroup.fd ∩ (δ₁⁻¹ * δ₂) • ModularGroup.fd ⊆
      ModularGroup.fd \ ModularGroup.fdo := by
    rintro z ⟨hzfd, hzα⟩
    refine ⟨hzfd, fun hzo => ?_⟩
    have hinv : (δ₁⁻¹ * δ₂)⁻¹ • z ∈ ModularGroup.fd := by
      rwa [← Set.mem_smul_set_iff_inv_smul_mem]
    rcases ModularGroup.eq_one_or_neg_one_of_mem_fdo_mem_fd hzo hinv with h | h
    · exact hα1 (by rwa [inv_eq_one] at h)
    · apply hα2
      have hneg : ((-1 : SL(2, ℤ)))⁻¹ = -1 :=
        inv_eq_of_mul_eq_one_right (by rw [neg_mul_neg, one_mul])
      rw [← inv_inv (δ₁⁻¹ * δ₂), h, hneg]
  exact measure_mono_null hsub fd_boundary_null

/-- **The coset tiling is a fundamental domain for the translation subgroup.** -/
theorem isFundamentalDomain_fdUnion :
    IsFundamentalDomain gammaInfty fdUnion (volume : Measure ℍ) where
  nullMeasurableSet :=
    (MeasurableSet.iUnion fun q => measurableSet_smul_fd (rep q)).nullMeasurableSet
  ae_covers := by
    refine Filter.Eventually.of_forall fun z => ?_
    obtain ⟨γ, hγ⟩ := ModularGroup.exists_smul_mem_fd z
    obtain ⟨n, hn⟩ := rep_spec γ⁻¹
    refine ⟨⟨ModularGroup.T ^ (-n), Subgroup.zpow_mem_zpowers _ _⟩, ?_⟩
    show ModularGroup.T ^ (-n) • z ∈ fdUnion
    refine Set.mem_iUnion.mpr ⟨Quotient.mk cosetSetoid γ⁻¹, ?_⟩
    rw [Set.mem_smul_set_iff_inv_smul_mem, smul_smul]
    have hprod : (rep (Quotient.mk cosetSetoid γ⁻¹))⁻¹ * ModularGroup.T ^ (-n) =
        (ModularGroup.T ^ n * rep (Quotient.mk cosetSetoid γ⁻¹))⁻¹ := by
      rw [mul_inv_rev, zpow_neg]
    rcases hn with hn | hn
    · have hkey : (ModularGroup.T ^ n * rep (Quotient.mk cosetSetoid γ⁻¹))⁻¹ = γ := by
        rw [← hn, inv_inv]
      rw [hprod, hkey]
      exact hγ
    · have hstep : ModularGroup.T ^ n * rep (Quotient.mk cosetSetoid γ⁻¹) = -γ⁻¹ := by
        have h3 := congrArg Neg.neg hn
        rw [neg_neg] at h3
        exact h3.symm
      have hkey : (ModularGroup.T ^ n * rep (Quotient.mk cosetSetoid γ⁻¹))⁻¹ = -γ := by
        have hneg : ((-γ⁻¹ : SL(2, ℤ)))⁻¹ = -γ := by
          apply inv_eq_of_mul_eq_one_right
          rw [neg_mul_neg, inv_mul_cancel]
        rw [hstep, hneg]
      rw [hprod, hkey, ModularGroup.SL_neg_smul]
      exact hγ
  aedisjoint := by
    intro g g' hne
    obtain ⟨δ, hδ⟩ := g
    obtain ⟨m, rfl⟩ := hδ
    obtain ⟨δ', hδ'⟩ := g'
    obtain ⟨m', rfl⟩ := hδ'
    have hmm : m ≠ m' := by
      rintro rfl
      exact hne rfl
    show (volume : Measure ℍ)
      ((ModularGroup.T ^ m) • fdUnion ∩ (ModularGroup.T ^ m') • fdUnion) = 0
    have hexp : ∀ k : ℤ, (ModularGroup.T ^ k) • fdUnion =
        ⋃ q : CosetQ, (ModularGroup.T ^ k * rep q) • ModularGroup.fd := by
      intro k
      rw [fdUnion, Set.smul_set_iUnion]
      exact Set.iUnion_congr fun q => smul_smul _ _ _
    rw [hexp m, hexp m']
    apply measure_mono_null (t := ⋃ q : CosetQ, ⋃ q' : CosetQ,
      ((ModularGroup.T ^ m * rep q) • ModularGroup.fd ∩
        (ModularGroup.T ^ m' * rep q') • ModularGroup.fd))
    · rintro w ⟨hw1, hw2⟩
      rw [Set.mem_iUnion] at hw1 hw2
      obtain ⟨q, hq⟩ := hw1
      obtain ⟨q', hq'⟩ := hw2
      rw [Set.mem_iUnion]
      refine ⟨q, ?_⟩
      rw [Set.mem_iUnion]
      exact ⟨q', hq, hq'⟩
    · rw [measure_iUnion_null_iff]
      intro q
      rw [measure_iUnion_null_iff]
      intro q'
      apply fd_smul_inter_null
      · intro h
        have hrel : cosetSetoid.r (rep q) (rep q') := by
          refine ⟨-m' + m, Or.inl ?_⟩
          calc rep q' = ModularGroup.T ^ (-m') * (ModularGroup.T ^ m' * rep q') := by
                rw [← mul_assoc, ← zpow_add, neg_add_cancel, zpow_zero, one_mul]
            _ = ModularGroup.T ^ (-m') * (ModularGroup.T ^ m * rep q) := by rw [h]
            _ = ModularGroup.T ^ (-m' + m) * rep q := by rw [← mul_assoc, ← zpow_add]
        have hqq : q = q' := by
          have h4 : Quotient.mk cosetSetoid (rep q) = Quotient.mk cosetSetoid (rep q') :=
            Quotient.sound hrel
          rwa [rep, rep, Quotient.out_eq, Quotient.out_eq] at h4
        subst hqq
        have h5 : ModularGroup.T ^ m = ModularGroup.T ^ m' := mul_right_cancel h
        have h6 : ModularGroup.T ^ (m - m') = 1 := by
          rw [zpow_sub, h5, mul_inv_cancel]
        exact hmm (sub_eq_zero.mp ((T_zpow_eq_one_iff _).mp h6))
      · intro h
        have hstep : ModularGroup.T ^ m' * rep q' = -(ModularGroup.T ^ m * rep q) := by
          have h3 := congrArg Neg.neg h
          rw [neg_neg] at h3
          exact h3.symm
        have hrel : cosetSetoid.r (rep q) (rep q') := by
          refine ⟨-m' + m, Or.inr ?_⟩
          calc rep q' = ModularGroup.T ^ (-m') * (ModularGroup.T ^ m' * rep q') := by
                rw [← mul_assoc, ← zpow_add, neg_add_cancel, zpow_zero, one_mul]
            _ = ModularGroup.T ^ (-m') * -(ModularGroup.T ^ m * rep q) := by rw [hstep]
            _ = -(ModularGroup.T ^ (-m' + m) * rep q) := by
                rw [mul_neg, ← mul_assoc, ← zpow_add]
        have hqq : q = q' := by
          have h4 : Quotient.mk cosetSetoid (rep q) = Quotient.mk cosetSetoid (rep q') :=
            Quotient.sound hrel
          rwa [rep, rep, Quotient.out_eq, Quotient.out_eq] at h4
        subst hqq
        rw [← neg_mul] at h
        have h5 : ModularGroup.T ^ m = -(ModularGroup.T ^ m') := mul_right_cancel h
        have h6 : ModularGroup.T ^ (m - m') = -1 := by
          rw [zpow_sub, h5, neg_mul, mul_inv_cancel]
        exact T_zpow_ne_neg_one _ h6

end CriticalLinePhasor.Unfolding

#print axioms CriticalLinePhasor.Unfolding.fd_smul_inter_null
#print axioms CriticalLinePhasor.Unfolding.isFundamentalDomain_fdUnion
