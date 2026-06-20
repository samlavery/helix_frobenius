import Mathlib

/-!
# The unconditional Frobenius eigenstate (self-adjoint design)

The genuinely unconditional part of the Hilbert–Pólya picture — no GRH, no infinitude of zeros:
the self-adjoint *design* itself.

* the real-diagonal multiplication operator `diagOp d` on the ℓ²-space `ι →₀ ℂ` is symmetric, has
  real spectrum, and carries explicit eigenvectors `single i 1` with real eigenvalues `d i`;
* the one-dimensional fiber operator `vonNeumannOp γ` is symmetric with real eigenvalue `γ`;
* the spectral wave `t ↦ exp(i γ t)` is a unit-norm eigenstate of the generator `D = −i d/dt` with
  eigenvalue `γ`.

This is the operator/eigenstate **design**: it is real because the inputs (`d : ι → ℝ`, `γ : ℝ`) are
real — a symmetric operator has real eigenvalues.  It does **not** connect the design to any actual
zeros; that link is left out.  Mathlib-only; self-contained; no GRH.
-/

open Complex

namespace CriticalLinePhasor.UnconditionalFrobenius
noncomputable section

/-! ## The ℓ² inner product and the real-diagonal operator on `ι →₀ ℂ` -/

variable {ι : Type*}

/-- The standard ℓ² inner product on finitely supported functions `ι →₀ ℂ`. -/
noncomputable instance : Inner ℂ (ι →₀ ℂ) :=
  ⟨fun f g => f.sum (fun i a => (starRingEnd ℂ) a * g i)⟩

theorem inner_def (f g : ι →₀ ℂ) :
    (inner ℂ f g : ℂ) = f.sum (fun i a => (starRingEnd ℂ) a * g i) := rfl

theorem inner_eq_sum_of_subset (f g : ι →₀ ℂ) {s : Finset ι} (hs : f.support ⊆ s) :
    (inner ℂ f g : ℂ) = ∑ i ∈ s, (starRingEnd ℂ) (f i) * g i := by
  rw [inner_def, Finsupp.sum]
  apply Finset.sum_subset hs
  intro i _ hi
  have : f i = 0 := Finsupp.notMem_support_iff.mp hi
  simp [this]

theorem inner_eq_sum_union [DecidableEq ι] (f g : ι →₀ ℂ) :
    (inner ℂ f g : ℂ) = ∑ i ∈ f.support ∪ g.support, (starRingEnd ℂ) (f i) * g i :=
  inner_eq_sum_of_subset f g Finset.subset_union_left

theorem inner_conj_symm (f g : ι →₀ ℂ) :
    (starRingEnd ℂ) (inner ℂ g f) = inner ℂ f g := by
  classical
  rw [inner_eq_sum_union, inner_eq_sum_union, map_sum, Finset.union_comm g.support f.support]
  exact Finset.sum_congr rfl (fun i _ => by rw [map_mul, Complex.conj_conj, mul_comm])

theorem inner_re_nonneg (f : ι →₀ ℂ) : 0 ≤ RCLike.re (inner ℂ f f : ℂ) := by
  rw [ inner_def ];
  simp +decide [ Finsupp.sum ];
  exact Finset.sum_nonneg fun _ _ => add_nonneg ( mul_self_nonneg _ ) ( mul_self_nonneg _ )

theorem inner_definite (f : ι →₀ ℂ) (h : (inner ℂ f f : ℂ) = 0) : f = 0 := by
  have h_zero_terms : ∀ i ∈ f.support, Complex.normSq (f i) = 0 := by
    have h_zero_terms : ∑ i ∈ f.support, Complex.normSq (f i) = 0 := by
      simp_all +decide [ Complex.ext_iff, inner_def ];
      simp_all +decide [ Complex.normSq, Finsupp.sum ];
    exact fun i hi => by rw [ Finset.sum_eq_zero_iff_of_nonneg fun _ _ => Complex.normSq_nonneg _ ] at h_zero_terms; aesop;
  ext i; by_cases hi : i ∈ f.support <;> simp_all +decide ;

theorem inner_add_left (f g h : ι →₀ ℂ) :
    (inner ℂ (f + g) h : ℂ) = inner ℂ f h + inner ℂ g h := by
  rw [inner_def, inner_def, inner_def]
  exact Finsupp.sum_add_index' (fun i => by simp) (fun i b₁ b₂ => by simp [map_add, add_mul])

theorem inner_smul_left (f g : ι →₀ ℂ) (r : ℂ) :
    (inner ℂ (r • f) g : ℂ) = (starRingEnd ℂ) r * inner ℂ f g := by
  apply Eq.symm; exact (by
    have h_support : (r • f).support ⊆ f.support := Finsupp.support_smul
    have h_eq : (inner ℂ (r • f) g : ℂ) = ∑ i ∈ f.support, (starRingEnd ℂ) (r * f i) * g i := by
      convert inner_eq_sum_of_subset ( r • f ) g h_support using 1
      exact Finset.sum_congr rfl (fun i _ => by rw [Finsupp.smul_apply, smul_eq_mul])
    have h_eq' : (inner ℂ f g : ℂ) = ∑ i ∈ f.support, (starRingEnd ℂ) (f i) * g i := by
      convert inner_eq_sum_of_subset f g ( Finset.Subset.refl _ ) using 1
    simp_all +decide [ mul_assoc, Finset.mul_sum _ _ _ ]
  )

/-- The ℓ² inner product makes `ι →₀ ℂ` a normed additive group (via its core). -/
noncomputable instance instNormedAddCommGroup : NormedAddCommGroup (ι →₀ ℂ) :=
  @InnerProductSpace.Core.toNormedAddCommGroup ℂ (ι →₀ ℂ) _ _ _
    { toInner := inferInstance
      conj_inner_symm := inner_conj_symm
      re_inner_nonneg := inner_re_nonneg
      definite := inner_definite
      add_left := inner_add_left
      smul_left := inner_smul_left }

/-- `ι →₀ ℂ` is an inner product space for the standard ℓ² inner product. -/
noncomputable instance instInnerProductSpace : InnerProductSpace ℂ (ι →₀ ℂ) :=
  InnerProductSpace.ofCore _

/-- The real-diagonal multiplication operator: multiply the value at `i` by the real number `d i`. -/
noncomputable def diagOp (d : ι → ℝ) : (ι →₀ ℂ) →ₗ[ℂ] (ι →₀ ℂ) :=
  Finsupp.lsum ℂ (fun i => (d i : ℂ) • Finsupp.lsingle i)

theorem diagOp_single (d : ι → ℝ) (i : ι) (c : ℂ) :
    diagOp d (Finsupp.single i c) = Finsupp.single i ((d i : ℂ) * c) := by
  unfold diagOp;
  simp +decide [ Finsupp.lsum ]

theorem diagOp_apply (d : ι → ℝ) (f : ι →₀ ℂ) (i : ι) :
    (diagOp d f) i = (d i : ℂ) * f i := by
  unfold diagOp; simp +decide [ Finsupp.sum ] ;
  rw [ Finset.sum_eq_single i ] <;> aesop

theorem diagOp_symmetric (d : ι → ℝ) : (diagOp d).IsSymmetric := by
  intro f g
  have hsub : (diagOp d f).support ⊆ f.support := by
    intro i hi
    rw [Finsupp.mem_support_iff, diagOp_apply] at hi
    rw [Finsupp.mem_support_iff]
    intro hf; exact hi (by rw [hf, mul_zero])
  rw [inner_eq_sum_of_subset (diagOp d f) g hsub,
      inner_eq_sum_of_subset f (diagOp d g) (Finset.Subset.refl _)]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [diagOp_apply, diagOp_apply, map_mul, Complex.conj_ofReal]
  ring

theorem diagOp_hasEigenvalue (d : ι → ℝ) (i : ι) :
    Module.End.HasEigenvalue (diagOp d) ((d i : ℂ)) := by
  refine' fun h => _;
  simp_all +decide [ Submodule.eq_bot_iff ];
  specialize h ( Finsupp.single i 1 ) ; simp_all +decide [ diagOp ]

/-! ## Von Neumann reality and the one-dimensional fiber operator -/

/-- Von Neumann reality: an eigenvalue of a symmetric complex operator is real. -/
theorem symmetric_eigenvalue_real {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {T : E →ₗ[ℂ] E} (hT : T.IsSymmetric) {mu : ℂ} (hmu : Module.End.HasEigenvalue T mu) :
    mu.im = 0 := by
  have h := hT.conj_eigenvalue_eq_self hmu
  rwa [Complex.conj_eq_iff_im] at h

/-- The von Neumann / Hilbert operator `H_γ z = γ · z` on the one-dimensional fiber `ℂ`. -/
noncomputable def vonNeumannOp (γ : ℝ) : Module.End ℂ ℂ := (γ : ℂ) • LinearMap.id

theorem vonNeumannOp_apply (γ : ℝ) (z : ℂ) : vonNeumannOp γ z = (γ : ℂ) * z := by
  simp [vonNeumannOp]

theorem vonNeumannOp_isSymmetric (γ : ℝ) : (vonNeumannOp γ).IsSymmetric := by
  intro x y; simp [vonNeumannOp_apply, inner];
  ring

theorem vonNeumannOp_hasEigenvalue (γ : ℝ) :
    Module.End.HasEigenvalue (vonNeumannOp γ) (γ : ℂ) := by
  simp [vonNeumannOp]
  rw [Module.End.HasUnifEigenvalue]
  simp +decide [Submodule.ne_bot_iff]
  exact ⟨1, one_ne_zero⟩

/-! ## The spectral-wave Frobenius eigenstate -/

/-- The spectral wave (phasor) at height `γ`: `t ↦ exp(i γ t)`. -/
noncomputable def spectralWave (γ : ℝ) : ℝ → ℂ :=
  fun t => Complex.exp ((γ : ℂ) * (t : ℂ) * Complex.I)

theorem spectralWave_hasDerivAt (γ : ℝ) (t : ℝ) :
    HasDerivAt (spectralWave γ) ((γ : ℂ) * Complex.I * spectralWave γ t) t := by
      convert HasDerivAt.comp t ( Complex.hasDerivAt_exp _ ) ( HasDerivAt.const_mul ( γ * Complex.I ) ( hasDerivAt_id t |> HasDerivAt.ofReal_comp ) ) using 1 <;> try rfl
      · funext x
        unfold spectralWave
        simp only [Function.comp, id_eq]
        ring_nf
      · unfold spectralWave
        simp only [id_eq]
        push_cast
        ring

theorem spectralWave_eigen (γ : ℝ) (t : ℝ) :
    -Complex.I * deriv (spectralWave γ) t = (γ : ℂ) * spectralWave γ t := by
      convert congr_arg ( fun x : ℂ => -Complex.I * x ) ( HasDerivAt.deriv ( spectralWave_hasDerivAt γ t ) ) using 1 ; ring!;
      norm_num

theorem spectralWave_norm (γ : ℝ) (t : ℝ) : ‖spectralWave γ t‖ = 1 := by
  unfold spectralWave; norm_num [ Complex.norm_exp ] ;

/-- The spectral wave is a unit-norm eigenstate of `D = −i d/dt` with real eigenvalue `γ`, and
`vonNeumannOp γ` is symmetric with eigenvalue `γ`. -/
theorem frobeniusEigenstate_realization (γ : ℝ) :
    (∀ t : ℝ, ‖spectralWave γ t‖ = 1)
      ∧ (∀ t : ℝ, -Complex.I * deriv (spectralWave γ) t = (γ : ℂ) * spectralWave γ t)
      ∧ (vonNeumannOp γ).IsSymmetric
      ∧ Module.End.HasEigenvalue (vonNeumannOp γ) (γ : ℂ) := by
  refine ⟨spectralWave_norm γ, spectralWave_eigen γ,
    vonNeumannOp_isSymmetric γ, vonNeumannOp_hasEigenvalue γ⟩

/-! ## The unconditional Frobenius eigenstate -/

/-- For each `i`, `single i 1` is a nonzero eigenvector of `diagOp d` with real eigenvalue `d i`. -/
theorem diagOp_eigenvector (d : ι → ℝ) (i : ι) :
    Finsupp.single i (1 : ℂ) ≠ 0 ∧
      diagOp d (Finsupp.single i (1 : ℂ)) = (d i : ℂ) • Finsupp.single i (1 : ℂ) := by
  refine ⟨Finsupp.single_ne_zero.mpr one_ne_zero, ?_⟩
  rw [diagOp_single]
  simp [Finsupp.smul_single]

/-- Every eigenvalue of `diagOp d` is real (von Neumann reality). -/
theorem diagOp_spectrum_real (d : ι → ℝ) {μ : ℂ}
    (hμ : Module.End.HasEigenvalue (diagOp d) μ) : μ.im = 0 :=
  symmetric_eigenvalue_real (diagOp_symmetric d) hμ

/-- The real-diagonal design is real and self-adjoint, with explicit Frobenius eigenstates. -/
theorem hilbertPolya_design_real_selfAdjoint (d : ι → ℝ) :
    (diagOp d).IsSymmetric
      ∧ (∀ μ : ℂ, Module.End.HasEigenvalue (diagOp d) μ → μ.im = 0)
      ∧ (∀ i : ι,
          Finsupp.single i (1 : ℂ) ≠ 0
            ∧ diagOp d (Finsupp.single i (1 : ℂ)) = (d i : ℂ) • Finsupp.single i (1 : ℂ)
            ∧ Module.End.HasEigenvalue (diagOp d) (d i : ℂ)
            ∧ ((d i : ℂ)).im = 0) := by
  refine ⟨diagOp_symmetric d, fun μ hμ => diagOp_spectrum_real d hμ, fun i => ?_⟩
  obtain ⟨hne, hact⟩ := diagOp_eigenvector d i
  exact ⟨hne, hact, diagOp_hasEigenvalue d i, by simp⟩

/-- The spectral-wave Frobenius eigenstate for every real height `γ`. -/
theorem frobenius_spectralWave_eigenstate (γ : ℝ) :
    (∀ t : ℝ, ‖spectralWave γ t‖ = 1)
      ∧ (∀ t : ℝ, -Complex.I * deriv (spectralWave γ) t
            = (γ : ℂ) * spectralWave γ t)
      ∧ (vonNeumannOp γ).IsSymmetric
      ∧ Module.End.HasEigenvalue (vonNeumannOp γ) (γ : ℂ) :=
  frobeniusEigenstate_realization γ

/-- Every eigenvalue of `vonNeumannOp γ` is real. -/
theorem vonNeumannOp_spectrum_real (γ : ℝ) {μ : ℂ}
    (hμ : Module.End.HasEigenvalue (vonNeumannOp γ) μ) : μ.im = 0 :=
  symmetric_eigenvalue_real (vonNeumannOp_isSymmetric γ) hμ

/-- The unconditional Frobenius eigenstate, assembled. -/
theorem unconditional_frobenius_eigenstate (γ : ℝ) :
    (vonNeumannOp γ).IsSymmetric
      ∧ (∀ μ : ℂ, Module.End.HasEigenvalue (vonNeumannOp γ) μ → μ.im = 0)
      ∧ Module.End.HasEigenvalue (vonNeumannOp γ) (γ : ℂ)
      ∧ (∀ t : ℝ, ‖spectralWave γ t‖ = 1)
      ∧ (∀ t : ℝ, -Complex.I * deriv (spectralWave γ) t
            = (γ : ℂ) * spectralWave γ t) := by
  obtain ⟨hnorm, heig, hsym, hev⟩ := frobenius_spectralWave_eigenstate γ
  exact ⟨hsym, fun μ hμ => vonNeumannOp_spectrum_real γ hμ, hev, hnorm, heig⟩

end
end CriticalLinePhasor.UnconditionalFrobenius
