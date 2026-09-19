import Mathlib

/-!
# The log-weight operator of the carrier model

This file formalises the operator `H` of the paper *A carrier readout for the zeros of ζ*
(§1, §13.2): the *log-weight operator*, which multiplies the `n`-th phasor of the fiber by
`log` of the `n`-th carrier site, together with its carrier-scaled form
`H_Δ = H + log Δ · I`.

The natural home for these operators is the Hilbert space of square-summable phasor
sequences `ℓ²(ℕ, ℂ)`.  Since the weights `log (Δ n)` are unbounded, `H` cannot be a
continuous operator; it is realised here as an unbounded operator (`LinearPMap`) on its
maximal domain.

## Main results

* `CarrierReadout.weightMul_isSelfAdjoint` : the multiplication operator by a real weight
  on its maximal domain is self-adjoint (`IsSelfAdjoint`, i.e. `T† = T`).
* `CarrierReadout.logWeight_isSelfAdjoint`, `CarrierReadout.carrierLogWeight_isSelfAdjoint` :
  the log-weight operator `H` and its carrier-scaled form `H_Δ` are self-adjoint.
* `CarrierReadout.phasor_total` : the phasor family `(e n)` is total — it is orthonormal and
  its span is dense — and each `e n` is an eigenvector of `H` with eigenvalue `log (n+1)`.
* `CarrierReadout.carrierLogWeight_eq_shift` : `H_Δ = H + log Δ · I` (equal domains, and the
  values differ by the constant shift), the whole effect of the carrier scale.
* `CarrierReadout.logWeight_not_bounded` : `H` is genuinely unbounded, which is why the
  unbounded-operator framework is the right one.
-/

open scoped BigOperators ComplexConjugate LinearPMap

noncomputable section

namespace CarrierReadout

/-- The Hilbert space of square-summable phasor sequences.  The index `n : ℕ` stands for the
carrier site number `n + 1`, so that the sites are `x_{n+1} = Δ (n+1)`. -/
abbrev L2 : Type := lp (fun _ : ℕ => ℂ) 2

/-- The maximal domain of the multiplication operator with real weight `w`: the phasor
sequences `v` for which the weighted sequence `w · v` is again square-summable. -/
def weightDomain (w : ℕ → ℝ) : Submodule ℂ L2 where
  carrier := {v : L2 | Memℓp (fun n => (w n : ℂ) * v n) 2}
  zero_mem' := by
    have : (fun n => (w n : ℂ) * (0 : L2) n) = fun _ => (0 : ℂ) := by
      funext n; simp
    rw [Set.mem_ofPred_eq, this]
    exact zero_memℓp
  add_mem' := by
    intro u v hu hv
    have : (fun n => (w n : ℂ) * (u + v) n)
        = (fun n => (w n : ℂ) * u n) + (fun n => (w n : ℂ) * v n) := by
      funext n; simp [mul_add]
    rw [Set.mem_ofPred_eq, this]
    exact Memℓp.add hu hv
  smul_mem' := by
    intro c v hv
    have : (fun n => (w n : ℂ) * (c • v) n) = c • (fun n => (w n : ℂ) * v n) := by
      funext n; simp [Pi.smul_apply, smul_eq_mul]; ring
    rw [Set.mem_ofPred_eq, this]
    exact Memℓp.const_smul hv c

theorem mem_weightDomain_iff (w : ℕ → ℝ) (v : L2) :
    v ∈ weightDomain w ↔ Memℓp (fun n => (w n : ℂ) * v n) 2 := Iff.rfl

/-- The multiplication operator by a real weight `w`, on its maximal domain: an unbounded
operator on `ℓ²(ℕ, ℂ)`.  For `w n = log (Δ (n+1))` this is the paper's log-weight operator. -/
def weightMul (w : ℕ → ℝ) : L2 →ₗ.[ℂ] L2 where
  domain := weightDomain w
  toFun :=
    { toFun := fun v => ⟨fun n => (w n : ℂ) * (v : L2) n, v.2⟩
      map_add' := by
        intro u v
        apply lp.ext
        funext n
        simp [mul_add]
        rfl
      map_smul' := by
        intro c v
        apply lp.ext
        funext n
        simp [smul_eq_mul]
        ring }

@[simp]
theorem weightMul_apply_coe (w : ℕ → ℝ) (v : (weightMul w).domain) (n : ℕ) :
    ((weightMul w v : L2) : ℕ → ℂ) n = (w n : ℂ) * ((v : L2) : ℕ → ℂ) n := rfl

@[simp]
theorem weightMul_domain (w : ℕ → ℝ) : (weightMul w).domain = weightDomain w := rfl

/-- The `n`-th phasor basis vector. -/
def phasor (n : ℕ) : L2 := lp.single 2 n (1 : ℂ)

theorem phasor_mem_weightDomain (w : ℕ → ℝ) (n : ℕ) : phasor n ∈ weightDomain w := by
  rw [mem_weightDomain_iff]
  have h : (fun m => (w m : ℂ) * (phasor n) m) = ⇑(lp.single 2 n ((w n : ℂ))) := by
    funext m
    by_cases hm : m = n
    · subst hm; simp [phasor]
    · simp [phasor, Pi.single_eq_of_ne hm]
  rw [h]
  exact lp.memℓp _

/-- The phasors are eigenvectors of the multiplication operator: the `n`-th phasor is
multiplied by the weight `w n`. -/
theorem weightMul_phasor (w : ℕ → ℝ) (n : ℕ) :
    weightMul w ⟨phasor n, phasor_mem_weightDomain w n⟩ = (w n : ℂ) • phasor n := by
  apply lp.ext
  funext m
  by_cases h : m = n
  · subst h; rfl
  · rw [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
    change (w m : ℂ) * ((phasor n : L2) : ℕ → ℂ) m = _
    simp [phasor, lp.single_apply, h]

/-- The phasor family is orthonormal. -/
theorem phasor_orthonormal : Orthonormal ℂ phasor := by
  constructor
  · intro n
    simp [phasor, lp.norm_single]
  · intro m n hmn
    simp [phasor, lp.inner_single_left, lp.single_apply, hmn]

/-- **Totality**: the span of the phasor family is dense in `ℓ²(ℕ, ℂ)`. -/
theorem phasor_total : Dense (Submodule.span ℂ (Set.range phasor) : Set L2) := by
  intro f
  have hs : HasSum (fun i : ℕ => lp.single 2 i ((f : ℕ → ℂ) i)) f :=
    lp.hasSum_single (by simp) f
  refine mem_closure_of_tendsto hs ?_
  filter_upwards with s
  refine Submodule.sum_mem _ ?_
  intro i _
  have hsingle : lp.single 2 i ((f : ℕ → ℂ) i) = ((f : ℕ → ℂ) i) • phasor i := by
    simp [phasor, ← lp.single_smul]
  rw [hsingle]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

/-- The phasors form a Hilbert basis of `ℓ²(ℕ, ℂ)`: an orthonormal total family.  Together
with `weightMul_phasor` this exhibits every weighted multiplication operator — in particular
the log-weight operator — as diagonal in this basis. -/
def phasorBasis : HilbertBasis ℕ ℂ L2 :=
  HilbertBasis.mk (𝕜 := ℂ) (E := L2) (v := phasor) phasor_orthonormal
    (by
      have h : (Submodule.span ℂ (Set.range phasor)).topologicalClosure = ⊤ :=
        Submodule.dense_iff_topologicalClosure_eq_top.mp phasor_total
      rw [h])

@[simp]
theorem phasorBasis_apply (n : ℕ) : phasorBasis n = phasor n := by
  simp [phasorBasis, HilbertBasis.coe_mk]

/-- The maximal domain of a weighted multiplication operator is dense. -/
theorem weightDomain_dense (w : ℕ → ℝ) : Dense ((weightDomain w : Submodule ℂ L2) : Set L2) := by
  refine phasor_total.mono ?_
  have : Submodule.span ℂ (Set.range phasor) ≤ weightDomain w :=
    Submodule.span_le.mpr (by rintro _ ⟨n, rfl⟩; exact phasor_mem_weightDomain w n)
  exact this

/-- The multiplication operator by a real weight is a formal adjoint of itself: it is
symmetric. -/
theorem weightMul_isFormalAdjoint (w : ℕ → ℝ) :
    (weightMul w).IsFormalAdjoint (weightMul w) := by
  intro x y
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  refine tsum_congr fun i => ?_
  simp only [weightMul_apply_coe, RCLike.inner_apply, map_mul, Complex.conj_ofReal]
  ring

/-- Any vector in the domain of the adjoint already lies in the maximal domain. -/
theorem adjointDomain_le (w : ℕ → ℝ) :
    ((weightMul w)†).domain ≤ (weightMul w).domain := by
  intro y hy
  have hd : Dense (((weightMul w).domain : Submodule ℂ L2) : Set L2) := weightDomain_dense w
  have hfa := LinearPMap.adjoint_isFormalAdjoint (T := weightMul w) hd
  have key : ∀ n : ℕ,
      (((weightMul w)† ⟨y, hy⟩ : L2) : ℕ → ℂ) n = (w n : ℂ) * ((y : L2) : ℕ → ℂ) n := by
    intro n
    have h := hfa ⟨y, hy⟩ ⟨phasor n, phasor_mem_weightDomain w n⟩
    rw [weightMul_phasor] at h
    simp only [phasor, inner_smul_right, lp.inner_single_right, RCLike.inner_apply] at h
    have h' := congrArg (starRingEnd ℂ) h
    simpa [map_mul, Complex.conj_ofReal, mul_comm] using h'
  rw [weightMul_domain, mem_weightDomain_iff]
  have hfun : (fun n => (w n : ℂ) * ((y : L2) : ℕ → ℂ) n)
      = ⇑(((weightMul w)† ⟨y, hy⟩ : L2)) := by
    funext n; exact (key n).symm
  rw [hfun]
  exact lp.memℓp _

/-- **Self-adjointness** of the multiplication operator by a real weight on its maximal
domain. -/
theorem weightMul_isSelfAdjoint (w : ℕ → ℝ) : IsSelfAdjoint (weightMul w) := by
  have hd : Dense (((weightMul w).domain : Submodule ℂ L2) : Set L2) := weightDomain_dense w
  have hle : weightMul w ≤ (weightMul w)† :=
    (weightMul_isFormalAdjoint w).le_adjoint hd
  have hge : (weightMul w)† ≤ weightMul w := by
    refine ⟨adjointDomain_le w, ?_⟩
    intro x y hxy
    exact (hle.2 hxy.symm).symm
  exact le_antisymm hge hle

/-! ### The log-weight operator of the paper -/

/-- The weight of the log-weight operator `H`: the `n`-th phasor (site `x = n+1`) is weighted
by `log (n+1)`. -/
def logWeight : ℕ → ℝ := fun n => Real.log (n + 1)

/-- The weight of the carrier-scaled log-weight operator `H_Δ`: sites at arclength
`x_n = Δ n`. -/
def carrierLogWeight (Δ : ℝ) : ℕ → ℝ := fun n => Real.log (Δ * (n + 1))

/-- The log-weight operator `H` of the carrier model. -/
def H : L2 →ₗ.[ℂ] L2 := weightMul logWeight

/-- The carrier-scaled log-weight operator `H_Δ`. -/
def HΔ (Δ : ℝ) : L2 →ₗ.[ℂ] L2 := weightMul (carrierLogWeight Δ)

theorem logWeight_isSelfAdjoint : IsSelfAdjoint H := weightMul_isSelfAdjoint _

theorem carrierLogWeight_isSelfAdjoint (Δ : ℝ) : IsSelfAdjoint (HΔ Δ) :=
  weightMul_isSelfAdjoint _

/-- `H` has the phasors as eigenvectors, with eigenvalue `log (n+1)`: the log of the site. -/
theorem H_phasor (n : ℕ) :
    H ⟨phasor n, phasor_mem_weightDomain _ n⟩ = (Real.log (n + 1) : ℂ) • phasor n :=
  weightMul_phasor _ n

/-- For `Δ > 0` the carrier scale only shifts the weight by the constant `log Δ`. -/
theorem carrierLogWeight_eq (Δ : ℝ) (hΔ : 0 < Δ) (n : ℕ) :
    carrierLogWeight Δ n = Real.log Δ + logWeight n := by
  have hn : (0:ℝ) < (n : ℝ) + 1 := by positivity
  simp [carrierLogWeight, logWeight, Real.log_mul hΔ.ne' hn.ne']

/-- Adding a constant to the weight does not change the maximal domain. -/
theorem weightDomain_const_add (c : ℝ) (w : ℕ → ℝ) :
    weightDomain (fun n => c + w n) = weightDomain w := by
  ext v
  simp only [mem_weightDomain_iff]
  have hcv : Memℓp (fun n => (c : ℂ) * ((v : L2) : ℕ → ℂ) n) 2 := (lp.memℓp v).const_mul (c : ℂ)
  constructor
  · intro hv
    have hsplit : (fun n => (w n : ℂ) * ((v : L2) : ℕ → ℂ) n)
        = (fun n => (((c + w n : ℝ)) : ℂ) * ((v : L2) : ℕ → ℂ) n)
          - (fun n => (c : ℂ) * ((v : L2) : ℕ → ℂ) n) := by
      funext n; simp only [Pi.sub_apply]; push_cast; ring
    rw [hsplit]
    exact hv.sub hcv
  · intro hv
    have hsplit : (fun n => (((c + w n : ℝ)) : ℂ) * ((v : L2) : ℕ → ℂ) n)
        = (fun n => (c : ℂ) * ((v : L2) : ℕ → ℂ) n)
          + (fun n => (w n : ℂ) * ((v : L2) : ℕ → ℂ) n) := by
      funext n; simp only [Pi.add_apply]; push_cast; ring
    rw [hsplit]
    exact hcv.add hv

/-- The carrier scale does not change the domain of the log-weight operator. -/
theorem HΔ_domain (Δ : ℝ) (hΔ : 0 < Δ) : (HΔ Δ).domain = H.domain := by
  have hw : carrierLogWeight Δ = fun n => Real.log Δ + logWeight n := by
    funext n; exact carrierLogWeight_eq Δ hΔ n
  show weightDomain (carrierLogWeight Δ) = weightDomain logWeight
  rw [hw, weightDomain_const_add]

/-- `H_Δ = H + log Δ · I`: the shift by a constant is the whole of the carrier's effect on
the log-weight operator. -/
theorem carrierLogWeight_eq_shift (Δ : ℝ) (hΔ : 0 < Δ) (v : L2)
    (hv : v ∈ (HΔ Δ).domain) (hv' : v ∈ H.domain) :
    HΔ Δ ⟨v, hv⟩ = H ⟨v, hv'⟩ + (Real.log Δ : ℂ) • v := by
  apply lp.ext
  funext n
  have hn := carrierLogWeight_eq Δ hΔ n
  show ((carrierLogWeight Δ n : ℝ) : ℂ) * ((v : L2) : ℕ → ℂ) n = _
  simp only [lp.coeFn_add, lp.coeFn_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul, H,
    weightMul_apply_coe, hn]
  push_cast
  ring

/-- The log-weight operator is genuinely unbounded: no constant dominates it on its
domain. -/
theorem logWeight_not_bounded :
    ¬ ∃ C : ℝ, ∀ v : H.domain, ‖(H v : L2)‖ ≤ C * ‖(v : L2)‖ := by
  rintro ⟨C, hC⟩
  obtain ⟨n, hn⟩ := exists_nat_gt (Real.exp C)
  have hlog : C < Real.log ((n : ℝ) + 1) := by
    have h1 : Real.exp C < (n : ℝ) + 1 := by linarith
    have := Real.log_lt_log (Real.exp_pos C) h1
    rwa [Real.log_exp] at this
  have hv := hC ⟨phasor n, phasor_mem_weightDomain _ n⟩
  rw [H_phasor n] at hv
  have hnorm : ‖phasor n‖ = 1 := by
    simp [phasor, lp.norm_single]
  rw [norm_smul, hnorm] at hv
  simp only [Complex.norm_real, Real.norm_eq_abs, mul_one] at hv
  have : Real.log ((n : ℝ) + 1) ≤ C := le_trans (le_abs_self _) hv
  linarith

end CarrierReadout
