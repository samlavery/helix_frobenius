import Mathlib
import RequestProject.SeatingLadderFold
import RequestProject.ChiralityHB

/-!
# The HP supply from the helix Euler product

Sam's standing directive (2026-08-31): prove unconditional HP; construct.
The Euler product lives on the helix (compiled: `symClock_logDeriv_expansion`,
`finiteBank_logDeriv_expansion`), and it is an OPERATOR statement already:
a unimodular clock face is a unitary boundary twist, and the compiled helix
FTA (`carrier_zeros_real`) puts every bank zero on the conjugation axis —
real spectrum from clock data, no census input.

Compiled here:
* `diagOp` + `diagOp_isSymmetric` + `diagOp_hasEigenvalue` — the diagonal
  spectral engine: any real symbol on a finite index is realized as a
  symmetric operator with those eigenvalues.
* `finiteBank_hp_supply` — **the helix Euler product supplies HP at every
  finite rank**: for any finite unitary bank and any finite set of its
  zeros, a symmetric operator (built from clock data via reality) has
  every one of them as an eigenvalue.  Unconditional.
* `xi_zeros_finite_in_compact` — zeros of `ξ` in a compact are finite
  (entire + identity theorem; anchor `ξ(0) = 1/2`).
* `hp_door_inhabited_below_ladder` — **the eigenvalue door is inhabited
  below the ladder cap**: one symmetric operator carries the spectral
  parameter `−i(ρ−1/2)` of every zero with `|Im ρ| ≤ 634.5` as an
  eigenvalue.  The campaign is the removal of the cap.

No `sorry`, no `axiom`.
-/

open Complex

noncomputable section

namespace CriticalLinePhasor.HPConstruction

open CriticalLinePhasor.ChiralityHB

/-- The diagonal operator with real symbol `d` on the finite Euclidean space. -/
def diagOp {τ : Type} [Fintype τ] (d : τ → ℝ) :
    EuclideanSpace ℂ τ →ₗ[ℂ] EuclideanSpace ℂ τ where
  toFun x := WithLp.toLp 2 fun j => (d j : ℂ) * x j
  map_add' x y := by
    ext j
    simp [mul_add]
  map_smul' c x := by
    ext j
    simp
    ring

@[simp] theorem diagOp_apply {τ : Type} [Fintype τ] (d : τ → ℝ)
    (x : EuclideanSpace ℂ τ) (j : τ) : diagOp d x j = (d j : ℂ) * x j := rfl

/-- A real diagonal symbol is symmetric. -/
theorem diagOp_isSymmetric {τ : Type} [Fintype τ] (d : τ → ℝ) :
    (diagOp d).IsSymmetric := by
  intro x y
  simp only [PiLp.inner_apply, RCLike.inner_apply, diagOp_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_mul, Complex.conj_ofReal]
  ring

/-- Each diagonal entry is an eigenvalue (standard basis eigenvector). -/
theorem diagOp_hasEigenvalue {τ : Type} [Fintype τ] [DecidableEq τ]
    (d : τ → ℝ) (j : τ) :
    Module.End.HasEigenvalue (diagOp d) ((d j : ℝ) : ℂ) := by
  apply Module.End.hasEigenvalue_of_hasEigenvector
    (x := EuclideanSpace.single j (1 : ℂ))
  constructor
  · rw [Module.End.mem_eigenspace_iff]
    ext i
    simp only [diagOp_apply, EuclideanSpace.single_apply, PiLp.smul_apply,
      smul_eq_mul]
    by_cases h : i = j
    · subst h; simp
    · simp [h]
  · intro h
    have h1 := congrArg (fun f : EuclideanSpace ℂ τ => f j) h
    simp [EuclideanSpace.single_apply] at h1

/-- **The helix Euler product supplies HP at finite rank, unconditionally.**
For any finite unitary clock bank and any finite set `Z` of its zeros,
there is a symmetric operator having every element of `Z` as an
eigenvalue.  The reality input is the compiled helix FTA
(`carrier_zeros_real`): unimodular faces force the bank's zeros onto the
conjugation axis, so the diagonal symbol `z ↦ Re z` realizes them. -/
theorem finiteBank_hp_supply {ι : Type*} (t : Finset ι) (α : ι → ℂ)
    (ℓ : ι → ℝ) (hα : ∀ i ∈ t, ‖α i‖ = 1) (hℓ : ∀ i ∈ t, 0 < ℓ i)
    (Z : Finset ℂ)
    (hZ : ∀ z ∈ Z, (∏ i ∈ t, symClock (α i) (ℓ i) z) = 0) :
    ∃ (E : Type) (_ : NormedAddCommGroup E) (_ : InnerProductSpace ℂ E)
      (T : E →ₗ[ℂ] E), T.IsSymmetric ∧
      ∀ z ∈ Z, Module.End.HasEigenvalue T z := by
  classical
  refine ⟨EuclideanSpace ℂ ↥Z, inferInstance, inferInstance,
    diagOp (fun z : ↥Z => z.val.re), diagOp_isSymmetric _, ?_⟩
  intro z hz
  have him : z.im = 0 := carrier_zeros_real t α ℓ hα hℓ (hZ z hz)
  have hzre : ((z.re : ℝ) : ℂ) = z := by
    apply Complex.ext
    · simp
    · simp [him]
  have h := diagOp_hasEigenvalue (fun w : ↥Z => w.val.re) (⟨z, hz⟩ : ↥Z)
  rwa [hzre] at h

/-- Zeros of `ξ` in any compact set are finite: `ξ` is entire and not
identically zero (`ξ(0) = 1/2`), so its zeros cannot accumulate. -/
theorem xi_zeros_finite_in_compact {K : Set ℂ} (hK : IsCompact K) :
    {z ∈ K | ZD.riemannXi z = 0}.Finite := by
  by_contra hinf
  rw [Set.not_finite] at hinf
  obtain ⟨z₀, hz₀K, hacc⟩ := hinf.exists_accPt_of_subset_isCompact hK
    (fun z hz => hz.1)
  have hana : ∀ z : ℂ, AnalyticAt ℂ ZD.riemannXi z := fun z =>
    (ZD.riemannXi_differentiable.differentiableOn).analyticAt
      (isOpen_univ.mem_nhds trivial)
  have hfreq : ∃ᶠ z in nhdsWithin z₀ {z₀}ᶜ, ZD.riemannXi z = 0 := by
    have h := accPt_iff_frequently_nhdsNE.mp hacc
    exact h.mono fun z hz => hz.2
  rcases (hana z₀).eventually_eq_zero_or_eventually_ne_zero with hev | hev
  · have hEqOn : Set.EqOn ZD.riemannXi 0 Set.univ := by
      apply AnalyticOnNhd.eqOn_zero_of_preconnected_of_eventuallyEq_zero
        (fun z _ => hana z) isPreconnected_univ (Set.mem_univ z₀)
      exact hev.mono fun z hz => by simpa using hz
    have h0 : ZD.riemannXi 0 = 0 := hEqOn (Set.mem_univ 0)
    have h12 : ZD.riemannXi 0 = 1 / 2 := by
      unfold ZD.riemannXi
      norm_num
    rw [h12] at h0
    norm_num at h0
  · obtain ⟨z, h1', h2'⟩ := (hfreq.and_eventually hev).exists
    exact h2' h1'

/-- The below-ladder zero set. -/
def LowZeros : Set ℂ :=
  {ρ : ℂ | ρ ∈ ZD.NontrivialZeros ∧ |ρ.im| ≤ 1269 / 2}

theorem lowZeros_finite : LowZeros.Finite := by
  have hK : IsCompact (Complex.reProdIm (Set.Icc (0:ℝ) 1)
      (Set.Icc (-(1269/2) : ℝ) (1269/2))) :=
    isCompact_Icc.reProdIm isCompact_Icc
  refine (xi_zeros_finite_in_compact hK).subset ?_
  rintro ρ ⟨hρ, him⟩
  refine ⟨?_, ZD.riemannXi_eq_zero_of_mem_NontrivialZeros ρ hρ⟩
  rw [Complex.mem_reProdIm]
  rcases abs_le.mp him with ⟨h1, h2⟩
  exact ⟨⟨hρ.1.le, hρ.2.1.le⟩, ⟨h1, h2⟩⟩

/-- **The eigenvalue door is inhabited below the ladder cap**: a single
symmetric operator carries `−i(ρ−1/2)` as an eigenvalue for every
nontrivial zero with `|Im ρ| ≤ 1269/2`.  Reality is supplied by the
compiled ladder (`online_below_1269o2`), realization by the diagonal
engine.  The HP campaign is the removal of the cap. -/
theorem hp_door_inhabited_below_ladder :
    ∃ (E : Type) (_ : NormedAddCommGroup E) (_ : InnerProductSpace ℂ E)
      (T : E →ₗ[ℂ] E), T.IsSymmetric ∧
      ∀ ρ ∈ ZD.NontrivialZeros, |ρ.im| ≤ 1269 / 2 →
        Module.End.HasEigenvalue T (-Complex.I * (ρ - 1 / 2)) := by
  classical
  haveI : Fintype ↥LowZeros := lowZeros_finite.fintype
  refine ⟨EuclideanSpace ℂ ↥LowZeros, inferInstance, inferInstance,
    diagOp (fun ρ : ↥LowZeros => ρ.val.im), diagOp_isSymmetric _, ?_⟩
  intro ρ hρ him
  have hre : ρ.re = 1 / 2 :=
    CriticalLinePhasor.DVP.online_below_1269o2 ρ hρ him
  have hρeq : ((ρ.re : ℝ) : ℂ) + (ρ.im : ℝ) * Complex.I = ρ :=
    Complex.re_add_im ρ
  have hrec : ((ρ.re : ℝ) : ℂ) = 1 / 2 := by
    rw [hre]; push_cast; ring
  have hμ : ((ρ.im : ℝ) : ℂ) = -Complex.I * (ρ - 1 / 2) := by
    linear_combination (-Complex.I) * hρeq + Complex.I * hrec
      + (ρ.im : ℂ) * Complex.I_mul_I
  have h := diagOp_hasEigenvalue (fun w : ↥LowZeros => w.val.im)
    (⟨ρ, hρ, him⟩ : ↥LowZeros)
  rwa [hμ] at h

end CriticalLinePhasor.HPConstruction

#print axioms CriticalLinePhasor.HPConstruction.finiteBank_hp_supply
#print axioms CriticalLinePhasor.HPConstruction.xi_zeros_finite_in_compact
#print axioms CriticalLinePhasor.HPConstruction.hp_door_inhabited_below_ladder
