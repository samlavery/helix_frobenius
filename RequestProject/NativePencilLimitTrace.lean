import RequestProject.ThreeDNativePencilLimit
import RequestProject.CarrierChannelReadout

/-!
# The commuting square of the native two-lane pencil (ledger 1149)

The square, at a fixed input `s` and a nonprincipal character `χ`:

    S_N(χ,s)  ──── coupling entry ────▶  stage-N native pencil (A_N, B_N)
       │                                          │
       │ nativeCoupling_tendsto_LFunction         │ ?
       ▼                                          ▼
    L(s,χ)    ──── (0,1) entry ───────▶  fullFiberMatrix χ s = !![1, L; 0, L]

What this file proves about it:
* **The square commutes on the coupling block** (`square_commutes_on_coupling_block`): the
  spatial off-diagonal block of the stage-N native height operator is `S_N·I₃`, and it converges
  as a matrix to `L(s,χ)·I₃`, whose determinant is `L³` (`limit_coupling_block_det`).
* **The identification at the limit is scalar** (`L_zero_iff_coupling_tendsto_zero`,
  `zeta_zero_iff_eta_coupling_tendsto_zero`): `L(s,χ) = 0` iff the coupling tends to zero, i.e. the
  two lanes decouple in the limit; for `ζ` on the open strip through the η configuration.
* **The diagonal blocks have no limit.** The reference lane has metric mass `N` and height mass
  `N(N+1)/2`. Under the `1/(N+1)` scalar of `ThreeDNativePencilLimit` the reference height entry
  is exactly `(N+2)/2` (`nativePencilA_reference_height`), which is unbounded, and the coupling
  entry tends to `0` at every `s` with `Re s > 0`, whether or not `L(s,χ) = 0`
  (`nativePencilA_coupling_tendsto_zero`).
* **Lane rescaling cannot restore the coupling.** The dimensionless coupling
  `κ = |C|²/(m_ref·m_fib)` is invariant under every lane-diagonal congruence
  (`pairCoupling_laneScale`), the `1/(N+1)` scalar included (`nativePencil_pairCoupling`), and
  `κ_N → 0` for every nonprincipal character and for the η configuration
  (`couplingCoeff_tendsto_zero`, `eta_couplingCoeff_tendsto_zero`). The characteristic polynomial
  is `det(A_N − zB_N) = (a_ref − z m_ref)(a_fib − z m_fib) − |S_N|²` (`stage_charpoly`): the
  L-information enters only through `|S_N|²`.
-/

open Matrix Complex Filter Topology
open scoped BigOperators Kronecker ComplexOrder

namespace CriticalLinePhasor.NativeSquare

open CriticalLinePhasor.Pencil3D CriticalLinePhasor.Geometric CriticalLinePhasor.SpectralFiber

/-! ## 1. The stage-N native pencil, unnormalized -/

/-- The stage-`N` native two-lane height operator, physical heights `1, …, N`. -/
noncomputable def stageA (w : ℕ → ℂ) (s : ℂ) (N : ℕ) :
    Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) ℂ :=
  twoLaneHelixA (referenceLane N) (nativeFiberLane w s N) (fun i => (i.val + 1 : ℝ))

/-- The stage-`N` native two-lane metric. -/
noncomputable def stageB (w : ℕ → ℂ) (s : ℂ) (N : ℕ) :
    Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) ℂ :=
  twoLaneB (referenceLane N) (nativeFiberLane w s N)

theorem nativePencilA_eq (w : ℕ → ℂ) (s : ℂ) (N : ℕ) :
    nativePencilA w s N = (1 / ((N + 1 : ℕ) : ℝ)) • spatial (stageA w s (N + 1)) :=
  rfl

theorem nativePencilB_eq (w : ℕ → ℂ) (s : ℂ) (N : ℕ) :
    nativePencilB w s N = (1 / ((N + 1 : ℕ) : ℝ)) • spatial (stageB w s (N + 1)) :=
  rfl

theorem stageA_coupling (w : ℕ → ℂ) (s : ℂ) (N : ℕ) :
    stageA w s N (Sum.inl 0) (Sum.inr 0) = nativeCoupling w s N :=
  rfl

theorem stageA_coupling_adjoint (w : ℕ → ℂ) (s : ℂ) (N : ℕ) :
    stageA w s N (Sum.inr 0) (Sum.inl 0) = star (nativeCoupling w s N) :=
  rfl

/-- The spatial off-diagonal block is the native partial sum times `I₃`. -/
theorem spatial_stageA_coupling (w : ℕ → ℂ) (s : ℂ) (N : ℕ) (i j : Fin 3) :
    spatial (stageA w s N) (Sum.inl 0, i) (Sum.inr 0, j) =
      nativeCoupling w s N * (1 : Matrix (Fin 3) (Fin 3) ℂ) i j := by
  simp only [spatial, Matrix.kroneckerMap_apply, stageA_coupling]

/-- The spatial coupling block of the stage-`N` operator. -/
noncomputable def couplingBlock (w : ℕ → ℂ) (s : ℂ) (N : ℕ) : Matrix (Fin 3) (Fin 3) ℂ :=
  fun i j => spatial (stageA w s N) (Sum.inl 0, i) (Sum.inr 0, j)

theorem couplingBlock_eq (w : ℕ → ℂ) (s : ℂ) (N : ℕ) :
    couplingBlock w s N = nativeCoupling w s N • (1 : Matrix (Fin 3) (Fin 3) ℂ) := by
  ext i j
  rw [couplingBlock, spatial_stageA_coupling, Matrix.smul_apply, smul_eq_mul]

/-! ## 2. The bottom edge and the commuting square on the coupling block -/

/-- The `(0,1)` entry of the completed full-fiber matrix is the L-value, inserted directly. -/
theorem fullFiberMatrix_coupling {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (s : ℂ) :
    fullFiberMatrix χ s 0 1 = DirichletCharacter.LFunction χ s := by
  simp [fullFiberMatrix, HarmonicCell.harmonicPencil]

/-- **The square commutes on the coupling block**: the stage-`N` spatial coupling block converges,
as a matrix, to the completed full-fiber `(0,1)` entry times `I₃`. -/
theorem square_commutes_on_coupling_block {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ ≠ 1) {s : ℂ} (hs : 0 < s.re) :
    Tendsto (couplingBlock (fun n => χ (n : ZMod q)) s) atTop
      (𝓝 (fullFiberMatrix χ s 0 1 • (1 : Matrix (Fin 3) (Fin 3) ℂ))) := by
  rw [fullFiberMatrix_coupling,
    show couplingBlock (fun n => χ (n : ZMod q)) s =
      fun N => nativeCoupling (fun n => χ (n : ZMod q)) s N • (1 : Matrix (Fin 3) (Fin 3) ℂ) from
      funext (couplingBlock_eq _ s)]
  exact (nativeCoupling_tendsto_LFunction χ hχ hs).smul_const _

/-- The limit block is singular exactly at an L-zero: `det(L·I₃) = L³`. -/
theorem limit_coupling_block_det (L : ℂ) :
    (L • (1 : Matrix (Fin 3) (Fin 3) ℂ)).det = L ^ 3 := by
  simp

theorem limit_coupling_block_singular_iff (L : ℂ) :
    (L • (1 : Matrix (Fin 3) (Fin 3) ℂ)).det = 0 ↔ L = 0 := by
  rw [limit_coupling_block_det, pow_eq_zero_iff (by norm_num)]

/-! ## 3. The identification at the limit: lane decoupling -/

/-- **`L(s,χ) = 0` iff the native coupling tends to zero** (the lanes decouple in the limit), for
a nonprincipal character at every `Re s > 0`. -/
theorem L_zero_iff_coupling_tendsto_zero {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ ≠ 1) {s : ℂ} (hs : 0 < s.re) :
    DirichletCharacter.LFunction χ s = 0 ↔
      Tendsto (nativeCoupling (fun n => χ (n : ZMod q)) s) atTop (𝓝 0) := by
  have h := nativeCoupling_tendsto_LFunction χ hχ hs
  constructor
  · intro hL
    rwa [hL] at h
  · intro h0
    exact tendsto_nhds_unique h h0

/-- **`ζ(s) = 0` iff the η-configured native coupling tends to zero**, on the open strip; the
η factor `1 − 2^{1−s}` does not vanish there. -/
theorem zeta_zero_iff_eta_coupling_tendsto_zero {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1) :
    riemannZeta s = 0 ↔ Tendsto (nativeCoupling etaW s) atTop (𝓝 0) := by
  have hne : s ≠ 1 := by
    rintro rfl
    simp at hs1
  have h := nativeCoupling_tendsto_eta hs0 hne
  constructor
  · intro hz
    rwa [hz, mul_zero] at h
  · intro h0
    exact (mul_eq_zero.mp (tendsto_nhds_unique h h0)).resolve_left
      (CarrierChannelReadout.etaFactor_ne_zero hs1)

/-! ## 4. The normalized pencil of `ThreeDNativePencilLimit` -/

theorem nativePencilA_coupling (w : ℕ → ℂ) (s : ℂ) (N : ℕ) (i j : Fin 3) :
    nativePencilA w s N (Sum.inl 0, i) (Sum.inr 0, j) =
      ((1 / ((N + 1 : ℕ) : ℝ) : ℝ) : ℂ) *
        (nativeCoupling w s (N + 1) * (1 : Matrix (Fin 3) (Fin 3) ℂ) i j) := by
  rw [nativePencilA_eq, Matrix.smul_apply, spatial_stageA_coupling, Complex.real_smul]

/-- **The normalized coupling tends to zero at every `Re s > 0`**, whether or not `L(s,χ) = 0`. -/
theorem nativePencilA_coupling_tendsto_zero {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ ≠ 1) {s : ℂ} (hs : 0 < s.re) (i j : Fin 3) :
    Tendsto (fun N => nativePencilA (fun n => χ (n : ZMod q)) s N (Sum.inl 0, i) (Sum.inr 0, j))
      atTop (𝓝 0) := by
  simp only [nativePencilA_coupling]
  have h1 : Tendsto (fun N : ℕ => ((1 / ((N + 1 : ℕ) : ℝ) : ℝ) : ℂ)) atTop (𝓝 0) := by
    have h := (Complex.continuous_ofReal.tendsto 0).comp tendsto_one_div_add_atTop_nhds_zero_nat
    simpa [Function.comp_def] using h
  have h2 := ((nativeCoupling_tendsto_LFunction χ hχ hs).comp
    (tendsto_add_atTop_nat 1)).mul_const ((1 : Matrix (Fin 3) (Fin 3) ℂ) i j)
  simpa using h1.mul h2

/-- The reference lane's height mass is the Gauss sum of the physical heights. -/
theorem sum_heights (N : ℕ) :
    ∑ k : Fin N, (((k.val + 1 : ℝ)) : ℂ) = (N : ℂ) * (N + 1) / 2 := by
  rw [Fin.sum_univ_eq_sum_range (fun k => (((k + 1 : ℝ)) : ℂ)) N]
  induction N with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    ring

theorem stageA_reference (w : ℕ → ℂ) (s : ℂ) (N : ℕ) :
    stageA w s N (Sum.inl 0) (Sum.inl 0) = (N : ℂ) * (N + 1) / 2 := by
  rw [← sum_heights]
  simp only [stageA, twoLaneHelixA, twoLaneA, Matrix.fromBlocks_apply₁₁, heightA,
    Matrix.mul_apply, Matrix.conjTranspose_apply, referenceLane, star_one, one_mul, mul_one,
    Matrix.diagonal_apply, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

/-- **The normalized reference height entry is exactly `(N+2)/2`.** -/
theorem nativePencilA_reference_height (w : ℕ → ℂ) (s : ℂ) (N : ℕ) (i : Fin 3) :
    nativePencilA w s N (Sum.inl 0, i) (Sum.inl 0, i) = ((N : ℂ) + 2) / 2 := by
  rw [nativePencilA_eq, Matrix.smul_apply]
  simp only [spatial, Matrix.kroneckerMap_apply, stageA_reference, Matrix.one_apply_eq, mul_one,
    Complex.real_smul]
  have hN : ((N : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero N
  push_cast
  field_simp
  ring

/-- The normalized operator has no limit: its reference height entry is unbounded. -/
theorem nativePencilA_reference_height_unbounded (w : ℕ → ℂ) (s : ℂ) (i : Fin 3) :
    Tendsto (fun N => (nativePencilA w s N (Sum.inl 0, i) (Sum.inl 0, i)).re) atTop atTop := by
  have h : ∀ N : ℕ, (nativePencilA w s N (Sum.inl 0, i) (Sum.inl 0, i)).re = ((N : ℝ) + 2) / 2 := by
    intro N
    rw [nativePencilA_reference_height]
    have : ((N : ℂ) + 2) / 2 = ((((N : ℝ) + 2) / 2 : ℝ) : ℂ) := by push_cast; ring
    rw [this, Complex.ofReal_re]
  simp only [h]
  exact (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds).atTop_div_const two_pos

/-! ## 5. The dimensionless coupling and its invariance -/

/-- The fiber lane's metric mass `Σ |readout(n)|²`. -/
noncomputable def fiberMass (w : ℕ → ℂ) (s : ℂ) (N : ℕ) : ℝ :=
  ∑ k : Fin N, ‖readout w s (k.val + 1)‖ ^ 2

theorem fiberMass_nonneg (w : ℕ → ℂ) (s : ℂ) (N : ℕ) : 0 ≤ fiberMass w s N :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem fiberMass_ge (w : ℕ → ℂ) (s : ℂ) (N : ℕ) (hN : 0 < N) :
    ‖w 1‖ ^ 2 ≤ fiberMass w s N := by
  have h := Finset.single_le_sum (f := fun k : Fin N => ‖readout w s (k.val + 1)‖ ^ 2)
    (fun _ _ => sq_nonneg _) (Finset.mem_univ ⟨0, hN⟩)
  have h1 : readout w s ((⟨0, hN⟩ : Fin N).val + 1) = w 1 := native_readout_one w s
  rw [← h1]
  exact h

theorem stageB_reference (w : ℕ → ℂ) (s : ℂ) (N : ℕ) :
    stageB w s N (Sum.inl 0) (Sum.inl 0) = N := by
  rw [stageB, twoLaneB_eq_blockDiag]
  simp [Matrix.mul_apply, referenceLane]

theorem stageB_fiber (w : ℕ → ℂ) (s : ℂ) (N : ℕ) :
    stageB w s N (Sum.inr 0) (Sum.inr 0) = (fiberMass w s N : ℂ) := by
  rw [stageB, twoLaneB_eq_blockDiag]
  simp only [Matrix.fromBlocks_apply₂₂, Matrix.mul_apply, Matrix.conjTranspose_apply,
    nativeFiberLane, fiberMass]
  push_cast
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Complex.star_def, Complex.conj_mul', norm_mul, norm_inv, cell_norm, inv_one, one_mul]

/-- The dimensionless coupling of a two-lane pair: `|C|² / (m_ref · m_fib)`. -/
noncomputable def pairCoupling (A B : Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) ℂ) : ℝ :=
  ‖A (Sum.inl 0) (Sum.inr 0)‖ ^ 2 /
    ((B (Sum.inl 0) (Sum.inl 0)).re * (B (Sum.inr 0) (Sum.inr 0)).re)

/-- The stage-`N` dimensionless coupling `|S_N|² / (N · fiberMass)`. -/
noncomputable def couplingCoeff (w : ℕ → ℂ) (s : ℂ) (N : ℕ) : ℝ :=
  ‖nativeCoupling w s N‖ ^ 2 / ((N : ℝ) * fiberMass w s N)

theorem pairCoupling_stage (w : ℕ → ℂ) (s : ℂ) (N : ℕ) :
    pairCoupling (stageA w s N) (stageB w s N) = couplingCoeff w s N := by
  rw [pairCoupling, couplingCoeff, stageA_coupling, stageB_reference, stageB_fiber,
    Complex.natCast_re, Complex.ofReal_re]

/-- A lane-diagonal rescaling `diag(a, b)`. -/
noncomputable def laneScale (a b : ℂ) : Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) ℂ :=
  Matrix.diagonal (Sum.elim (fun _ => a) (fun _ => b))

theorem laneScale_congr_apply (M : Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) ℂ) (a b : ℂ)
    (x y : Fin 1 ⊕ Fin 1) :
    ((laneScale a b)ᴴ * M * laneScale a b) x y =
      star (Sum.elim (fun _ => a) (fun _ => b) x) * M x y *
        Sum.elim (fun (_ : Fin 1) => a) (fun _ => b) y := by
  rw [laneScale, Matrix.diagonal_conjTranspose, Matrix.mul_diagonal, Matrix.diagonal_mul]
  rfl

theorem star_mul_mul_self_re (a x : ℂ) : (star a * x * a).re = ‖a‖ ^ 2 * x.re := by
  have h : star a * x * a = ((‖a‖ ^ 2 : ℝ) : ℂ) * x := by
    rw [mul_comm (star a) x, mul_assoc, Complex.star_def, Complex.conj_mul']
    push_cast
    ring
  rw [h, Complex.re_ofReal_mul]

/-- **The dimensionless coupling is invariant under every lane-diagonal congruence.** -/
theorem pairCoupling_laneScale (A B : Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) ℂ) {a b : ℂ}
    (ha : a ≠ 0) (hb : b ≠ 0) :
    pairCoupling ((laneScale a b)ᴴ * A * laneScale a b) ((laneScale a b)ᴴ * B * laneScale a b) =
      pairCoupling A B := by
  simp only [pairCoupling, laneScale_congr_apply, Sum.elim_inl, Sum.elim_inr,
    star_mul_mul_self_re, norm_mul, norm_star]
  have ha' : 0 < ‖a‖ := norm_pos_iff.mpr ha
  have hb' : 0 < ‖b‖ := norm_pos_iff.mpr hb
  rw [show ‖a‖ ^ 2 * (B (Sum.inl 0) (Sum.inl 0)).re * (‖b‖ ^ 2 * (B (Sum.inr 0) (Sum.inr 0)).re) =
      (‖a‖ * ‖b‖) ^ 2 * ((B (Sum.inl 0) (Sum.inl 0)).re * (B (Sum.inr 0) (Sum.inr 0)).re) by ring,
    show (‖a‖ * ‖A (Sum.inl 0) (Sum.inr 0)‖ * ‖b‖) ^ 2 =
      (‖a‖ * ‖b‖) ^ 2 * ‖A (Sum.inl 0) (Sum.inr 0)‖ ^ 2 by ring,
    mul_div_mul_left _ _ (by positivity)]

/-- The normalized pencil of `ThreeDNativePencilLimit` carries the same dimensionless coupling
as the unnormalized stage `N+1`: the `1/(N+1)` scalar cancels. -/
theorem nativePencil_pairCoupling (w : ℕ → ℂ) (s : ℂ) (N : ℕ) :
    ‖nativePencilA w s N (Sum.inl 0, 0) (Sum.inr 0, 0)‖ ^ 2 /
        ((nativePencilB w s N (Sum.inl 0, 0) (Sum.inl 0, 0)).re *
          (nativePencilB w s N (Sum.inr 0, 0) (Sum.inr 0, 0)).re) =
      couplingCoeff w s (N + 1) := by
  rw [← pairCoupling_stage, pairCoupling, nativePencilA_eq, nativePencilB_eq]
  simp only [Matrix.smul_apply, spatial, Matrix.kroneckerMap_apply, Matrix.one_apply_eq, mul_one,
    Complex.real_smul, norm_mul, Complex.re_ofReal_mul, Complex.norm_real, Real.norm_eq_abs]
  have hr : 0 < (1 / ((N + 1 : ℕ) : ℝ)) := by positivity
  rw [abs_of_pos hr]
  rw [show (1 / ((N + 1 : ℕ) : ℝ) * (stageB w s (N + 1) (Sum.inl 0) (Sum.inl 0)).re) *
        (1 / ((N + 1 : ℕ) : ℝ) * (stageB w s (N + 1) (Sum.inr 0) (Sum.inr 0)).re) =
      (1 / ((N + 1 : ℕ) : ℝ)) ^ 2 * ((stageB w s (N + 1) (Sum.inl 0) (Sum.inl 0)).re *
        (stageB w s (N + 1) (Sum.inr 0) (Sum.inr 0)).re) by ring,
    mul_pow, mul_div_mul_left _ _ (by positivity)]

/-- **The dimensionless coupling tends to zero** for any weight with `|w 1| = 1` whose coupling
converges. -/
theorem couplingCoeff_tendsto_zero_of_tendsto (w : ℕ → ℂ) (hw : ‖w 1‖ = 1) (s L : ℂ)
    (hC : Tendsto (nativeCoupling w s) atTop (𝓝 L)) :
    Tendsto (couplingCoeff w s) atTop (𝓝 0) := by
  have hC2 := (hC.norm.pow 2).mul tendsto_one_div_atTop_nhds_zero_nat
  rw [mul_zero] at hC2
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hC2 ?_ ?_
  · filter_upwards with N
    exact div_nonneg (sq_nonneg _) (mul_nonneg (Nat.cast_nonneg _) (fiberMass_nonneg w s N))
  · filter_upwards [eventually_ge_atTop 1] with N hN
    have hm := fiberMass_ge w s N hN
    rw [hw, one_pow] at hm
    have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
    rw [couplingCoeff, div_eq_mul_one_div]
    refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
    exact one_div_le_one_div_of_le (by positivity) (by nlinarith)

theorem couplingCoeff_tendsto_zero {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ ≠ 1) {s : ℂ} (hs : 0 < s.re) :
    Tendsto (couplingCoeff (fun n => χ (n : ZMod q)) s) atTop (𝓝 0) :=
  couplingCoeff_tendsto_zero_of_tendsto _ (by simp) s _ (nativeCoupling_tendsto_LFunction χ hχ hs)

theorem eta_couplingCoeff_tendsto_zero {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) :
    Tendsto (couplingCoeff etaW s) atTop (𝓝 0) :=
  couplingCoeff_tendsto_zero_of_tendsto _ (by norm_num [etaW]) s _
    (nativeCoupling_tendsto_eta hs hs1)

/-! ## 6. The characteristic polynomial -/

theorem det_sum_one_one (M : Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) ℂ) :
    M.det = M (Sum.inl 0) (Sum.inl 0) * M (Sum.inr 0) (Sum.inr 0) -
      M (Sum.inl 0) (Sum.inr 0) * M (Sum.inr 0) (Sum.inl 0) := by
  rw [← Matrix.det_reindex_self finSumFinEquiv M]
  exact Matrix.det_fin_two _

theorem stageB_offDiag (w : ℕ → ℂ) (s : ℂ) (N : ℕ) :
    stageB w s N (Sum.inl 0) (Sum.inr 0) = 0 ∧ stageB w s N (Sum.inr 0) (Sum.inl 0) = 0 := by
  rw [stageB, twoLaneB_eq_blockDiag]
  exact ⟨rfl, rfl⟩

/-- **The characteristic polynomial of the stage pencil**: the L-information enters only through
`|S_N|²`. -/
theorem stage_charpoly (w : ℕ → ℂ) (s z : ℂ) (N : ℕ) :
    (stageA w s N - z • stageB w s N).det =
      (stageA w s N (Sum.inl 0) (Sum.inl 0) - z * N) *
          (stageA w s N (Sum.inr 0) (Sum.inr 0) - z * fiberMass w s N) -
        ((‖nativeCoupling w s N‖ ^ 2 : ℝ) : ℂ) := by
  rw [det_sum_one_one]
  simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, stageB_reference, stageB_fiber,
    (stageB_offDiag w s N).1, (stageB_offDiag w s N).2, mul_zero, sub_zero, stageA_coupling,
    stageA_coupling_adjoint]
  rw [Complex.star_def, mul_comm (nativeCoupling w s N), Complex.conj_mul']
  push_cast
  ring

end CriticalLinePhasor.NativeSquare

#print axioms CriticalLinePhasor.NativeSquare.square_commutes_on_coupling_block
#print axioms CriticalLinePhasor.NativeSquare.limit_coupling_block_singular_iff
#print axioms CriticalLinePhasor.NativeSquare.L_zero_iff_coupling_tendsto_zero
#print axioms CriticalLinePhasor.NativeSquare.zeta_zero_iff_eta_coupling_tendsto_zero
#print axioms CriticalLinePhasor.NativeSquare.nativePencilA_coupling_tendsto_zero
#print axioms CriticalLinePhasor.NativeSquare.nativePencilA_reference_height_unbounded
#print axioms CriticalLinePhasor.NativeSquare.pairCoupling_laneScale
#print axioms CriticalLinePhasor.NativeSquare.nativePencil_pairCoupling
#print axioms CriticalLinePhasor.NativeSquare.couplingCoeff_tendsto_zero
#print axioms CriticalLinePhasor.NativeSquare.eta_couplingCoeff_tendsto_zero
#print axioms CriticalLinePhasor.NativeSquare.stage_charpoly
