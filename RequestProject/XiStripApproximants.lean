import RequestProject.FinitePartSymmetry
import RequestProject.XiHadamardFactorization
import RequestProject.XiProductMultPartialFraction
import RequestProject.FlowCoshStages

/-!
# Real polynomial approximants of `Ξ(z) = ξ(½ + iz)` with zeros in the strip `|Im z| < ½` (T2c)

From the compiled Hadamard product `ξ(s) = e^{As+B} ∏'_{(ρ,k)} (1 − s/ρ)e^{s/ρ}` (`riemannXi_hadamard_factorization`)
restricted to the cofinal finite zero sets `G_N = {ρ : |Im ρ| ≤ N}` (closed under `ρ ↦ 1 − ρ` and `ρ ↦ ρ̄`): at
`s = ½ + iz`,
  `e^{As+B} ∏_{ρ ∈ G_N} ((1 − s/ρ)e^{s/ρ})^{m_ρ} = κ_N · e^{iz(A + c_N)} · Q_N(z)`,
with `Q_N(z) = ∏_{ρ∈G_N} (1 − z/w_ρ)^{m_ρ}` (`w_ρ = −i(ρ − ½)`) and `c_N = Σ_{G_N} m_ρ/ρ`.  The paired sums `c_N`
converge to `−A` (`reflection_const_eq_zero`), `κ_N → Ξ(0) ≠ 0`, so `Ξ(0)·Q_N → Ξ` locally uniformly.  `Q_N` has real
coefficients (its zero multiset is conjugation-closed) and its zeros `w_ρ` satisfy `|Im w_ρ| < ½`.

Main result: `xiSection_stripClass : StripClass (1/4) xiSection`.
-/

open Complex Polynomial Filter Topology Set
open CriticalLinePhasor.ContourArgument
open CriticalLinePhasor.DeBruijn (StripClass aeval_eq_eval_map)
open CriticalLinePhasor.XiChannel (xiSection)
open CriticalLinePhasor.XiKernel (xiSection_zero_ne_zero xiSection_eq_Ktrans differentiable_Ktrans)

namespace CriticalLinePhasor.XiApprox

abbrev Zero := {ρ : ℂ // ρ ∈ ZD.NontrivialZeros}

/-! ### The factorization constant is the partial-fraction constant -/

theorem hadamard_factorization_const :
    ∃ B : ℂ, ∀ z : ℂ, ZD.riemannXi z = Complex.exp (xiHadamardConst * z + B) * ZD.xiProductMult z := by
  obtain ⟨A, B, hAB⟩ := ZD.riemannXi_hadamard_factorization
  have h2 : (2 : ℂ) ∉ ZD.NontrivialZeros := two_ne_zero_mem
  have hne1 : Complex.exp (A * 2 + B) ≠ 0 := Complex.exp_ne_zero _
  have hne2 : ZD.xiProductMult 2 ≠ 0 := ZD.xiProductMult_ne_zero_of_notMem_NontrivialZeros h2
  have hd1 : DifferentiableAt ℂ (fun z : ℂ => Complex.exp (A * z + B)) 2 := by fun_prop
  have hd2 : DifferentiableAt ℂ ZD.xiProductMult 2 := ZD.xiProductMult_differentiable 2
  have hξ : ZD.riemannXi = fun z => Complex.exp (A * z + B) * ZD.xiProductMult z := funext hAB
  have hexp : logDeriv (fun z : ℂ => Complex.exp (A * z + B)) 2 = A := by
    rw [logDeriv_apply]
    have h : HasDerivAt (fun z : ℂ => Complex.exp (A * z + B)) (Complex.exp (A * 2 + B) * A) 2 := by
      have := (((hasDerivAt_id (2 : ℂ)).const_mul A).add_const B).cexp
      simpa using this
    rw [h.deriv]
    field_simp
  have hlog : logDeriv ZD.riemannXi 2 = A + logDeriv ZD.xiProductMult 2 := by
    rw [hξ, logDeriv_mul 2 hne1 hne2 hd1 hd2, hexp]
  rw [logDeriv_apply, xiHadamardConst_spec 2 h2, ZD.logDeriv_xiProductMult_partial_fraction h2] at hlog
  have hA : A = xiHadamardConst := (add_right_cancel hlog).symm
  exact ⟨B, fun z => by rw [hAB z, hA]⟩

/-- The exponential constant of the factorization, fixed. -/
noncomputable def hadamardB : ℂ := Classical.choose hadamard_factorization_const

theorem riemannXi_eq_factor (z : ℂ) :
    ZD.riemannXi z = Complex.exp (xiHadamardConst * z + hadamardB) * ZD.xiProductMult z :=
  Classical.choose_spec hadamard_factorization_const z

/-! ### The zeros: spectral coordinate and elementary facts -/

theorem im_ne_zero (ρ : Zero) : ρ.val.im ≠ 0 := by
  intro h0
  obtain ⟨hre0, hre1, hz⟩ := ρ.2
  have := riemannZeta_nontrivial_zero_im_ge_two hz (by
    intro n hn
    have := congrArg Complex.re hn
    simp at this
    linarith)
  rw [h0] at this
  simp at this
  linarith

theorem val_ne_zero (ρ : Zero) : ρ.val ≠ 0 := by
  intro h
  have := ρ.2.1
  rw [h] at this
  simp at this

/-- `w ρ = −i(ρ − ½)`. -/
noncomputable def w (ρ : Zero) : ℂ := -I * (ρ.val - 1 / 2)

theorem I_mul_w (ρ : Zero) : I * w ρ = ρ.val - 1 / 2 := by
  unfold w
  linear_combination (-(ρ.val - 1 / 2)) * Complex.I_mul_I

theorem w_im (ρ : Zero) : (w ρ).im = -(ρ.val.re - 1 / 2) := by
  unfold w
  simp [Complex.mul_im, Complex.sub_re]

theorem w_re (ρ : Zero) : (w ρ).re = ρ.val.im := by
  unfold w
  simp [Complex.mul_re, Complex.sub_im]

theorem w_ne_zero (ρ : Zero) : w ρ ≠ 0 := by
  intro h
  have := w_re ρ
  rw [h] at this
  exact im_ne_zero ρ (by simpa using this.symm)

theorem w_im_sq_le (ρ : Zero) : (w ρ).im ^ 2 ≤ 1 / 4 := by
  rw [w_im]
  have h0 := ρ.2.1
  have h1 := ρ.2.2.1
  nlinarith

theorem w_conj (ρ : Zero) : (starRingEnd ℂ) (w ρ) = w (mirrorZero (conjZero ρ)) := by
  unfold w
  rw [mirrorZero_val, conjZero_val]
  simp only [map_mul, map_neg, Complex.conj_I, map_sub, map_div₀, map_one, map_ofNat]
  ring

/-! ### The cofinal finite zero sets -/

theorem finite_zerosUpTo (N : ℕ) : {ρ : Zero | |ρ.val.im| ≤ N}.Finite := by
  have h := ZD.ZeroCount.NontrivialZeros_inter_closedBall_finite (N + 1)
  refine (h.preimage (Subtype.val_injective.injOn)).subset ?_
  intro ρ hρ
  have hρ' : |ρ.val.im| ≤ N := hρ
  refine Set.mem_preimage.mpr ⟨ρ.2, ?_⟩
  rw [Metric.mem_closedBall, dist_zero_right]
  have hre : |ρ.val.re| ≤ 1 := by
    have := ρ.2.1; have := ρ.2.2.1
    rw [abs_le]; constructor <;> linarith
  calc ‖ρ.val‖ = ‖(ρ.val.re : ℂ) + (ρ.val.im : ℂ) * I‖ := by rw [Complex.re_add_im]
    _ ≤ ‖(ρ.val.re : ℂ)‖ + ‖(ρ.val.im : ℂ) * I‖ := norm_add_le _ _
    _ = |ρ.val.re| + |ρ.val.im| := by simp
    _ ≤ 1 + N := add_le_add hre hρ'
    _ = N + 1 := by ring

/-- `G_N = {ρ : |Im ρ| ≤ N}`. -/
noncomputable def zerosUpTo (N : ℕ) : Finset Zero := (finite_zerosUpTo N).toFinset

theorem mem_zerosUpTo {N : ℕ} {ρ : Zero} : ρ ∈ zerosUpTo N ↔ |ρ.val.im| ≤ N := by
  unfold zerosUpTo
  rw [Set.Finite.mem_toFinset]
  rfl

theorem mirrorZero_mem_zerosUpTo {N : ℕ} (ρ : Zero) : mirrorZero ρ ∈ zerosUpTo N ↔ ρ ∈ zerosUpTo N := by
  simp only [mem_zerosUpTo, mirrorZero_val, Complex.sub_im, Complex.one_im, zero_sub, abs_neg]

theorem conjZero_mem_zerosUpTo {N : ℕ} (ρ : Zero) : conjZero ρ ∈ zerosUpTo N ↔ ρ ∈ zerosUpTo N := by
  simp only [mem_zerosUpTo, conjZero_val, Complex.conj_im, abs_neg]

theorem tendsto_zerosUpTo : Tendsto zerosUpTo atTop atTop := by
  rw [Filter.tendsto_atTop_atTop]
  intro G
  refine ⟨G.sup (fun ρ : Zero => (Nat.ceil |ρ.val.im| : ℕ)), fun N hN ρ hρ => ?_⟩
  rw [mem_zerosUpTo]
  have hle : (Nat.ceil |ρ.val.im| : ℕ) ≤ G.sup (fun ρ : Zero => (Nat.ceil |ρ.val.im| : ℕ)) :=
    Finset.le_sup (f := fun ρ : Zero => (Nat.ceil |ρ.val.im| : ℕ)) hρ
  calc |ρ.val.im| ≤ (Nat.ceil |ρ.val.im| : ℕ) := Nat.le_ceil _
    _ ≤ ((G.sup (fun ρ : Zero => (Nat.ceil |ρ.val.im| : ℕ)) : ℕ) : ℝ) := by exact_mod_cast hle
    _ ≤ N := by exact_mod_cast hN

/-- The corresponding finite sets of the multiplicity index. -/
noncomputable def idxUpTo (N : ℕ) : Finset ZD.MultiZeroIdx :=
  (zerosUpTo N).sigma (fun ρ => (Finset.univ : Finset (Fin (ZD.xiOrderNat ρ.val))))

theorem tendsto_idxUpTo : Tendsto idxUpTo atTop atTop := by
  rw [Filter.tendsto_atTop_atTop]
  intro F
  obtain ⟨N₀, hN₀⟩ := Filter.tendsto_atTop_atTop.mp tendsto_zerosUpTo (F.image (fun p => p.1))
  refine ⟨N₀, fun N hN p hp => ?_⟩
  rw [idxUpTo, Finset.mem_sigma]
  exact ⟨hN₀ N hN (Finset.mem_image_of_mem _ hp), Finset.mem_univ _⟩

theorem prod_idxUpTo (N : ℕ) (f : Zero → ℂ) :
    ∏ p ∈ idxUpTo N, f p.1 = ∏ ρ ∈ zerosUpTo N, f ρ ^ (ZD.xiOrderNat ρ.val) := by
  rw [idxUpTo, Finset.prod_sigma]
  simp [Finset.prod_const]

/-! ### Convergence of the finite products -/

theorem tendstoLocallyUniformly_prod :
    TendstoLocallyUniformly (fun N z => ∏ p ∈ idxUpTo N, (1 + ZD.xiWeierstrassTerm p.1.val z))
      ZD.xiProductMult atTop := by
  have h : TendstoLocallyUniformlyOn
      (fun F : Finset ZD.MultiZeroIdx => fun z => ∏ p ∈ F, (1 + ZD.xiWeierstrassTerm p.1.val z))
      ZD.xiProductMult atTop univ :=
    ZD.xiProductMult_multipliableLocallyUniformlyOn_univ.hasProdLocallyUniformlyOn
  rw [← tendstoLocallyUniformlyOn_univ]
  intro u hu z hz
  obtain ⟨t, ht, hF⟩ := h u hu z hz
  exact ⟨t, ht, tendsto_idxUpTo.eventually hF⟩

/-- Multiplying by a fixed continuous function preserves locally uniform convergence. -/
theorem tendstoLocallyUniformly_mul_left {F : ℕ → ℂ → ℂ} {f g : ℂ → ℂ} (hg : Continuous g)
    (hF : TendstoLocallyUniformly F f atTop) :
    TendstoLocallyUniformly (fun n z => g z * F n z) (fun z => g z * f z) atTop := by
  rw [tendstoLocallyUniformly_iff_forall_isCompact] at hF ⊢
  intro K hK
  obtain ⟨M₀, hM₀⟩ := (hK.image hg).isBounded.exists_norm_le
  set M : ℝ := max M₀ 0 with hMdef
  have hM : ∀ y ∈ g '' K, ‖y‖ ≤ M := fun y hy => (hM₀ y hy).trans (le_max_left _ _)
  have hM0 : 0 ≤ M := le_max_right _ _
  have hFK := Metric.tendstoUniformlyOn_iff.mp (hF K hK)
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  filter_upwards [hFK (ε / (M + 1)) (by positivity)] with n hn z hz
  rw [dist_eq_norm, ← mul_sub, norm_mul]
  have hgz : ‖g z‖ ≤ M := hM (g z) (mem_image_of_mem g hz)
  have h1 := hn z hz
  rw [dist_eq_norm] at h1
  calc ‖g z‖ * ‖f z - F n z‖ ≤ M * (ε / (M + 1)) :=
        mul_le_mul hgz h1.le (norm_nonneg _) hM0
    _ < ε := by
        rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
        nlinarith

/-- The sequence `E_N(z) = e^{A s + B} ∏_{idxUpTo N}(…)(s)`, `s = ½ + iz`. -/
noncomputable def Eseq (N : ℕ) (z : ℂ) : ℂ :=
  Complex.exp (xiHadamardConst * (1 / 2 + I * z) + hadamardB) *
    ∏ p ∈ idxUpTo N, (1 + ZD.xiWeierstrassTerm p.1.val (1 / 2 + I * z))

theorem tendstoLocallyUniformly_Eseq : TendstoLocallyUniformly Eseq xiSection atTop := by
  have h1 := tendstoLocallyUniformly_mul_left
    (g := fun z => Complex.exp (xiHadamardConst * z + hadamardB)) (by fun_prop) tendstoLocallyUniformly_prod
  have h2 := h1.comp (fun z : ℂ => 1 / 2 + I * z) (by fun_prop)
  refine (h2.congr fun N z => rfl).congr_right fun z => ?_
  simp only [Function.comp_apply, xiSection]
  rw [riemannXi_eq_factor]

/-! ### The factorization of the finite products at `s = ½ + iz` -/

theorem factor_eq (ρ : Zero) (z : ℂ) :
    1 + ZD.xiWeierstrassTerm ρ.val (1 / 2 + I * z) =
      (I * w ρ / ρ.val) * (1 - z / w ρ) * Complex.exp ((1 / 2 + I * z) / ρ.val) := by
  rw [ZD.one_add_xiWeierstrassTerm, ZD.xiWeierstrassFactor]
  have hρ := val_ne_zero ρ
  have hw := w_ne_zero ρ
  congr 1
  have h1 : (I * w ρ / ρ.val) * (1 - z / w ρ) = (I * w ρ - I * z) / ρ.val := by
    field_simp
  rw [h1, I_mul_w]
  field_simp
  ring

/-- `D_N = ∏ (i w_ρ/ρ)^{m_ρ}`. -/
noncomputable def Dconst (N : ℕ) : ℂ := ∏ ρ ∈ zerosUpTo N, (I * w ρ / ρ.val) ^ (ZD.xiOrderNat ρ.val)
/-- `Q_N(z) = ∏ (1 − z/w_ρ)^{m_ρ}`. -/
noncomputable def Qfun (N : ℕ) (z : ℂ) : ℂ := ∏ ρ ∈ zerosUpTo N, (1 - z / w ρ) ^ (ZD.xiOrderNat ρ.val)
/-- `c_N = Σ m_ρ/ρ`. -/
noncomputable def cN (N : ℕ) : ℂ := ∑ ρ ∈ zerosUpTo N, (ZD.xiOrderNat ρ.val : ℂ) / ρ.val
/-- `d_N = A + c_N`. -/
noncomputable def dN (N : ℕ) : ℂ := xiHadamardConst + cN N
/-- `κ_N = e^{(A + c_N)/2 + B} D_N`. -/
noncomputable def kappa (N : ℕ) : ℂ := Complex.exp (dN N / 2 + hadamardB) * Dconst N

theorem prod_factor (N : ℕ) (z : ℂ) :
    ∏ p ∈ idxUpTo N, (1 + ZD.xiWeierstrassTerm p.1.val (1 / 2 + I * z)) =
      Dconst N * Qfun N z * Complex.exp ((1 / 2 + I * z) * cN N) := by
  rw [show (∏ p ∈ idxUpTo N, (1 + ZD.xiWeierstrassTerm p.1.val (1 / 2 + I * z))) =
      ∏ ρ ∈ zerosUpTo N, (1 + ZD.xiWeierstrassTerm ρ.val (1 / 2 + I * z)) ^ (ZD.xiOrderNat ρ.val)
    from prod_idxUpTo N (fun ρ => 1 + ZD.xiWeierstrassTerm ρ.val (1 / 2 + I * z))]
  simp_rw [factor_eq, mul_pow, Finset.prod_mul_distrib]
  unfold Dconst Qfun cN
  congr 1
  rw [Finset.mul_sum, Complex.exp_sum]
  apply Finset.prod_congr rfl
  intro ρ _
  rw [← Complex.exp_nat_mul]
  congr 1
  ring

theorem Eseq_eq (N : ℕ) (z : ℂ) : Eseq N z = kappa N * Complex.exp (I * z * dN N) * Qfun N z := by
  unfold Eseq kappa dN
  rw [prod_factor]
  rw [show Complex.exp (xiHadamardConst * (1 / 2 + I * z) + hadamardB) *
      (Dconst N * Qfun N z * Complex.exp ((1 / 2 + I * z) * cN N)) =
      (Complex.exp (xiHadamardConst * (1 / 2 + I * z) + hadamardB) * Complex.exp ((1 / 2 + I * z) * cN N)) *
        Dconst N * Qfun N z by ring]
  rw [← Complex.exp_add]
  rw [show Complex.exp ((xiHadamardConst + cN N) / 2 + hadamardB) * Dconst N *
      Complex.exp (I * z * (xiHadamardConst + cN N)) * Qfun N z =
      (Complex.exp ((xiHadamardConst + cN N) / 2 + hadamardB) * Complex.exp (I * z * (xiHadamardConst + cN N))) *
        Dconst N * Qfun N z by ring]
  rw [← Complex.exp_add]
  congr 3
  ring

/-! ### The limits of `c_N` and `κ_N` -/

theorem cN_eq (N : ℕ) :
    2 * cN N = ∑ ρ ∈ zerosUpTo N, (ZD.xiOrderNat ρ.val : ℂ) * (1 / ρ.val + 1 / (1 - ρ.val)) := by
  have hmirror : ∑ ρ ∈ zerosUpTo N, (ZD.xiOrderNat ρ.val : ℂ) / ρ.val =
      ∑ ρ ∈ zerosUpTo N, (ZD.xiOrderNat ρ.val : ℂ) / (1 - ρ.val) := by
    refine Finset.sum_equiv mirrorZero (fun ρ => (mirrorZero_mem_zerosUpTo ρ).symm) ?_
    intro ρ _
    rw [xiOrderNat_mirrorZero, mirrorZero_val, sub_sub_cancel]
  unfold cN
  rw [two_mul]
  nth_rewrite 2 [hmirror]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro ρ _
  ring

theorem tendsto_cN : Tendsto cN atTop (𝓝 (-xiHadamardConst)) := by
  have hs : Summable (fun ρ : Zero => (ZD.xiOrderNat ρ.val : ℂ) * (1 / ρ.val + 1 / (1 - ρ.val))) := by
    have := summable_reflect_family 0
    simpa using this
  have hT : Tendsto (fun s : Finset Zero => ∑ ρ ∈ s, (ZD.xiOrderNat ρ.val : ℂ) * (1 / ρ.val + 1 / (1 - ρ.val)))
      atTop (𝓝 (∑' ρ : Zero, (ZD.xiOrderNat ρ.val : ℂ) * (1 / ρ.val + 1 / (1 - ρ.val)))) := hs.hasSum
  have htot : ∑' ρ : Zero, (ZD.xiOrderNat ρ.val : ℂ) * (1 / ρ.val + 1 / (1 - ρ.val)) = -2 * xiHadamardConst := by
    have h := reflection_const_eq_zero
    have hc : ∑' ρ : Zero, (ZD.xiOrderNat ρ.val : ℂ) * (1 / ρ.val + 1 / (1 - ρ.val)) =
        ∑' ρ : Zero, (ZD.xiOrderNat ρ.val : ℂ) * (1 / (1 - ρ.val) + 1 / ρ.val) := by
      congr 1; funext ρ; ring
    rw [hc]
    linear_combination h
  have h2 : Tendsto (fun N => 2 * cN N) atTop (𝓝 (-2 * xiHadamardConst)) := by
    rw [← htot]
    refine (hT.comp tendsto_zerosUpTo).congr fun N => ?_
    simp only [Function.comp_apply, cN_eq]
  have h3 := h2.const_mul (1 / 2 : ℂ)
  have hfun : (fun N => (1 / 2 : ℂ) * (2 * cN N)) = cN := by funext N; ring
  rw [hfun] at h3
  convert h3 using 2
  ring

theorem tendsto_dN : Tendsto dN atTop (𝓝 0) := by
  have := tendsto_cN.const_add xiHadamardConst
  have hfun : dN = fun N => xiHadamardConst + cN N := rfl
  rw [hfun]
  simpa using this

theorem Qfun_zero (N : ℕ) : Qfun N 0 = 1 := by
  unfold Qfun
  simp

theorem tendsto_kappa : Tendsto kappa atTop (𝓝 (xiSection 0)) := by
  have h := (tendstoLocallyUniformlyOn_univ.mpr tendstoLocallyUniformly_Eseq).tendsto_at (mem_univ (0 : ℂ))
  refine h.congr fun N => ?_
  rw [Eseq_eq, Qfun_zero]
  simp

/-! ### The scaled convergence `Ξ(0) Q_N → Ξ` -/

/-- If `E_n → f` uniformly on `K`, `a_n → 1`, and `g_n → 1` uniformly on `K`, then `a_n g_n E_n → f` uniformly on
`K` (`f` bounded on `K`). -/
theorem tendstoUniformlyOn_scale {E : ℕ → ℂ → ℂ} {f : ℂ → ℂ} {K : Set ℂ} {B : ℝ} (hB : 0 ≤ B)
    (hf : ∀ z ∈ K, ‖f z‖ ≤ B) (hE : TendstoUniformlyOn E f atTop K) {a : ℕ → ℂ} (ha : Tendsto a atTop (𝓝 1))
    {g : ℕ → ℂ → ℂ} (hg : TendstoUniformlyOn g (fun _ => 1) atTop K) :
    TendstoUniformlyOn (fun n z => a n * g n z * E n z) f atTop K := by
  rw [Metric.tendstoUniformlyOn_iff] at hE hg ⊢
  intro ε hε
  set δ : ℝ := min 1 (ε / (3 * B + 5)) with hδ
  have hδpos : 0 < δ := lt_min one_pos (by positivity)
  have hδ1 : δ ≤ 1 := min_le_left _ _
  have hδ2 : δ ≤ ε / (3 * B + 5) := min_le_right _ _
  have ha' := Metric.tendsto_nhds.mp ha δ hδpos
  filter_upwards [hE δ hδpos, hg δ hδpos, ha'] with n hEn hgn han z hz
  have h1 : ‖f z - E n z‖ < δ := by rw [← dist_eq_norm]; exact hEn z hz
  have h2 : ‖g n z - 1‖ < δ := by rw [← dist_eq_norm, dist_comm]; exact hgn z hz
  have h3 : ‖a n - 1‖ < δ := by rw [← dist_eq_norm]; exact han
  have ha2 : ‖a n‖ ≤ 2 := by
    have := norm_sub_norm_le (a n) 1
    rw [norm_one] at this
    linarith
  have hg2 : ‖g n z‖ ≤ 2 := by
    have := norm_sub_norm_le (g n z) 1
    rw [norm_one] at this
    linarith
  have hfz := hf z hz
  rw [dist_eq_norm]
  have hdecomp : f z - a n * g n z * E n z = a n * g n z * (f z - E n z) + (1 - a n * g n z) * f z := by ring
  have hag : ‖1 - a n * g n z‖ ≤ ‖a n‖ * ‖g n z - 1‖ + ‖a n - 1‖ := by
    have : 1 - a n * g n z = -(a n * (g n z - 1)) - (a n - 1) := by ring
    rw [this]
    calc ‖-(a n * (g n z - 1)) - (a n - 1)‖ ≤ ‖-(a n * (g n z - 1))‖ + ‖a n - 1‖ := norm_sub_le _ _
      _ = ‖a n‖ * ‖g n z - 1‖ + ‖a n - 1‖ := by rw [norm_neg, norm_mul]
  calc ‖f z - a n * g n z * E n z‖
      = ‖a n * g n z * (f z - E n z) + (1 - a n * g n z) * f z‖ := by rw [hdecomp]
    _ ≤ ‖a n * g n z * (f z - E n z)‖ + ‖(1 - a n * g n z) * f z‖ := norm_add_le _ _
    _ = ‖a n‖ * ‖g n z‖ * ‖f z - E n z‖ + ‖1 - a n * g n z‖ * ‖f z‖ := by rw [norm_mul, norm_mul, norm_mul]
    _ ≤ 2 * 2 * δ + (2 * δ + δ) * B := by
        have hb1 : ‖a n‖ * ‖g n z‖ * ‖f z - E n z‖ ≤ 2 * 2 * δ :=
          mul_le_mul (mul_le_mul ha2 hg2 (norm_nonneg _) (by norm_num)) h1.le (norm_nonneg _) (by norm_num)
        have hag2 : ‖a n‖ * ‖g n z - 1‖ + ‖a n - 1‖ ≤ 2 * δ + δ :=
          add_le_add (mul_le_mul ha2 h2.le (norm_nonneg _) (by norm_num)) h3.le
        have hb2 : ‖1 - a n * g n z‖ * ‖f z‖ ≤ (2 * δ + δ) * B :=
          mul_le_mul (hag.trans hag2) hfz (norm_nonneg _) (by positivity)
        exact add_le_add hb1 hb2
    _ = δ * (3 * B + 4) := by ring
    _ < ε := by
        calc δ * (3 * B + 4) ≤ (ε / (3 * B + 5)) * (3 * B + 4) :=
              mul_le_mul_of_nonneg_right hδ2 (by positivity)
          _ < ε := by
              rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
              nlinarith

theorem tendstoUniformlyOn_exp_neg {K : Set ℂ} {R : ℝ} (hR : 0 ≤ R) (hK : ∀ z ∈ K, ‖z‖ ≤ R) :
    TendstoUniformlyOn (fun N z => Complex.exp (-(I * z * dN N))) (fun _ => 1) atTop K := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have hd := Metric.tendsto_nhds.mp tendsto_dN (min (1 / (R + 1)) (ε / (2 * R + 2))) (by positivity)
  filter_upwards [hd] with N hN z hz
  rw [dist_zero_right] at hN
  have hzR := hK z hz
  have hsmall : ‖-(I * z * dN N)‖ ≤ 1 := by
    rw [norm_neg, norm_mul, norm_mul, Complex.norm_I, one_mul]
    calc ‖z‖ * ‖dN N‖ ≤ R * (1 / (R + 1)) :=
          mul_le_mul hzR ((hN.trans_le (min_le_left _ _)).le) (norm_nonneg _) hR
      _ ≤ 1 := by rw [mul_one_div, div_le_one (by positivity)]; linarith
  rw [dist_comm, dist_eq_norm]
  calc ‖Complex.exp (-(I * z * dN N)) - 1‖ ≤ 2 * ‖-(I * z * dN N)‖ := Complex.norm_exp_sub_one_le hsmall
    _ = 2 * (‖z‖ * ‖dN N‖) := by rw [norm_neg, norm_mul, norm_mul, Complex.norm_I, one_mul]
    _ ≤ 2 * (R * (ε / (2 * R + 2))) := by
        gcongr
        exact (hN.trans_le (min_le_right _ _)).le
    _ < ε := by
        rw [show 2 * (R * (ε / (2 * R + 2))) = ε * (2 * R / (2 * R + 2)) by ring]
        have : 2 * R / (2 * R + 2) < 1 := by rw [div_lt_one (by positivity)]; linarith
        nlinarith

theorem continuous_xiSection : Continuous xiSection := by
  have : xiSection = CriticalLinePhasor.XiKernel.Ktrans := funext xiSection_eq_Ktrans
  rw [this]
  exact differentiable_Ktrans.continuous

theorem tendstoLocallyUniformly_final :
    TendstoLocallyUniformly (fun N z => xiSection 0 * Qfun N z) xiSection atTop := by
  have hE : TendstoLocallyUniformly (fun N z => kappa N * Complex.exp (I * z * dN N) * Qfun N z) xiSection atTop :=
    tendstoLocallyUniformly_Eseq.congr fun N z => Eseq_eq N z
  have hΞ0 := xiSection_zero_ne_zero
  have hκne : ∀ᶠ N in atTop, kappa N ≠ 0 := tendsto_kappa.eventually_ne hΞ0
  have ha : Tendsto (fun N => xiSection 0 / kappa N) atTop (𝓝 1) := by
    have := (tendsto_const_nhds (x := xiSection 0)).div tendsto_kappa hΞ0
    rwa [div_self hΞ0] at this
  rw [tendstoLocallyUniformly_iff_forall_isCompact] at hE ⊢
  intro K hK
  obtain ⟨R, hR⟩ := hK.isBounded.exists_norm_le
  obtain ⟨B, hB⟩ := (hK.image continuous_xiSection).isBounded.exists_norm_le
  have hB' : ∀ z ∈ K, ‖xiSection z‖ ≤ max B 0 := fun z hz =>
    (hB _ (mem_image_of_mem _ hz)).trans (le_max_left _ _)
  have hR' : ∀ z ∈ K, ‖z‖ ≤ max R 0 := fun z hz => (hR z hz).trans (le_max_left _ _)
  have hg := tendstoUniformlyOn_exp_neg (K := K) (le_max_right R 0) hR'
  have hmain := tendstoUniformlyOn_scale (le_max_right B 0) hB' (hE K hK) ha hg
  refine hmain.congr ?_
  filter_upwards [hκne] with N hN z _
  have hexp : Complex.exp (I * z * dN N) ≠ 0 := Complex.exp_ne_zero _
  show xiSection 0 / kappa N * Complex.exp (-(I * z * dN N)) *
    (kappa N * Complex.exp (I * z * dN N) * Qfun N z) = xiSection 0 * Qfun N z
  rw [Complex.exp_neg]
  field_simp

/-! ### The real polynomials -/

/-- `Q_N` as a complex polynomial. -/
noncomputable def Qpoly (N : ℕ) : ℂ[X] :=
  ∏ ρ ∈ zerosUpTo N, (1 - C (w ρ)⁻¹ * X) ^ (ZD.xiOrderNat ρ.val)

theorem Qpoly_eval (N : ℕ) (z : ℂ) : (Qpoly N).eval z = Qfun N z := by
  unfold Qpoly Qfun
  rw [eval_prod]
  apply Finset.prod_congr rfl
  intro ρ _
  simp only [eval_pow, eval_sub, eval_one, eval_mul, eval_C, eval_X]
  rw [div_eq_mul_inv, mul_comm]

theorem Qpoly_map_conj (N : ℕ) : (Qpoly N).map (starRingEnd ℂ) = Qpoly N := by
  unfold Qpoly
  rw [Polynomial.map_prod]
  simp only [Polynomial.map_pow, Polynomial.map_sub, Polynomial.map_one, Polynomial.map_mul, map_C, map_X,
    map_inv₀]
  refine Finset.prod_equiv (conjZero.trans mirrorZero) ?_ ?_
  · intro ρ
    rw [Equiv.trans_apply, mirrorZero_mem_zerosUpTo, conjZero_mem_zerosUpTo]
  · intro ρ _
    rw [Equiv.trans_apply, xiOrderNat_mirrorZero, xiOrderNat_conjZero, w_conj]

theorem Qpoly_mem_lifts (N : ℕ) : Qpoly N ∈ lifts (algebraMap ℝ ℂ) := by
  rw [lifts_iff_coeff_lifts]
  intro n
  refine ⟨((Qpoly N).coeff n).re, ?_⟩
  have h := congrArg (fun p : ℂ[X] => p.coeff n) (Qpoly_map_conj N)
  simp only [coeff_map] at h
  have him : ((Qpoly N).coeff n).im = 0 := Complex.conj_eq_iff_im.mp h
  apply Complex.ext <;> simp [him]

/-- The real polynomial with `aeval z (Preal N) = Q_N(z)`. -/
noncomputable def Preal (N : ℕ) : ℝ[X] := Classical.choose ((mem_lifts _).mp (Qpoly_mem_lifts N))

theorem Preal_map (N : ℕ) : (Preal N).map (algebraMap ℝ ℂ) = Qpoly N :=
  Classical.choose_spec ((mem_lifts _).mp (Qpoly_mem_lifts N))

theorem aeval_Preal (N : ℕ) (z : ℂ) : aeval z (Preal N) = Qfun N z := by
  rw [aeval_eq_eval_map, Preal_map, Qpoly_eval]

theorem xiSection_zero_im : (xiSection 0).im = 0 := by
  have h := riemannXi_conj (1 / 2 : ℂ)
  have hc : (starRingEnd ℂ) (1 / 2 : ℂ) = 1 / 2 := by
    rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; ring, Complex.conj_ofReal]
  rw [hc] at h
  have : (xiSection 0) = ZD.riemannXi (1 / 2) := by simp [xiSection]
  rw [this]
  exact Complex.conj_eq_iff_im.mp h.symm

theorem xiSection_zero_eq_re : ((xiSection 0).re : ℂ) = xiSection 0 := by
  apply Complex.ext <;> simp [xiSection_zero_im]

/-- The scaled real polynomial `Ξ(0) · Preal N`. -/
noncomputable def Pscaled (N : ℕ) : ℝ[X] := C ((xiSection 0).re) * Preal N

theorem aeval_Pscaled (N : ℕ) (z : ℂ) : aeval z (Pscaled N) = xiSection 0 * Qfun N z := by
  unfold Pscaled
  rw [map_mul, aeval_C, aeval_Preal]
  simp [xiSection_zero_eq_re]

theorem Pscaled_ne_zero (N : ℕ) : Pscaled N ≠ 0 := by
  intro h
  have := aeval_Pscaled N 0
  rw [h, map_zero, Qfun_zero, mul_one] at this
  exact xiSection_zero_ne_zero this.symm

theorem Pscaled_zeros (N : ℕ) (z : ℂ) (hz : aeval z (Pscaled N) = 0) : z.im ^ 2 ≤ 1 / 4 := by
  rw [aeval_Pscaled] at hz
  have hQ : Qfun N z = 0 := (mul_eq_zero.mp hz).resolve_left xiSection_zero_ne_zero
  unfold Qfun at hQ
  obtain ⟨ρ, _, hρ⟩ := Finset.prod_eq_zero_iff.mp hQ
  have hm : ZD.xiOrderNat ρ.val ≠ 0 := (ZD.xiOrderNat_pos_of_mem_NontrivialZeros ρ.2).ne'
  have h1 : 1 - z / w ρ = 0 := pow_eq_zero_iff hm |>.mp hρ
  have hzw : z = w ρ := by
    have := w_ne_zero ρ
    field_simp at h1
    linear_combination -h1
  rw [hzw]
  exact w_im_sq_le ρ

/-- **`Ξ` is a locally uniform limit of nonzero real polynomials with zeros in the closed strip `(Im)² ≤ ¼`.** -/
theorem xiSection_stripClass : StripClass (1 / 4) xiSection := by
  refine ⟨Pscaled, Pscaled_ne_zero, Pscaled_zeros, ?_⟩
  refine tendstoLocallyUniformly_final.congr fun N z => ?_
  rw [aeval_Pscaled]

end CriticalLinePhasor.XiApprox

#print axioms CriticalLinePhasor.XiApprox.hadamard_factorization_const
#print axioms CriticalLinePhasor.XiApprox.tendstoLocallyUniformly_final
#print axioms CriticalLinePhasor.XiApprox.xiSection_stripClass
