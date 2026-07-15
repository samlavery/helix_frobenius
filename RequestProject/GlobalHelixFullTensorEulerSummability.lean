import RequestProject.GlobalHelixExponentLatticeSummability
import RequestProject.GlobalHelixZeroModeGaussian

open Real Complex Filter Asymptotics MeasureTheory
open scoped BigOperators

namespace CriticalLinePhasor.GlobalHelix

/-- Rapid decay of the zero-mode Gaussian kernel, restricted to every positive
three-dimensional helix-height ray. -/
theorem exists_zeroModeGaussianKernel_ray_rpow_bound
    {c x : ℝ} (hc : 0 < c) (hx : 0 < x) (M : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ H : ℝ, 1 ≤ H →
      ‖zeroModeGaussianKernel c (H * x)‖ ≤ C * H ^ (-(M : ℝ)) := by
  have hrapid := zeroModeGaussianKernel_rapid hc (-(M : ℝ))
  rw [isBigO_iff] at hrapid
  rcases hrapid with ⟨A, hA⟩
  rcases (eventually_atTop.1 hA) with ⟨T₀, hT₀⟩
  let T : ℝ := max T₀ x
  let R : ℝ := T / x
  have hTx : x ≤ T := le_max_right _ _
  have hT₀T : T₀ ≤ T := le_max_left _ _
  have hR1 : 1 ≤ R := by
    dsimp [R]
    exact (le_div_iff₀ hx).2 (by simpa using hTx)
  have hkcomp : ContinuousOn (fun H : ℝ => zeroModeGaussianKernel c (H * x))
      (Set.Icc 1 R) := by
    exact (zeroModeGaussianKernel_continuousOn hc).comp
      (continuousOn_id.mul continuousOn_const) (fun H hH =>
        mul_pos (lt_of_lt_of_le zero_lt_one hH.1) hx)
  have hcont : ContinuousOn
      (fun H : ℝ => ‖zeroModeGaussianKernel c (H * x)‖ * H ^ M)
      (Set.Icc 1 R) := hkcomp.norm.mul (continuousOn_id.pow M)
  obtain ⟨D, hD⟩ := bddAbove_def.mp
    (IsCompact.bddAbove_image isCompact_Icc hcont)
  let C : ℝ := max D (A * x ^ (-(M : ℝ)))
  have hD0 : 0 ≤ D := by
    have hmem : (1 : ℝ) ∈ Set.Icc (1 : ℝ) R := ⟨le_rfl, hR1⟩
    have himg : ‖zeroModeGaussianKernel c (1 * x)‖ * (1 : ℝ) ^ M ∈
        (fun H : ℝ => ‖zeroModeGaussianKernel c (H * x)‖ * H ^ M) ''
          Set.Icc 1 R := ⟨1, hmem, rfl⟩
    exact (mul_nonneg (norm_nonneg _) (pow_nonneg zero_le_one _)).trans (hD _ himg)
  refine ⟨C, hD0.trans (le_max_left _ _), ?_⟩
  intro H hH
  have hHpos : 0 < H := zero_lt_one.trans_le hH
  by_cases hHR : H ≤ R
  · have hmem : H ∈ Set.Icc (1 : ℝ) R := ⟨hH, hHR⟩
    have himg : ‖zeroModeGaussianKernel c (H * x)‖ * H ^ M ∈
        (fun Y : ℝ => ‖zeroModeGaussianKernel c (Y * x)‖ * Y ^ M) ''
          Set.Icc 1 R := ⟨H, hmem, rfl⟩
    have hFC : ‖zeroModeGaussianKernel c (H * x)‖ * H ^ M ≤ C :=
      (hD _ himg).trans (le_max_left _ _)
    have hpowpos : 0 < H ^ M := pow_pos hHpos M
    have hrpow : H ^ (-(M : ℝ)) = (H ^ M)⁻¹ := by
      rw [Real.rpow_neg hHpos.le, Real.rpow_natCast]
    rw [hrpow]
    calc
      ‖zeroModeGaussianKernel c (H * x)‖ =
          (‖zeroModeGaussianKernel c (H * x)‖ * H ^ M) * (H ^ M)⁻¹ := by
            field_simp [hpowpos.ne']
      _ ≤ C * (H ^ M)⁻¹ :=
        mul_le_mul_of_nonneg_right hFC (inv_nonneg.mpr hpowpos.le)
  · have hRH : R < H := lt_of_not_ge hHR
    have hTHx : T < H * x := by
      have hRx : R * x = T := by
        dsimp [R]
        field_simp [hx.ne']
      rw [← hRx]
      exact mul_lt_mul_of_pos_right hRH hx
    have htail := hT₀ (H * x) (hT₀T.trans hTHx.le)
    have hHx : 0 < H * x := mul_pos hHpos hx
    rw [Real.norm_of_nonneg (Real.rpow_nonneg hHx.le _),
      Real.mul_rpow hHpos.le hx.le] at htail
    calc
      ‖zeroModeGaussianKernel c (H * x)‖
          ≤ A * (H ^ (-(M : ℝ)) * x ^ (-(M : ℝ))) := htail
      _ = (A * x ^ (-(M : ℝ))) * H ^ (-(M : ℝ)) := by ring
      _ ≤ C * H ^ (-(M : ℝ)) :=
        mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg hHpos.le _)

/-- Absolute summability of the nonnegative exponent sector of the tensor Euler
bank after coupling it to the three-dimensional zero-mode Gaussian kernel. -/
theorem summable_naturalTensorEuler_zeroModeTerm
    {V ι : Type*} [Fintype ι]
    (S : Finset V) (W : V → FiniteWeightFiber ι) (q : V → ℝ)
    (hq : ∀ v ∈ S, 1 < q v) {c x : ℝ} (hc : 0 < c) (hx : 0 < x) :
    Summable (fun k : (v : S) → ℕ =>
      (∏ v : S, localEulerCoeff (W v) (k v)) *
        zeroModeGaussianKernel c ((∏ v : S, q v ^ k v) * x)) := by
  let M : ℕ := Fintype.card ι + 2
  have hM : 0 < M := by omega
  have hs := summable_naturalTensorEulerCoeff_mul_height_rpow S W q hq M hM
  obtain ⟨C, hC0, hC⟩ := exists_zeroModeGaussianKernel_ray_rpow_bound hc hx M
  have hsC := hs.mul_left C
  apply Summable.of_norm_bounded hsC
  intro k
  rw [norm_mul]
  have hH1 : 1 ≤ ∏ v : S, q v ^ k v := by
    apply Finset.one_le_prod
    intro v hv
    exact one_le_pow₀ (le_of_lt (hq v v.property))
  calc
    ‖∏ v : S, localEulerCoeff (W v) (k v)‖ *
        ‖zeroModeGaussianKernel c ((∏ v : S, q v ^ k v) * x)‖
        ≤ ‖∏ v : S, localEulerCoeff (W v) (k v)‖ *
            (C * (∏ v : S, q v ^ k v) ^ (-(M : ℝ))) := by
          gcongr
          exact hC _ hH1
    _ = C * (‖∏ v : S, localEulerCoeff (W v) (k v)‖ *
          (∏ v : S, q v ^ k v) ^ (-(M : ℝ))) := by ring

/-- Natural exponent vectors are exactly the nonnegative integral exponent vectors. -/
def nonnegativeExponentEquiv {V : Type*} (S : Finset V) :
    ((v : S) → ℕ) ≃ {k : (v : S) → ℤ // ∀ v, 0 ≤ k v} where
  toFun k := ⟨fun v => (k v : ℤ), fun v => Int.natCast_nonneg _⟩
  invFun k := fun v => (k.1 v).toNat
  left_inv k := by
    funext v
    simp
  right_inv k := by
    apply Subtype.ext
    funext v
    exact Int.toNat_of_nonneg (k.2 v)

/-- Absolute summability of the full bilateral integral exponent lattice.  The
seed vanishes off the nonnegative sector, so this is the summability statement
used by the full 3D helix tensor bank. -/
theorem summable_fullTensorEuler_zeroModeTerm
    {V ι : Type*} [Fintype ι]
    (S : Finset V) (W : V → FiniteWeightFiber ι) (q : V → ℝ)
    (hq : ∀ v ∈ S, 1 < q v) {c x : ℝ} (hc : 0 < c) (hx : 0 < x) :
    Summable (fun k : (v : S) → ℤ =>
      bilateralTensorEulerSeed S W k *
        zeroModeGaussianKernel c (bilateralEulerHeight S q k * x)) := by
  let A : Set ((v : S) → ℤ) := {k | ∀ v, 0 ≤ k v}
  let F : ((v : S) → ℤ) → ℂ := fun k =>
    (∏ v : S, localEulerCoeff (W v) (k v).toNat) *
      zeroModeGaussianKernel c (bilateralEulerHeight S q k * x)
  have hsNat := summable_naturalTensorEuler_zeroModeTerm S W q hq hc hx
  have hsSub : Summable (fun k : A => F k) := by
    apply (nonnegativeExponentEquiv S).summable_iff.mp
    convert hsNat using 1
    funext k
    simp [F, A, nonnegativeExponentEquiv, bilateralEulerHeight]
  have hi : Summable (A.indicator F) := summable_subtype_iff_indicator.mp hsSub
  apply hi.congr
  intro k
  by_cases hk : ∀ v, 0 ≤ k v
  · have hmem : k ∈ A := by simpa [A] using hk
    rw [Set.indicator_of_mem hmem]
    unfold F bilateralTensorEulerSeed
    rw [if_pos hk]
  · have hmem : k ∉ A := by simpa [A] using hk
    rw [Set.indicator_of_notMem hmem]
    unfold bilateralTensorEulerSeed
    rw [if_neg hk]
    simp

/-- The 3D helix reflection converts the rapid large-height estimate into a
global polynomial bound on every positive height. -/
theorem exists_zeroModeGaussianKernel_global_rpow_bound
    {c : ℝ} (hc : 0 < c) (M : ℕ) (hM : 1 ≤ M) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 0 < x →
      ‖zeroModeGaussianKernel c x‖ ≤ C * x ^ (-(M : ℝ)) := by
  obtain ⟨C, hC0, hC⟩ :=
    exists_zeroModeGaussianKernel_ray_rpow_bound hc (x := 1) zero_lt_one M
  refine ⟨C, hC0, ?_⟩
  intro x hx
  by_cases hx1 : 1 ≤ x
  · simpa using hC x hx1
  · have hxlt : x < 1 := lt_of_not_ge hx1
    have hxin : 1 ≤ 1 / x := (le_div_iff₀ hx).2 (by simpa using hxlt.le)
    have htail := hC (1 / x) hxin
    simp only [mul_one] at htail
    rw [zeroModeGaussianKernel_reflection hc hx, norm_mul]
    have hscaleNorm :
        ‖(((1 / x ^ (1 / 2 : ℝ) : ℝ) : ℂ))‖ = 1 / x ^ (1 / 2 : ℝ) := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg]
      exact one_div_nonneg.mpr (Real.rpow_nonneg hx.le _)
    rw [hscaleNorm]
    calc
      1 / x ^ (1 / 2 : ℝ) * ‖zeroModeGaussianKernel c (1 / x)‖
          ≤ 1 / x ^ (1 / 2 : ℝ) * (C * (1 / x) ^ (-(M : ℝ))) := by
            gcongr
      _ = C * x ^ ((M : ℝ) - 1 / 2) := by
        have hhalf : (x ^ (1 / 2 : ℝ))⁻¹ = x ^ (-(1 / 2 : ℝ)) := by
          rw [Real.rpow_neg hx.le]
        have hinvM : (1 / x) ^ (-(M : ℝ)) = x ^ (M : ℝ) := by
          rw [one_div, Real.inv_rpow hx.le, Real.rpow_neg hx.le, inv_inv]
        rw [one_div, hhalf, hinvM]
        calc
          x ^ (-(1 / 2 : ℝ)) * (C * x ^ (M : ℝ)) =
              C * (x ^ (-(1 / 2 : ℝ)) * x ^ (M : ℝ)) := by ring
          _ = C * x ^ ((M : ℝ) - 1 / 2) := by
            rw [← Real.rpow_add hx]
            congr 2
            ring
      _ ≤ C * x ^ (-(M : ℝ)) := by
        apply mul_le_mul_of_nonneg_left _ hC0
        apply Real.rpow_le_rpow_of_exponent_ge hx hxlt.le
        have hMreal : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
        linarith

/-- The polynomial-height majorant remains summable after extending the
nonnegative exponent sector by zero to the full integral lattice. -/
theorem summable_fullTensorEulerCoeff_mul_height_rpow
    {V ι : Type*} [Fintype ι]
    (S : Finset V) (W : V → FiniteWeightFiber ι) (q : V → ℝ)
    (hq : ∀ v ∈ S, 1 < q v) (M : ℕ) (hM : 0 < M) :
    Summable (fun k : (v : S) → ℤ =>
      ‖bilateralTensorEulerSeed S W k‖ *
        bilateralEulerHeight S q k ^ (-(M : ℝ))) := by
  let A : Set ((v : S) → ℤ) := {k | ∀ v, 0 ≤ k v}
  let F : ((v : S) → ℤ) → ℝ := fun k =>
    ‖∏ v : S, localEulerCoeff (W v) (k v).toNat‖ *
      bilateralEulerHeight S q k ^ (-(M : ℝ))
  have hsNat := summable_naturalTensorEulerCoeff_mul_height_rpow S W q hq M hM
  have hsSub : Summable (fun k : A => F k) := by
    apply (nonnegativeExponentEquiv S).summable_iff.mp
    convert hsNat using 1
    funext k
    simp [F, A, nonnegativeExponentEquiv, bilateralEulerHeight]
  have hi : Summable (A.indicator F) := summable_subtype_iff_indicator.mp hsSub
  apply hi.congr
  intro k
  by_cases hk : ∀ v, 0 ≤ k v
  · have hmem : k ∈ A := by simpa [A] using hk
    rw [Set.indicator_of_mem hmem]
    unfold F bilateralTensorEulerSeed
    rw [if_pos hk]
  · have hmem : k ∉ A := by simpa [A] using hk
    rw [Set.indicator_of_notMem hmem]
    unfold bilateralTensorEulerSeed
    rw [if_neg hk]
    simp

/-- On each compact positive-height interval, the full 3D tensor-Euler theta
bank is the uniform limit of its finite exponent-lattice banks. -/
theorem fullTensorEulerZeroModeTheta_continuousOn_Icc
    {V ι : Type*} [Fintype ι]
    (S : Finset V) (W : V → FiniteWeightFiber ι) (q : V → ℝ)
    (hq : ∀ v ∈ S, 1 < q v) {c a b : ℝ} (hc : 0 < c) (ha : 0 < a) :
    ContinuousOn
      (indexedZeroModeGaussianTheta
        (bilateralTensorEulerSeed S W) (bilateralEulerHeight S q) c)
      (Set.Icc a b) := by
  let H : ((v : S) → ℤ) → ℝ := bilateralEulerHeight S q
  let coeff : ((v : S) → ℤ) → ℂ := bilateralTensorEulerSeed S W
  have hHpos : ∀ k, 0 < H k := fun k =>
    bilateralEulerHeight_pos S q (fun v hv => zero_lt_one.trans (hq v hv)) k
  obtain ⟨C, hC0, hC⟩ :=
    exists_zeroModeGaussianKernel_global_rpow_bound hc 1 (by omega)
  have hs := summable_fullTensorEulerCoeff_mul_height_rpow S W q hq 1 (by omega)
  have hsu : Summable (fun k =>
      (C * a ^ (-1 : ℝ)) * (‖coeff k‖ * H k ^ (-1 : ℝ))) := by
    simpa [coeff, H] using hs.mul_left (C * a ^ (-1 : ℝ))
  unfold indexedZeroModeGaussianTheta indexedTheta
  apply continuousOn_tsum
  · intro k
    exact continuousOn_const.mul ((zeroModeGaussianKernel_continuousOn hc).comp
      (continuousOn_const.mul continuousOn_id) (fun x hx =>
        mul_pos (hHpos k) (ha.trans_le hx.1)))
  · exact hsu
  · intro k x hx
    rw [norm_mul]
    have hHx : 0 < H k * x := mul_pos (hHpos k) (ha.trans_le hx.1)
    have hHa : 0 < H k * a := mul_pos (hHpos k) ha
    have hbase : H k * a ≤ H k * x :=
      mul_le_mul_of_nonneg_left hx.1 (hHpos k).le
    have hpow : (H k * x) ^ (-1 : ℝ) ≤ (H k * a) ^ (-1 : ℝ) :=
      Real.rpow_le_rpow_of_nonpos hHa hbase (by norm_num)
    calc
      ‖coeff k‖ * ‖zeroModeGaussianKernel c (H k * x)‖
          ≤ ‖coeff k‖ * (C * (H k * x) ^ (-1 : ℝ)) := by
            gcongr
            simpa using hC _ hHx
      _ ≤ ‖coeff k‖ * (C * (H k * a) ^ (-1 : ℝ)) := by
            gcongr
      _ = (C * a ^ (-1 : ℝ)) * (‖coeff k‖ * H k ^ (-1 : ℝ)) := by
            rw [Real.mul_rpow (hHpos k).le ha.le]
            ring

/-- The infinite full-lattice scalar projection is continuous throughout the
positive 3D multiplicative-height chart. -/
theorem fullTensorEulerZeroModeTheta_continuousOn
    {V ι : Type*} [Fintype ι]
    (S : Finset V) (W : V → FiniteWeightFiber ι) (q : V → ℝ)
    (hq : ∀ v ∈ S, 1 < q v) {c : ℝ} (hc : 0 < c) :
    ContinuousOn
      (indexedZeroModeGaussianTheta
        (bilateralTensorEulerSeed S W) (bilateralEulerHeight S q) c)
      (Set.Ioi 0) := by
  apply continuousOn_of_forall_continuousAt
  intro x hx
  simp only [Set.mem_Ioi] at hx
  have hlocal := fullTensorEulerZeroModeTheta_continuousOn_Icc
    S W q hq hc (a := x / 2) (b := 2 * x) (by linarith)
  have hxmem : x ∈ Set.Icc (x / 2) (2 * x) := by constructor <;> linarith
  exact (hlocal x hxmem).continuousAt (Icc_mem_nhds (by linarith) (by linarith))

/-- The continuous infinite 3D readout is locally integrable on positive
multiplicative heights. -/
theorem fullTensorEulerZeroModeTheta_locallyIntegrableOn
    {V ι : Type*} [Fintype ι]
    (S : Finset V) (W : V → FiniteWeightFiber ι) (q : V → ℝ)
    (hq : ∀ v ∈ S, 1 < q v) {c : ℝ} (hc : 0 < c) :
    LocallyIntegrableOn
      (indexedZeroModeGaussianTheta
        (bilateralTensorEulerSeed S W) (bilateralEulerHeight S q) c)
      (Set.Ioi 0) :=
  (fullTensorEulerZeroModeTheta_continuousOn S W q hq hc).locallyIntegrableOn
    measurableSet_Ioi

#print axioms exists_zeroModeGaussianKernel_ray_rpow_bound
#print axioms summable_naturalTensorEuler_zeroModeTerm
#print axioms nonnegativeExponentEquiv
#print axioms summable_fullTensorEuler_zeroModeTerm
#print axioms exists_zeroModeGaussianKernel_global_rpow_bound
#print axioms summable_fullTensorEulerCoeff_mul_height_rpow
#print axioms fullTensorEulerZeroModeTheta_continuousOn_Icc
#print axioms fullTensorEulerZeroModeTheta_continuousOn
#print axioms fullTensorEulerZeroModeTheta_locallyIntegrableOn

end CriticalLinePhasor.GlobalHelix
