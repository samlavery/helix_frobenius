import RequestProject.CarrierHeadFiniteFiber
import RequestProject.EtaLogDerivBank

/-!
# The grown fiber converges to the readout (T2c rebuilt on the growth head)

The carrier's grown fiber `finiteFiber Z s = Σ_{k<⌈Z⌉} (−1)^k w((k+1)/Z) (k+1)^{−s}` (smooth entry window `w`,
head `Z`) is, by summation by parts, the **window-weighted average of the ordered bank's partial readouts**:
  `finiteFiber Z s = Σ_{i<⌈Z⌉−1} (w((i+1)/Z) − w((i+2)/Z)) · P_{i+1}(s)`,  `P_n(s) = Σ_{k<n} (−1)^k (k+1)^{−s}`,
with nonnegative weights summing to `w(1/Z) → 1`.  Since the partial readouts converge locally uniformly on
`Re s > 0` to the eta readout (the compiled Abel tail `etaTailPartial_tendstoLocallyUniformlyOn`), so does the grown
fiber, for every head sequence `Z n → ∞`: `finiteFiber_tendstoLocallyUniformlyOn`.
-/

open Complex Filter Topology Finset
open CriticalLinePhasor.CarrierHeadFiniteFiber
open CriticalLinePhasor.BankNoTransient

namespace CriticalLinePhasor.GrownFiber

/-! ### The window -/

theorem smoothEntry_of_one_le {u : ℝ} (hu : 1 ≤ u) : smoothEntry u = 0 := by
  unfold smoothEntry
  rw [if_neg (not_lt.mpr hu)]

theorem smoothEntry_le_one {u : ℝ} (hu : 0 ≤ u) : smoothEntry u ≤ 1 := by
  unfold smoothEntry
  split_ifs with h
  · apply Real.exp_le_one_iff.mpr
    have h1 : 0 < 1 - u ^ 2 := by nlinarith
    rw [sub_nonpos, le_div_iff₀ h1]
    nlinarith
  · exact zero_le_one

theorem smoothEntry_antitoneOn : AntitoneOn smoothEntry (Set.Ici 0) := by
  intro u hu v hv huv
  simp only [Set.mem_Ici] at hu hv
  unfold smoothEntry
  split_ifs with hv1 hu1 hu1
  · apply Real.exp_le_exp.mpr
    have hu2 : 0 < 1 - u ^ 2 := by nlinarith
    have hv2 : 0 < 1 - v ^ 2 := by nlinarith
    have : 1 / (1 - u ^ 2) ≤ 1 / (1 - v ^ 2) := one_div_le_one_div_of_le hv2 (by nlinarith)
    linarith
  · exact absurd (lt_of_le_of_lt huv hv1) hu1
  · positivity
  · exact le_refl 0

/-- Near the origin the window is within `2u²` of `1`. -/
theorem one_sub_smoothEntry_le {u : ℝ} (hu0 : 0 ≤ u) (hu : u ≤ 1 / 2) : 1 - smoothEntry u ≤ 2 * u ^ 2 := by
  unfold smoothEntry
  rw [if_pos (by linarith)]
  have h1 : 0 < 1 - u ^ 2 := by nlinarith
  have hx : 1 - 1 / (1 - u ^ 2) = -(u ^ 2 / (1 - u ^ 2)) := by field_simp; ring
  rw [hx]
  have h2 := Real.add_one_le_exp (-(u ^ 2 / (1 - u ^ 2)))
  have hu2 : u ^ 2 ≤ 1 / 4 := by nlinarith
  have h3 : u ^ 2 / (1 - u ^ 2) ≤ 2 * u ^ 2 := by
    rw [div_le_iff₀ h1]
    nlinarith [mul_nonneg (sq_nonneg u) (by linarith : (0:ℝ) ≤ 1 - 2 * u ^ 2)]
  linarith

/-! ### The ordered bank's partial readouts -/

/-- `P_n(s) = Σ_{k<n} (−1)^k (k+1)^{−s}`. -/
noncomputable def partialReadout (n : ℕ) (s : ℂ) : ℂ :=
  ∑ k ∈ range n, (-1 : ℂ) ^ k * ((k : ℂ) + 1) ^ (-s)

/-- The compiled hard partial sums `Σ_{m<N} (−1)^{m+1} m^{−s}`. -/
noncomputable def hardPartial (N : ℕ) (s : ℂ) : ℂ :=
  ∑ n ∈ range N, (-1 : ℂ) ^ (n + 1) * (n : ℂ) ^ (-s)

theorem partialReadout_eq_hardPartial (n : ℕ) {s : ℂ} (hs : s ≠ 0) :
    partialReadout n s = hardPartial (n + 1) s := by
  unfold partialReadout hardPartial
  rw [Finset.sum_range_succ']
  rw [show (-1 : ℂ) ^ (0 + 1) * ((0 : ℕ) : ℂ) ^ (-s) = 0 by
    rw [Nat.cast_zero, zero_cpow (neg_ne_zero.mpr hs), mul_zero], add_zero]
  apply Finset.sum_congr rfl
  intro k _
  push_cast
  ring

theorem norm_partialReadout_le (n : ℕ) {s : ℂ} (hs : 0 < s.re) : ‖partialReadout n s‖ ≤ n := by
  unfold partialReadout
  calc ‖∑ k ∈ range n, (-1 : ℂ) ^ k * ((k : ℂ) + 1) ^ (-s)‖
      ≤ ∑ k ∈ range n, ‖(-1 : ℂ) ^ k * ((k : ℂ) + 1) ^ (-s)‖ := norm_sum_le _ _
    _ ≤ ∑ k ∈ range n, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro k _
        rw [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
        have hk : ((k : ℂ) + 1) = (((k : ℝ) + 1 : ℝ) : ℂ) := by push_cast; ring
        rw [hk, norm_cpow_eq_rpow_re_of_pos (by positivity)]
        apply Real.rpow_le_one_of_one_le_of_nonpos (by linarith [(k.cast_nonneg : (0:ℝ) ≤ k)])
        simp only [Complex.neg_re]; linarith
    _ = n := by simp

/-! ### The hard partial sums converge locally uniformly (from the compiled Abel tail) -/

theorem hardPartial_eq_tail (N : ℕ) (s : ℂ) :
    hardPartial N s = ((N - 1 : ℕ) : ℂ) ^ (-s) * (∑ j ∈ range N, (-1 : ℂ) ^ (j + 1)) +
      etaTailPartial (N - 1) s := by
  unfold hardPartial
  set f : ℕ → ℂ := fun n => (n : ℂ) ^ (-s) with hf
  set g : ℕ → ℂ := fun n => (-1 : ℂ) ^ (n + 1) with hg
  have hsum_eq : (∑ n ∈ range N, (-1 : ℂ) ^ (n + 1) * (n : ℂ) ^ (-s)) = ∑ i ∈ range N, f i • g i := by
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [hf, hg, smul_eq_mul, mul_comm]
  rw [hsum_eq, Finset.sum_range_by_parts f g N]
  unfold etaTailPartial etaTailTerm
  simp only [hf, hg, smul_eq_mul]
  rw [sub_eq_add_neg, ← Finset.sum_neg_distrib]
  refine congrArg₂ HAdd.hAdd ?_ ?_
  · first | rfl | (push_cast; ring)
  · apply Finset.sum_congr rfl
    intro i _
    push_cast
    ring

theorem isOpen_rightHalf : IsOpen {s : ℂ | 0 < s.re} := isOpen_lt continuous_const Complex.continuous_re

/-- **The hard partial sums converge locally uniformly on `Re s > 0`.** -/
theorem hardPartial_tendstoLocallyUniformlyOn :
    TendstoLocallyUniformlyOn hardPartial etaTailLimit atTop {s : ℂ | 0 < s.re} := by
  rw [tendstoLocallyUniformlyOn_iff_forall_isCompact isOpen_rightHalf]
  intro K hKsub hKc
  rcases K.eq_empty_or_nonempty with hKe | hKne
  · rw [hKe]; exact tendstoUniformlyOn_empty
  obtain ⟨z₀, hz₀K, hz₀min⟩ := hKc.exists_isMinOn hKne Complex.continuous_re.continuousOn
  rw [isMinOn_iff] at hz₀min
  set σ₀ : ℝ := z₀.re with hσ₀
  have hσ₀pos : 0 < σ₀ := hKsub hz₀K
  have htail : TendstoUniformlyOn etaTailPartial etaTailLimit atTop K :=
    (tendstoLocallyUniformlyOn_iff_forall_isCompact isOpen_rightHalf).mp
      etaTailPartial_tendstoLocallyUniformlyOn K hKsub hKc
  rw [Metric.tendstoUniformlyOn_iff] at htail ⊢
  intro ε hε
  have hbnd : Tendsto (fun N : ℕ => (((N - 1 : ℕ) : ℝ)) ^ (-σ₀)) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop hσ₀pos).comp (tendsto_natCast_atTop_atTop.comp (tendsto_sub_atTop_nat 1))
  filter_upwards [(tendsto_sub_atTop_nat 1).eventually (htail (ε / 2) (by positivity)),
    (tendsto_order.1 hbnd).2 (ε / 2) (by positivity), eventually_ge_atTop 2] with N hN hb hN2 s hs
  rw [dist_eq_norm, hardPartial_eq_tail]
  have h1 : ‖etaTailLimit s - etaTailPartial (N - 1) s‖ < ε / 2 := by
    rw [← dist_eq_norm]; exact hN s hs
  have h2 : ‖((N - 1 : ℕ) : ℂ) ^ (-s) * (∑ j ∈ range N, (-1 : ℂ) ^ (j + 1))‖ < ε / 2 := by
    rw [norm_mul]
    have hG := CriticalLinePhasor.LFunctionPhasor.eta_partialSum_norm_le N
    have hN1 : (1 : ℝ) ≤ ((N - 1 : ℕ) : ℝ) := by
      have : 1 ≤ N - 1 := by omega
      exact_mod_cast this
    have hpow : ‖((N - 1 : ℕ) : ℂ) ^ (-s)‖ ≤ ((N - 1 : ℕ) : ℝ) ^ (-σ₀) := by
      rw [show ((N - 1 : ℕ) : ℂ) = ((((N - 1 : ℕ) : ℝ)) : ℂ) by push_cast; rfl,
        norm_cpow_eq_rpow_re_of_pos (by linarith)]
      apply Real.rpow_le_rpow_of_exponent_le hN1
      simp only [Complex.neg_re]
      linarith [hz₀min s hs]
    calc ‖((N - 1 : ℕ) : ℂ) ^ (-s)‖ * ‖∑ j ∈ range N, (-1 : ℂ) ^ (j + 1)‖
        ≤ ((N - 1 : ℕ) : ℝ) ^ (-σ₀) * 1 := mul_le_mul hpow hG (norm_nonneg _) (by positivity)
      _ < ε / 2 := by rw [mul_one]; exact hb
  calc ‖etaTailLimit s - (((N - 1 : ℕ) : ℂ) ^ (-s) * (∑ j ∈ range N, (-1 : ℂ) ^ (j + 1)) +
        etaTailPartial (N - 1) s)‖
      = ‖(etaTailLimit s - etaTailPartial (N - 1) s) -
          ((N - 1 : ℕ) : ℂ) ^ (-s) * (∑ j ∈ range N, (-1 : ℂ) ^ (j + 1))‖ := by ring_nf
    _ ≤ ‖etaTailLimit s - etaTailPartial (N - 1) s‖ +
          ‖((N - 1 : ℕ) : ℂ) ^ (-s) * (∑ j ∈ range N, (-1 : ℂ) ^ (j + 1))‖ := norm_sub_le _ _
    _ < ε / 2 + ε / 2 := add_lt_add h1 h2
    _ = ε := by ring

/-! ### The grown fiber is the window-weighted average of the partial readouts -/

theorem exp_neg_log_eq_cpow (k : ℕ) (s : ℂ) :
    Complex.exp (-s * (Real.log ((k + 1 : ℕ) : ℝ) : ℂ)) = ((k : ℂ) + 1) ^ (-s) := by
  have hpos : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := by positivity
  have hne : ((k : ℂ) + 1) ≠ 0 := by
    have : ((k : ℂ) + 1) = (((k + 1 : ℕ) : ℝ) : ℂ) := by push_cast; ring
    rw [this]; exact_mod_cast hpos.ne'
  rw [Complex.cpow_def_of_ne_zero hne]
  congr 1
  have hlog : Complex.log ((k : ℂ) + 1) = (Real.log ((k + 1 : ℕ) : ℝ) : ℂ) := by
    rw [Complex.ofReal_log hpos.le]
    congr 1
    push_cast; ring
  rw [hlog]; ring

/-- The increment weights `Δ_i = w((i+1)/Z) − w((i+2)/Z)`. -/
noncomputable def weight (Z : ℝ) (i : ℕ) : ℝ :=
  smoothEntry (((i : ℝ) + 1) / Z) - smoothEntry (((i : ℝ) + 2) / Z)

theorem weight_nonneg {Z : ℝ} (hZ : 0 < Z) (i : ℕ) : 0 ≤ weight Z i := by
  unfold weight
  rw [sub_nonneg]
  apply smoothEntry_antitoneOn (by simp only [Set.mem_Ici]; positivity) (by simp only [Set.mem_Ici]; positivity)
  apply div_le_div_of_nonneg_right _ hZ.le
  linarith

/-- Telescoping of the weights over `Ico a b`. -/
theorem sum_weight_Ico (Z : ℝ) {a b : ℕ} (hab : a ≤ b) :
    ∑ i ∈ Finset.Ico a b, weight Z i = smoothEntry (((a : ℝ) + 1) / Z) - smoothEntry (((b : ℝ) + 1) / Z) := by
  induction b, hab using Nat.le_induction with
  | base => simp
  | succ b hab ih =>
    rw [Finset.sum_Ico_succ_top hab, ih]
    unfold weight
    push_cast
    rw [show ((b : ℝ) + 1 + 1) = (b : ℝ) + 2 by ring]
    ring

/-- **Abel summation on the grown fiber.** -/
theorem finiteFiber_eq_avg {Z : ℝ} (hZ : 0 < Z) (s : ℂ) :
    finiteFiber Z s = ∑ i ∈ range (⌈Z⌉₊ - 1), ((weight Z i : ℝ) : ℂ) * partialReadout (i + 1) s := by
  unfold finiteFiber
  set M : ℕ := ⌈Z⌉₊ with hM
  set f : ℕ → ℂ := fun i => ((smoothEntry (((i + 1 : ℕ) : ℝ) / Z) : ℝ) : ℂ) with hf
  set g : ℕ → ℂ := fun k => (-1 : ℂ) ^ k * ((k : ℂ) + 1) ^ (-s) with hg
  have hsum_eq : (∑ k ∈ range M, ((-1 : ℂ) ^ k * (smoothEntry (((k + 1 : ℕ) : ℝ) / Z) : ℂ)) *
      Complex.exp (-s * (Real.log ((k + 1 : ℕ) : ℝ) : ℂ))) = ∑ i ∈ range M, f i • g i := by
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [hf, hg, smul_eq_mul, exp_neg_log_eq_cpow]
    ring
  rw [hsum_eq, Finset.sum_range_by_parts f g M]
  have hM1 : 1 ≤ M := Nat.ceil_pos.mpr hZ
  have hfM : f (M - 1) = 0 := by
    rw [hf]
    simp only
    rw [show ((M - 1 + 1 : ℕ) : ℝ) = (M : ℝ) by
      rw [Nat.sub_add_cancel hM1]]
    rw [smoothEntry_of_one_le, Complex.ofReal_zero]
    rw [le_div_iff₀ hZ, one_mul]
    exact Nat.le_ceil Z
  rw [hfM, zero_smul, zero_sub, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [hf, hg, smul_eq_mul]
  unfold weight partialReadout
  simp only
  push_cast
  ring

/-! ### Convergence of the grown fiber -/

/-- **The grown fiber converges locally uniformly on `Re s > 0` to the eta readout, for every head sequence
`Z n → ∞`.** -/
theorem finiteFiber_tendstoLocallyUniformlyOn (Z : ℕ → ℝ) (hZ : Tendsto Z atTop atTop) :
    TendstoLocallyUniformlyOn (fun n => finiteFiber (Z n)) etaTailLimit atTop {s : ℂ | 0 < s.re} := by
  rw [tendstoLocallyUniformlyOn_iff_forall_isCompact isOpen_rightHalf]
  intro K hKsub hKc
  rcases K.eq_empty_or_nonempty with hKe | hKne
  · rw [hKe]; exact tendstoUniformlyOn_empty
  have hhard := (tendstoLocallyUniformlyOn_iff_forall_isCompact isOpen_rightHalf).mp
    hardPartial_tendstoLocallyUniformlyOn K hKsub hKc
  rw [Metric.tendstoUniformlyOn_iff] at hhard ⊢
  intro ε hε
  set ε' : ℝ := ε / 4 with hε'
  have hε'pos : 0 < ε' := by positivity
  -- the partial readouts are eventually `ε'`-close to the readout, uniformly on `K`
  obtain ⟨N₁, hN₁⟩ := (hhard ε' hε'pos).exists_forall_of_atTop
  set N₀ : ℕ := N₁ + 1 with hN₀
  have hP : ∀ n, N₀ ≤ n → ∀ s ∈ K, ‖partialReadout n s - etaTailLimit s‖ < ε' := by
    intro n hn s hs
    have hs0 : s ≠ 0 := by
      intro h0; have := hKsub hs; rw [h0] at this; simp at this
    rw [partialReadout_eq_hardPartial n hs0, ← dist_eq_norm, dist_comm]
    exact hN₁ (n + 1) (by omega) s hs
  -- bounds on the readout and on the partial readouts, on `K`
  have hη : ∀ s ∈ K, ‖etaTailLimit s‖ ≤ N₀ + ε' := by
    intro s hs
    have h1 := hP N₀ le_rfl s hs
    have h2 := norm_partialReadout_le N₀ (hKsub hs)
    have h3 := norm_le_insert' (etaTailLimit s) (partialReadout N₀ s)
    rw [norm_sub_rev] at h3
    linarith
  have hBpos : 0 < 2 * (N₀ : ℝ) + ε' := by positivity
  have hPB : ∀ n, n ≤ N₀ → ∀ s ∈ K, ‖partialReadout n s - etaTailLimit s‖ ≤ 2 * (N₀ : ℝ) + ε' := by
    intro n hn s hs
    have h1 := norm_partialReadout_le n (hKsub hs)
    have h2 := hη s hs
    have h3 : (n : ℝ) ≤ N₀ := by exact_mod_cast hn
    calc ‖partialReadout n s - etaTailLimit s‖ ≤ ‖partialReadout n s‖ + ‖etaTailLimit s‖ := norm_sub_le _ _
      _ ≤ n + (N₀ + ε') := add_le_add h1 h2
      _ ≤ 2 * (N₀ : ℝ) + ε' := by linarith
  have hN1 : (1 : ℝ) ≤ N₀ := by rw [hN₀]; push_cast; linarith [(N₁.cast_nonneg : (0:ℝ) ≤ N₁)]
  -- the head threshold
  set Z₁ : ℝ := max (2 * N₀ + 2)
    (max (8 * (N₀ : ℝ) ^ 2 * (2 * (N₀ : ℝ) + ε') / ε') (2 * (N₀ + ε') / ε')) with hZ₁
  filter_upwards [hZ.eventually (eventually_ge_atTop Z₁)] with n hn s hs
  set Zn : ℝ := Z n with hZn
  have hZ1 : 2 * (N₀ : ℝ) + 2 ≤ Zn := (le_max_left _ _).trans hn
  have hZ2 : 8 * (N₀ : ℝ) ^ 2 * (2 * (N₀ : ℝ) + ε') / ε' ≤ Zn :=
    ((le_max_left _ _).trans (le_max_right _ _)).trans hn
  have hZ3 : 2 * (N₀ + ε') / ε' ≤ Zn := ((le_max_right _ _).trans (le_max_right _ _)).trans hn
  have hZpos : 0 < Zn := by linarith
  have hZ2' : 2 ≤ Zn := by linarith
  have hZsq : Zn ≤ Zn ^ 2 := by nlinarith
  set M : ℕ := ⌈Zn⌉₊ with hM
  have hMZ : Zn ≤ M := Nat.le_ceil Zn
  have hMN : N₀ + 1 ≤ M - 1 := by
    have h1 : (2 * N₀ + 2 : ℝ) ≤ M := hZ1.trans hMZ
    have h2 : 2 * N₀ + 2 ≤ M := by exact_mod_cast h1
    omega
  have hM1 : 1 ≤ M := by omega
  have h01 : ((0 : ℕ) : ℝ) + 1 = 1 := by norm_num
  have hMcast : ((M - 1 : ℕ) : ℝ) + 1 = (M : ℝ) := by rw [Nat.cast_sub hM1]; push_cast; ring
  -- total weight
  have hw1 : ∑ i ∈ range (M - 1), weight Zn i = smoothEntry (1 / Zn) := by
    rw [Finset.range_eq_Ico, sum_weight_Ico Zn (Nat.zero_le _), h01, hMcast,
      smoothEntry_of_one_le (u := (M : ℝ) / Zn) (by rw [le_div_iff₀ hZpos, one_mul]; exact hMZ), sub_zero]
  have hsumC : (∑ i ∈ range (M - 1), ((weight Zn i : ℝ) : ℂ)) = ((smoothEntry (1 / Zn) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_sum, hw1]
  -- the identity and the decomposition of the error
  rw [dist_eq_norm, finiteFiber_eq_avg hZpos]
  have hdecomp : etaTailLimit s - ∑ i ∈ range (M - 1), ((weight Zn i : ℝ) : ℂ) * partialReadout (i + 1) s
      = (∑ i ∈ range (M - 1), ((weight Zn i : ℝ) : ℂ) * (etaTailLimit s - partialReadout (i + 1) s))
        + ((1 - smoothEntry (1 / Zn) : ℝ) : ℂ) * etaTailLimit s := by
    have hsplit : ∑ i ∈ range (M - 1), ((weight Zn i : ℝ) : ℂ) * (etaTailLimit s - partialReadout (i + 1) s)
        = (∑ i ∈ range (M - 1), ((weight Zn i : ℝ) : ℂ)) * etaTailLimit s
          - ∑ i ∈ range (M - 1), ((weight Zn i : ℝ) : ℂ) * partialReadout (i + 1) s := by
      rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [hsplit, hsumC]
    push_cast
    ring
  rw [hdecomp]
  -- split the weighted sum at `N₀`
  have hsplit2 : ∑ i ∈ range (M - 1), ((weight Zn i : ℝ) : ℂ) * (etaTailLimit s - partialReadout (i + 1) s)
      = ∑ i ∈ Finset.Ico 0 N₀, ((weight Zn i : ℝ) : ℂ) * (etaTailLimit s - partialReadout (i + 1) s)
        + ∑ i ∈ Finset.Ico N₀ (M - 1), ((weight Zn i : ℝ) : ℂ) * (etaTailLimit s - partialReadout (i + 1) s) := by
    rw [Finset.range_eq_Ico, Finset.sum_Ico_consecutive _ (Nat.zero_le _) (by omega)]
  have hbound1 : ‖∑ i ∈ Finset.Ico 0 N₀, ((weight Zn i : ℝ) : ℂ) * (etaTailLimit s - partialReadout (i + 1) s)‖
      ≤ (∑ i ∈ Finset.Ico 0 N₀, weight Zn i) * (2 * (N₀ : ℝ) + ε') := by
    rw [Finset.sum_mul]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i hi => ?_)
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (weight_nonneg hZpos i), norm_sub_rev]
    apply mul_le_mul_of_nonneg_left _ (weight_nonneg hZpos i)
    exact hPB (i + 1) (by rw [Finset.mem_Ico] at hi; omega) s hs
  have hbound2 : ‖∑ i ∈ Finset.Ico N₀ (M - 1), ((weight Zn i : ℝ) : ℂ) *
      (etaTailLimit s - partialReadout (i + 1) s)‖
      ≤ (∑ i ∈ Finset.Ico N₀ (M - 1), weight Zn i) * ε' := by
    rw [Finset.sum_mul]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i hi => ?_)
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (weight_nonneg hZpos i), norm_sub_rev]
    apply mul_le_mul_of_nonneg_left _ (weight_nonneg hZpos i)
    exact (hP (i + 1) (by rw [Finset.mem_Ico] at hi; omega) s hs).le
  -- the weight sums
  have hsum1 : ∑ i ∈ Finset.Ico 0 N₀, weight Zn i ≤ 2 * (((N₀ : ℝ) + 1) / Zn) ^ 2 := by
    rw [sum_weight_Ico Zn (Nat.zero_le _), h01]
    have h1 := smoothEntry_le_one (u := 1 / Zn) (by positivity)
    have h2 := one_sub_smoothEntry_le (u := ((N₀ : ℝ) + 1) / Zn) (by positivity)
      (by rw [div_le_iff₀ hZpos]; linarith)
    linarith
  have hsum2 : ∑ i ∈ Finset.Ico N₀ (M - 1), weight Zn i ≤ 1 := by
    rw [sum_weight_Ico Zn (by omega)]
    have h1 := smoothEntry_le_one (u := ((N₀ : ℝ) + 1) / Zn) (by positivity)
    have h2 := smoothEntry_nonneg ((((M - 1 : ℕ) : ℝ) + 1) / Zn)
    linarith
  have hlast : ‖((1 - smoothEntry (1 / Zn) : ℝ) : ℂ) * etaTailLimit s‖ ≤ 2 * (1 / Zn) ^ 2 * (N₀ + ε') := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have h1 := one_sub_smoothEntry_le (u := 1 / Zn) (by positivity)
      (by rw [div_le_iff₀ hZpos]; linarith)
    have h0 := smoothEntry_le_one (u := 1 / Zn) (by positivity)
    rw [abs_of_nonneg (by linarith)]
    exact mul_le_mul h1 (hη s hs) (norm_nonneg _) (by positivity)
  -- each of the three pieces is at most `ε'`
  have hpiece1 : (∑ i ∈ Finset.Ico 0 N₀, weight Zn i) * (2 * (N₀ : ℝ) + ε') ≤ ε' := by
    have hN : ((N₀ : ℝ) + 1) ^ 2 ≤ 4 * (N₀ : ℝ) ^ 2 := by nlinarith
    have h1 : ((N₀ : ℝ) + 1) ^ 2 / Zn ^ 2 ≤ 4 * (N₀ : ℝ) ^ 2 / Zn := by
      rw [div_le_div_iff₀ (by positivity) hZpos]
      nlinarith [mul_nonneg (sq_nonneg (N₀ : ℝ)) (sub_nonneg.mpr hZsq)]
    have h2 : 2 * (((N₀ : ℝ) + 1) / Zn) ^ 2 * (2 * (N₀ : ℝ) + ε')
        ≤ 8 * (N₀ : ℝ) ^ 2 * (2 * (N₀ : ℝ) + ε') / Zn := by
      rw [div_pow]
      have := mul_le_mul_of_nonneg_right h1 hBpos.le
      calc 2 * (((N₀ : ℝ) + 1) ^ 2 / Zn ^ 2) * (2 * (N₀ : ℝ) + ε')
          = 2 * (((N₀ : ℝ) + 1) ^ 2 / Zn ^ 2 * (2 * (N₀ : ℝ) + ε')) := by ring
        _ ≤ 2 * (4 * (N₀ : ℝ) ^ 2 / Zn * (2 * (N₀ : ℝ) + ε')) := by linarith
        _ = 8 * (N₀ : ℝ) ^ 2 * (2 * (N₀ : ℝ) + ε') / Zn := by ring
    calc (∑ i ∈ Finset.Ico 0 N₀, weight Zn i) * (2 * (N₀ : ℝ) + ε')
        ≤ 2 * (((N₀ : ℝ) + 1) / Zn) ^ 2 * (2 * (N₀ : ℝ) + ε') :=
          mul_le_mul_of_nonneg_right hsum1 hBpos.le
      _ ≤ 8 * (N₀ : ℝ) ^ 2 * (2 * (N₀ : ℝ) + ε') / Zn := h2
      _ ≤ ε' := by
          rw [div_le_iff₀ hZpos]
          calc 8 * (N₀ : ℝ) ^ 2 * (2 * (N₀ : ℝ) + ε')
              = (8 * (N₀ : ℝ) ^ 2 * (2 * (N₀ : ℝ) + ε') / ε') * ε' := by field_simp
            _ ≤ Zn * ε' := mul_le_mul_of_nonneg_right hZ2 hε'pos.le
            _ = ε' * Zn := mul_comm _ _
  have hpiece2 : (∑ i ∈ Finset.Ico N₀ (M - 1), weight Zn i) * ε' ≤ ε' := by
    calc (∑ i ∈ Finset.Ico N₀ (M - 1), weight Zn i) * ε' ≤ 1 * ε' :=
          mul_le_mul_of_nonneg_right hsum2 hε'pos.le
      _ = ε' := one_mul _
  have hpiece3 : 2 * (1 / Zn) ^ 2 * (N₀ + ε') ≤ ε' := by
    calc 2 * (1 / Zn) ^ 2 * (N₀ + ε') = 2 * (N₀ + ε') / Zn ^ 2 := by ring
      _ ≤ 2 * (N₀ + ε') / Zn := div_le_div_of_nonneg_left (by positivity) hZpos hZsq
      _ ≤ ε' := by
          rw [div_le_iff₀ hZpos]
          calc 2 * ((N₀ : ℝ) + ε') = (2 * ((N₀ : ℝ) + ε') / ε') * ε' := by field_simp
            _ ≤ Zn * ε' := mul_le_mul_of_nonneg_right hZ3 hε'pos.le
            _ = ε' * Zn := mul_comm _ _
  calc ‖(∑ i ∈ range (M - 1), ((weight Zn i : ℝ) : ℂ) * (etaTailLimit s - partialReadout (i + 1) s))
        + ((1 - smoothEntry (1 / Zn) : ℝ) : ℂ) * etaTailLimit s‖
      ≤ ‖∑ i ∈ range (M - 1), ((weight Zn i : ℝ) : ℂ) * (etaTailLimit s - partialReadout (i + 1) s)‖
        + ‖((1 - smoothEntry (1 / Zn) : ℝ) : ℂ) * etaTailLimit s‖ := norm_add_le _ _
    _ ≤ ((∑ i ∈ Finset.Ico 0 N₀, weight Zn i) * (2 * (N₀ : ℝ) + ε')
          + (∑ i ∈ Finset.Ico N₀ (M - 1), weight Zn i) * ε')
        + 2 * (1 / Zn) ^ 2 * (N₀ + ε') := by
        apply add_le_add _ hlast
        rw [hsplit2]
        exact (norm_add_le _ _).trans (add_le_add hbound1 hbound2)
    _ ≤ ε' + ε' + ε' := by linarith [hpiece1, hpiece2, hpiece3]
    _ < ε := by rw [hε']; linarith

end CriticalLinePhasor.GrownFiber

#print axioms CriticalLinePhasor.GrownFiber.finiteFiber_eq_avg
#print axioms CriticalLinePhasor.GrownFiber.hardPartial_tendstoLocallyUniformlyOn
#print axioms CriticalLinePhasor.GrownFiber.finiteFiber_tendstoLocallyUniformlyOn
