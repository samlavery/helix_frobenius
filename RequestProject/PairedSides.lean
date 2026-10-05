import RequestProject.StageBoundStatus
import RequestProject.ArchSideJets

/-!
# The paired sides: the Γ face, after the end pairing, is unconditionally bounded (ledger 636)

`archSide` carries the end atom `0`, whose transport at `s₀ = −1 + 20i` lies outside the unit circle;
`primeSide` carries the compensating pole at the reflected point. Pair them:

  `pairedArch s = 1/(s−1) + log π/2 − ½ψ((1−s)/2)`,  `pairedPrime s = 1/s + primeSide s`,
  `explicitLogDeriv = pairedArch + pairedPrime`.

`pairedArch`'s atoms are exactly the Γ ticks `3, 5, 7, …` (`jets_pairedArch_series`), every one of which
transports into the closed unit disc, with summable weights. So its coefficient sequence is **bounded,
unconditionally** (`pairedArchCoeff_bounded`), and the leaf moves entirely onto the arithmetic side:

  **`rh_of_pairedPrime_polynomial`: a polynomial bound on the paired prime coefficients at `−1 + 20i`
  puts every nontrivial zero on the line.**
-/

open Complex Finset Filter Topology

namespace CriticalLinePhasor.SeatingLedger

/-- The anchor domain. -/
def anchorDom : Set ℂ := {s : ℂ | s.re < 0} ∩ {s : ℂ | s.im ≠ 0}

theorem anchorDom_open : IsOpen anchorDom := isOpen_anchorDomain

theorem anchor20_mem : anchor20 ∈ anchorDom := by
  constructor
  · rw [Set.mem_setOf_eq, anchor20_re]; norm_num
  · rw [Set.mem_setOf_eq, anchor20_im]; norm_num

/-- Jets are additive on the anchor domain. -/
theorem jets_add_contDiffOn {f g : ℂ → ℂ} {s : ℂ} (hsV : s ∈ anchorDom)
    (hf : ContDiffOn ℂ ⊤ f anchorDom) (hg : ContDiffOn ℂ ⊤ g anchorDom) :
    jets (f + g) s = jets f s + jets g s := by
  funext m
  cases m with
  | zero => simp [jets]
  | succ m =>
    simp only [jets, Pi.add_apply]
    rw [← iteratedDerivWithin_of_isOpen (f := f + g) anchorDom_open hsV,
      ← iteratedDerivWithin_of_isOpen (f := f) anchorDom_open hsV,
      ← iteratedDerivWithin_of_isOpen (f := g) anchorDom_open hsV,
      iteratedDerivWithin_add hsV anchorDom_open.uniqueDiffOn ((hf s hsV).of_le le_top)
        ((hg s hsV).of_le le_top)]
    ring

/-- The Archimedean side with the end atom removed. -/
noncomputable def pairedArch (s : ℂ) : ℂ :=
  1 / (s - 1) + ((Real.log Real.pi : ℝ) : ℂ) / 2 - (1 / 2 : ℂ) * Complex.digamma ((1 - s) / 2)

/-- The prime side with the end atom attached. -/
noncomputable def pairedPrime (s : ℂ) : ℂ := 1 / s + primeSide s

theorem archSide_split : archSide = (fun s : ℂ => 1 / s) + pairedArch := by
  rw [archSide_eq]; funext w; simp only [pairedArch, Pi.add_apply]; ring

theorem explicitLogDeriv_paired : explicitLogDeriv = pairedArch + pairedPrime := by
  funext s
  rw [explicitLogDeriv, archSide_eq]
  simp only [pairedArch, pairedPrime, Pi.add_apply]
  ring

theorem oneDiv_contDiffOn : ContDiffOn ℂ ⊤ (fun s : ℂ => 1 / s) anchorDom := by
  refine DifferentiableOn.contDiffOn ?_ anchorDom_open
  intro w hw
  have h0 : w ≠ 0 := by intro h; rw [h] at hw; exact absurd hw.1 (by simp)
  exact ((differentiableAt_const (1 : ℂ)).div differentiableAt_id h0).differentiableWithinAt

theorem pairedArch_contDiffOn : ContDiffOn ℂ ⊤ pairedArch anchorDom := by
  refine DifferentiableOn.contDiffOn ?_ anchorDom_open
  intro w hw
  have hs1 : w - 1 ≠ 0 := by
    intro h
    have hw1 : w = 1 := by linear_combination h
    rw [hw1] at hw; exact absurd hw.1 (by simp)
  have hmem := archDomain_of_im_ne_zero hw.2
  have h1 : DifferentiableAt ℂ (fun w : ℂ => (1 - w) / 2) w := by fun_prop
  have hq : DifferentiableAt ℂ (fun s : ℂ => (1 / 2 : ℂ) * Complex.digamma ((1 - s) / 2)) w :=
    ((Zeta23.Stirling.differentiableAt_digamma hmem).comp w h1).const_mul _
  have hp : DifferentiableAt ℂ (fun s : ℂ => 1 / (s - 1)) w :=
    (differentiableAt_const (1 : ℂ)).div ((differentiableAt_id (𝕜 := ℂ)).sub_const 1) hs1
  have : DifferentiableAt ℂ pairedArch w := by
    unfold pairedArch
    exact (hp.add_const _).sub hq
  exact this.differentiableWithinAt

theorem pairedPrime_contDiffOn : ContDiffOn ℂ ⊤ pairedPrime anchorDom := by
  have h1 : ContDiffOn ℂ ⊤ primeSide anchorDom :=
    primeSide_contDiffOn.mono (fun w hw => hw.1)
  have := oneDiv_contDiffOn.add h1
  refine this.congr (fun w _ => ?_)
  simp [pairedPrime]

/-! ## The tick series -/

/-- Every tick `3 + 2n` is far from an anchor-domain point. -/
theorem norm_tick_ge {s : ℂ} (hs : s.re < 0) (n : ℕ) : ((n : ℝ) + 1) ≤ ‖s - 3 - 2 * (n : ℂ)‖ := by
  have h := Complex.abs_re_le_norm (s - 3 - 2 * (n : ℂ))
  have hre : (s - 3 - 2 * (n : ℂ)).re = s.re - 3 - 2 * (n : ℝ) := by simp
  rw [hre] at h
  have : ((n : ℝ) + 1) ≤ |s.re - 3 - 2 * (n : ℝ)| := by
    rw [abs_of_nonpos (by linarith [Nat.cast_nonneg (α := ℝ) n])]
    have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  linarith

/-- The same for the shift `1`. -/
theorem norm_shift1_ge {s : ℂ} (hs : s.re < 0) (n : ℕ) : ((n : ℝ) + 1) ≤ ‖s - 1 - 2 * (n : ℂ)‖ := by
  have h := Complex.abs_re_le_norm (s - 1 - 2 * (n : ℂ))
  have hre : (s - 1 - 2 * (n : ℂ)).re = s.re - 1 - 2 * (n : ℝ) := by simp
  rw [hre] at h
  have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have : ((n : ℝ) + 1) ≤ |s.re - 1 - 2 * (n : ℝ)| := by
    rw [abs_of_nonpos (by linarith)]
    linarith
  linarith

theorem summable_shift1Pow {s : ℂ} (hs : s.re < 0) {m : ℕ} (hm : 2 ≤ m) :
    Summable (fun n : ℕ => (1 : ℂ) / (s - 1 - 2 * (n : ℂ)) ^ m) := by
  have hg : Summable (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ 2) := by
    have h1 : Summable (fun n : ℕ => 1 / (n : ℝ) ^ 2) := Real.summable_one_div_nat_pow.mpr (by omega)
    exact ((summable_nat_add_iff 1).mpr h1).congr (fun n => by rw [Nat.cast_add_one])
  refine Summable.of_norm_bounded hg (fun n => ?_)
  have hlow := norm_shift1_ge hs n
  have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  rw [norm_div, norm_one, norm_pow]
  have h1 : ((n : ℝ) + 1) ^ 2 ≤ ‖s - 1 - 2 * (n : ℂ)‖ ^ m := by
    calc ((n : ℝ) + 1) ^ 2 ≤ ((n : ℝ) + 1) ^ m := pow_le_pow_right₀ (by linarith) hm
      _ ≤ ‖s - 1 - 2 * (n : ℂ)‖ ^ m := pow_le_pow_left₀ hpos.le hlow m
  exact one_div_le_one_div_of_le (by positivity) h1

theorem summable_gammaTickPow {s : ℂ} (hs : s.re < 0) {m : ℕ} (hm : 2 ≤ m) :
    Summable (fun n : ℕ => (1 : ℂ) / (s - 3 - 2 * (n : ℂ)) ^ m) := by
  have hg : Summable (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ 2) := by
    have h1 : Summable (fun n : ℕ => 1 / (n : ℝ) ^ 2) := Real.summable_one_div_nat_pow.mpr (by omega)
    exact ((summable_nat_add_iff 1).mpr h1).congr (fun n => by rw [Nat.cast_add_one])
  refine Summable.of_norm_bounded hg (fun n => ?_)
  have hlow := norm_tick_ge hs n
  have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  rw [norm_div, norm_one, norm_pow]
  have h1 : ((n : ℝ) + 1) ^ 2 ≤ ‖s - 3 - 2 * (n : ℂ)‖ ^ m := by
    calc ((n : ℝ) + 1) ^ 2 ≤ ((n : ℝ) + 1) ^ m := pow_le_pow_right₀ (by linarith) hm
      _ ≤ ‖s - 3 - 2 * (n : ℂ)‖ ^ m := pow_le_pow_left₀ hpos.le hlow m
  exact one_div_le_one_div_of_le (by positivity) h1

/-- **The paired Archimedean jets are the Γ ticks `3, 5, 7, …` alone.** -/
theorem jets_pairedArch_series {s : ℂ} (hs : s.re < 0) (hi : s.im ≠ 0) {m : ℕ} (hm : 2 ≤ m) :
    jets pairedArch s m = -∑' n : ℕ, (1 : ℂ) / (s - 3 - 2 * (n : ℂ)) ^ m := by
  have hsV : s ∈ anchorDom := ⟨hs, hi⟩
  have hsplit : jets archSide s = jets (fun s : ℂ => 1 / s) s + jets pairedArch s := by
    rw [archSide_split]
    exact jets_add_contDiffOn hsV oneDiv_contDiffOn pairedArch_contDiffOn
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  have hend : jets (fun s : ℂ => 1 / s) s (k + 1) = 1 / s ^ (k + 1) := by
    simp only [jets]
    rw [show (fun s : ℂ => 1 / s) = fun s : ℂ => 1 / (s - 0) by funext w; rw [sub_zero],
      iteratedDeriv_one_div_sub 0 k (by intro h; rw [h] at hs; simp at hs)]
    have hf : (k.factorial : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
    have hsq : ((-1 : ℂ) ^ k) ^ 2 = 1 := by rw [← pow_mul]; exact Even.neg_one_pow ⟨k, by ring⟩
    rw [sub_zero, show (-1 : ℂ) ^ k / (k.factorial : ℂ) * ((-1) ^ k * (k.factorial : ℂ) / s ^ (k + 1))
        = ((-1 : ℂ) ^ k) ^ 2 * ((k.factorial : ℂ) / (k.factorial : ℂ)) * (1 / s ^ (k + 1)) by ring,
      hsq, div_self hf, one_mul, one_mul]
  have hfull := jets_archSide_series hs hi (m := k + 1) hm
  have hsum : Summable (fun n : ℕ => (1 : ℂ) / (s - 1 - 2 * (n : ℂ)) ^ (k + 1)) :=
    summable_shift1Pow hs hm
  have hshift : ∑' n : ℕ, (1 : ℂ) / (s - 1 - 2 * (n : ℂ)) ^ (k + 1)
      = 1 / (s - 1) ^ (k + 1) + ∑' n : ℕ, (1 : ℂ) / (s - 3 - 2 * (n : ℂ)) ^ (k + 1) := by
    rw [hsum.tsum_eq_zero_add]
    congr 1
    · norm_num
    · exact tsum_congr (fun n => by push_cast; ring_nf)
  have := congrFun hsplit (k + 1)
  simp only [Pi.add_apply] at this
  rw [hend, hfull, hshift] at this
  linear_combination -this


/-! ## The paired Archimedean coefficients are bounded, unconditionally -/

/-- The Γ ticks `3, 5, 7, …`. -/
noncomputable def gammaTick (n : ℕ) : ℂ := 3 + 2 * (n : ℂ)

theorem anchor20_mirror : 1 - (starRingEnd ℂ) anchor20 = 2 + 20 * I := by
  unfold anchor20
  apply Complex.ext <;> simp <;> norm_num

theorem norm_anchor_sub_tick_ge (n : ℕ) : ((n : ℝ) + 1) ≤ ‖anchor20 - gammaTick n‖ := by
  have h : anchor20 - gammaTick n = anchor20 - 3 - 2 * (n : ℂ) := by unfold gammaTick; ring
  rw [h]
  have hs : anchor20.re < 0 := by rw [anchor20_re]; norm_num
  exact norm_tick_ge hs n

theorem norm_tick_sub_mirror_ge (n : ℕ) :
    ((n : ℝ) + 1) ≤ ‖gammaTick n - (1 - (starRingEnd ℂ) anchor20)‖ := by
  rw [anchor20_mirror]
  have h := Complex.abs_re_le_norm (gammaTick n - (2 + 20 * I))
  have hre : (gammaTick n - (2 + 20 * I)).re = 1 + 2 * (n : ℝ) := by
    unfold gammaTick; simp; ring
  rw [hre] at h
  have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have : ((n : ℝ) + 1) ≤ |1 + 2 * (n : ℝ)| := by rw [abs_of_nonneg (by linarith)]; linarith
  linarith

theorem anchor_sub_tick_ne (n : ℕ) : anchor20 - gammaTick n ≠ 0 := by
  intro h
  have := norm_anchor_sub_tick_ge n
  rw [h, norm_zero] at this
  have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  linarith [norm_anchor_sub_tick_ge n]

theorem tick_sub_mirror_ne (n : ℕ) : gammaTick n - (1 - (starRingEnd ℂ) anchor20) ≠ 0 := by
  intro h
  have h2 := norm_tick_sub_mirror_ge n
  rw [h, norm_zero] at h2
  have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  linarith

/-- The tick weights are summable. -/
theorem summable_tickWeightC :
    Summable (fun n : ℕ => ‖atomWeight anchor20 (gammaTick n)‖) := by
  have hg : Summable (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ 2) := by
    have h1 : Summable (fun n : ℕ => 1 / (n : ℝ) ^ 2) := Real.summable_one_div_nat_pow.mpr (by omega)
    exact ((summable_nat_add_iff 1).mpr h1).congr (fun n => by rw [Nat.cast_add_one])
  refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_) hg
  have h1 := norm_anchor_sub_tick_ge n
  have h2 := norm_tick_sub_mirror_ge n
  have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  unfold atomWeight
  rw [norm_inv, norm_mul, inv_eq_one_div]
  have hAB : ((n : ℝ) + 1) ^ 2
      ≤ ‖anchor20 - gammaTick n‖ * ‖gammaTick n - (1 - (starRingEnd ℂ) anchor20)‖ := by
    nlinarith [norm_nonneg (anchor20 - gammaTick n),
      norm_nonneg (gammaTick n - (1 - (starRingEnd ℂ) anchor20))]
  exact one_div_le_one_div_of_le (by positivity) hAB

/-- Each Γ tick transports into the closed unit disc. -/
theorem norm_transport_tick_le_one (n : ℕ) : ‖transport anchor20 (gammaTick n)‖ ≤ 1 := by
  have h : gammaTick n = ((3 + 2 * (n : ℝ) : ℝ) : ℂ) := by unfold gammaTick; push_cast; ring
  rw [h]
  have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  exact (norm_transport_anchor_tick_lt_one (by linarith)).le

/-- **The paired Archimedean coefficients as a tick-atom sum** (`k ≥ 1`). -/
theorem pairedArchCoeff_atoms (k : ℕ) :
    toeplitzCoeff (-3) (jets pairedArch anchor20) (k + 1)
      = -∑' n : ℕ, atomWeight anchor20 (gammaTick n) * transport anchor20 (gammaTick n) ^ (k + 1) := by
  have hs : anchor20.re < 0 := by rw [anchor20_re]; norm_num
  have hi : anchor20.im ≠ 0 := by rw [anchor20_im]; norm_num
  have hd : anchor20 - (1 - (starRingEnd ℂ) anchor20) = -3 := by
    rw [mirror_d, anchor20_re]; norm_num
  simp only [toeplitzCoeff]
  have hjet : ∀ i ∈ range (k + 1), jets pairedArch anchor20 (k + 2 - i)
      = -∑' n : ℕ, (1 : ℂ) / (anchor20 - 3 - 2 * (n : ℂ)) ^ (k + 2 - i) := by
    intro i hi'
    rw [mem_range] at hi'
    exact jets_pairedArch_series hs hi (by omega)
  have hsum : ∀ i ∈ range (k + 1),
      Summable (fun n : ℕ => (1 : ℂ) / (anchor20 - 3 - 2 * (n : ℂ)) ^ (k + 2 - i)) := by
    intro i hi'
    rw [mem_range] at hi'
    exact summable_gammaTickPow hs (by omega)
  have hL : ∑ i ∈ range (k + 1), ((k.choose i : ℂ) * (-3 : ℂ) ^ (k - i) * (-1) ^ i
        * jets pairedArch anchor20 (k + 2 - i))
      = -∑' n : ℕ, ∑ i ∈ range (k + 1), ((k.choose i : ℂ) * (-3 : ℂ) ^ (k - i) * (-1) ^ i
        * ((1 : ℂ) / (anchor20 - 3 - 2 * (n : ℂ)) ^ (k + 2 - i))) := by
    have step : ∀ i ∈ range (k + 1),
        (k.choose i : ℂ) * (-3 : ℂ) ^ (k - i) * (-1) ^ i * jets pairedArch anchor20 (k + 2 - i)
          = -(∑' n : ℕ, (k.choose i : ℂ) * (-3 : ℂ) ^ (k - i) * (-1) ^ i
              * ((1 : ℂ) / (anchor20 - 3 - 2 * (n : ℂ)) ^ (k + 2 - i))) := by
      intro i hi'
      rw [hjet i hi', tsum_mul_left]
      ring
    rw [Finset.sum_congr rfl step, Finset.sum_neg_distrib]
    congr 1
    exact (Summable.tsum_finsetSum (fun i hi' => (hsum i hi').mul_left _)).symm
  rw [hL]
  congr 1
  apply tsum_congr
  intro n
  have hne := anchor_sub_tick_ne n
  have htick : anchor20 - 3 - 2 * (n : ℂ) = anchor20 - gammaTick n := by unfold gammaTick; ring
  have hid := transport_pow_identity anchor20 (gammaTick n) hne k
  rw [hd] at hid
  have hconv : ∀ i : ℕ, (1 : ℂ) / (anchor20 - 3 - 2 * (n : ℂ)) ^ (k + 2 - i)
      = (anchor20 - gammaTick n)⁻¹ ^ (k + 2 - i) := by
    intro i; rw [htick, one_div, inv_pow]
  simp_rw [hconv]
  rw [← hid]
  have hB := tick_sub_mirror_ne n
  rw [show (gammaTick n - (1 - (starRingEnd ℂ) anchor20)) ^ k
      = (gammaTick n - (1 - (starRingEnd ℂ) anchor20))⁻¹
        * (gammaTick n - (1 - (starRingEnd ℂ) anchor20)) ^ (k + 1) by
    rw [pow_succ', inv_mul_cancel_left₀ hB]]
  unfold atomWeight transport
  rw [div_pow, mul_inv, div_eq_mul_inv, ← inv_pow]
  ring

/-- **The paired Archimedean coefficient sequence is bounded, unconditionally.** -/
theorem pairedArchCoeff_bounded :
    ∃ K : ℝ, ∀ k, ‖toeplitzCoeff (-3) (jets pairedArch anchor20) k‖ ≤ K := by
  set K₁ : ℝ := ∑' n : ℕ, ‖atomWeight anchor20 (gammaTick n)‖ with hK₁
  refine ⟨max ‖toeplitzCoeff (-3) (jets pairedArch anchor20) 0‖ K₁, fun k => ?_⟩
  cases k with
  | zero => exact le_max_left _ _
  | succ k =>
    refine le_trans ?_ (le_max_right _ _)
    rw [pairedArchCoeff_atoms k, norm_neg]
    have hterm : ∀ n : ℕ,
        ‖atomWeight anchor20 (gammaTick n) * transport anchor20 (gammaTick n) ^ (k + 1)‖
          ≤ ‖atomWeight anchor20 (gammaTick n)‖ := by
      intro n
      rw [norm_mul, norm_pow]
      calc ‖atomWeight anchor20 (gammaTick n)‖ * ‖transport anchor20 (gammaTick n)‖ ^ (k + 1)
          ≤ ‖atomWeight anchor20 (gammaTick n)‖ * 1 ^ (k + 1) := by
            gcongr
            exact norm_transport_tick_le_one n
        _ = _ := by rw [one_pow, mul_one]
    have hsn : Summable (fun n : ℕ =>
        ‖atomWeight anchor20 (gammaTick n) * transport anchor20 (gammaTick n) ^ (k + 1)‖) :=
      Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hterm summable_tickWeightC
    calc ‖∑' n : ℕ, atomWeight anchor20 (gammaTick n) * transport anchor20 (gammaTick n) ^ (k + 1)‖
        ≤ ∑' n : ℕ, ‖atomWeight anchor20 (gammaTick n) * transport anchor20 (gammaTick n) ^ (k + 1)‖ :=
          norm_tsum_le_tsum_norm hsn
      _ ≤ K₁ := Summable.tsum_le_tsum hterm hsn summable_tickWeightC

/-! ## The leaf moves onto the arithmetic side -/

theorem explicitCoeff_split (k : ℕ) :
    toeplitzCoeff (-3) (jets explicitLogDeriv anchor20) k
      = toeplitzCoeff (-3) (jets pairedArch anchor20) k
        + toeplitzCoeff (-3) (jets pairedPrime anchor20) k := by
  rw [explicitLogDeriv_paired,
    jets_add_contDiffOn anchor20_mem pairedArch_contDiffOn pairedPrime_contDiffOn,
    toeplitzCoeff_add]

/-- **A polynomial bound on the paired prime coefficients alone puts every zero on the line.** -/
theorem rh_of_pairedPrime_polynomial
    (hpoly : ∃ C : ℝ, ∃ p : ℕ, ∀ k,
      ‖toeplitzCoeff (-3) (jets pairedPrime anchor20) k‖ ≤ C * (1 + (k : ℝ) ^ p)) : RH := by
  obtain ⟨K, hK⟩ := pairedArchCoeff_bounded
  have hK0 : 0 ≤ K := le_trans (norm_nonneg _) (hK 0)
  have hs : anchor20.re < 0 := by rw [anchor20_re]; norm_num
  have hd : ((2 * anchor20.re - 1 : ℝ) : ℂ) = -3 := by rw [anchor20_re]; norm_num
  apply rh_of_explicit_polynomial_growth hs
  rw [hd]
  obtain ⟨C, p, h⟩ := hpoly
  refine ⟨C + K, p, fun k => ?_⟩
  have hk : (1 : ℝ) ≤ 1 + (k : ℝ) ^ p := by
    have : (0 : ℝ) ≤ (k : ℝ) ^ p := by positivity
    linarith
  rw [explicitCoeff_split k]
  calc ‖toeplitzCoeff (-3) (jets pairedArch anchor20) k
        + toeplitzCoeff (-3) (jets pairedPrime anchor20) k‖
      ≤ ‖toeplitzCoeff (-3) (jets pairedArch anchor20) k‖
        + ‖toeplitzCoeff (-3) (jets pairedPrime anchor20) k‖ := norm_add_le _ _
    _ ≤ K + C * (1 + (k : ℝ) ^ p) := by gcongr; exacts [hK k, h k]
    _ ≤ (C + K) * (1 + (k : ℝ) ^ p) := by nlinarith

end CriticalLinePhasor.SeatingLedger

#print axioms CriticalLinePhasor.SeatingLedger.pairedArchCoeff_bounded
#print axioms CriticalLinePhasor.SeatingLedger.rh_of_pairedPrime_polynomial
