import RequestProject.AnchorLadder

/-!
# The ladder at one anchor, part 2a: the minor bound and the transported atoms (ledger 630)

* `ladder_coeff_bound`: the ladder at `s` forces `‖μ_k‖ ≤ Re μ_0` for every `k` (the `2×2` minor on the
  vector `e_0 + θ e_k` with `θ = −μ_k/‖μ_k‖`);
* `norm_transport_sq`: `‖w_ρ‖² = 1 + (2Re ρ − 1)(2Re s − 1)/|s−ρ|²`, so in the channel `‖w_ρ‖ > 1` exactly
  for zeros with `Re ρ < ½`;
* mirror symmetry of the zero set, injectivity of the transport, non-vanishing and summability of the
  weights, and a uniform bound on `‖w_ρ‖`.
-/

open Complex Finset

namespace CriticalLinePhasor.SeatingLedger

/-! ## Sesquilinear expansion of the Toeplitz form -/

noncomputable def toeplitzBil (μ : ℤ → ℂ) {N : ℕ} (u v : Fin N → ℂ) : ℂ :=
  ∑ j : Fin N, ∑ l : Fin N, (starRingEnd ℂ) (u j) * v l * μ ((j : ℤ) - (l : ℤ))

theorem toeplitzForm_eq_bil (μ : ℤ → ℂ) {N : ℕ} (c : Fin N → ℂ) :
    toeplitzForm μ c = toeplitzBil μ c c := rfl

theorem toeplitzBil_add_left (μ : ℤ → ℂ) {N : ℕ} (u u' v : Fin N → ℂ) :
    toeplitzBil μ (u + u') v = toeplitzBil μ u v + toeplitzBil μ u' v := by
  unfold toeplitzBil
  simp only [Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib]

theorem toeplitzBil_add_right (μ : ℤ → ℂ) {N : ℕ} (u v v' : Fin N → ℂ) :
    toeplitzBil μ u (v + v') = toeplitzBil μ u v + toeplitzBil μ u v' := by
  unfold toeplitzBil
  simp only [Pi.add_apply, mul_add, add_mul, Finset.sum_add_distrib]

theorem toeplitzBil_single (μ : ℤ → ℂ) {N : ℕ} (a b : Fin N) (x y : ℂ) :
    toeplitzBil μ (Pi.single a x) (Pi.single b y)
      = (starRingEnd ℂ) x * y * μ ((a : ℤ) - (b : ℤ)) := by
  unfold toeplitzBil
  rw [Finset.sum_eq_single a]
  · rw [Finset.sum_eq_single b]
    · simp
    · intro l _ hl
      simp [Pi.single_eq_of_ne hl]
    · intro h; exact absurd (Finset.mem_univ b) h
  · intro j _ hj
    simp [Pi.single_eq_of_ne hj]
  · intro h; exact absurd (Finset.mem_univ a) h

theorem toeplitzForm_two_singles (μ : ℤ → ℂ) {N : ℕ} (a b : Fin N) (x y : ℂ) :
    toeplitzForm μ (Pi.single a x + Pi.single b y)
      = (starRingEnd ℂ) x * x * μ ((a : ℤ) - (a : ℤ)) + (starRingEnd ℂ) x * y * μ ((a : ℤ) - (b : ℤ))
        + ((starRingEnd ℂ) y * x * μ ((b : ℤ) - (a : ℤ)) + (starRingEnd ℂ) y * y * μ ((b : ℤ) - (b : ℤ))) := by
  rw [toeplitzForm_eq_bil, toeplitzBil_add_left, toeplitzBil_add_right, toeplitzBil_add_right,
    toeplitzBil_single, toeplitzBil_single, toeplitzBil_single, toeplitzBil_single]

theorem hermExt_natCast (μ : ℕ → ℂ) (k : ℕ) : hermExt μ (k : ℤ) = μ k := by
  unfold hermExt
  rw [if_pos (Int.natCast_nonneg k), Int.toNat_natCast]

theorem hermExt_zero (μ : ℕ → ℂ) : hermExt μ 0 = μ 0 := by
  unfold hermExt; simp

theorem hermExt_neg_natCast (μ : ℕ → ℂ) {k : ℕ} (hk : 0 < k) :
    hermExt μ (-(k : ℤ)) = (starRingEnd ℂ) (μ k) := by
  unfold hermExt
  rw [if_neg (by omega), neg_neg, Int.toNat_natCast]

/-- The zeroth coefficient of a ladder anchor is a nonnegative real. -/
theorem ladder_coeff_zero {s : ℂ} (hL : Ladder s) :
    (xiCoeff s 0).im = 0 ∧ 0 ≤ (xiCoeff s 0).re := by
  have h := hL 1 (Pi.single (0 : Fin 1) 1)
  rw [toeplitzForm_eq_bil, toeplitzBil_single] at h
  simpa [hermExt] using h

/-- **The minor bound**: the ladder forces `‖μ_k‖ ≤ μ_0`. -/
theorem ladder_coeff_bound {s : ℂ} (hL : Ladder s) (k : ℕ) :
    ‖xiCoeff s k‖ ≤ (xiCoeff s 0).re := by
  obtain ⟨h0im, h0re⟩ := ladder_coeff_zero hL
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · have e : xiCoeff s 0 = ((xiCoeff s 0).re : ℂ) := Complex.ext (by simp) (by simp [h0im])
    conv_lhs => rw [e]
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg h0re]
  · by_cases hz : xiCoeff s k = 0
    · rw [hz, norm_zero]; exact h0re
    · have hn : (‖xiCoeff s k‖ : ℂ) ≠ 0 := by exact_mod_cast (norm_ne_zero_iff.mpr hz)
      set θ : ℂ := -(xiCoeff s k) / (‖xiCoeff s k‖ : ℂ) with hθ
      have hab : (0 : Fin (k + 1)) ≠ Fin.last k := by
        intro h; have := congrArg Fin.val h; simp at this; omega
      have h := hL (k + 1) (Pi.single 0 1 + Pi.single (Fin.last k) θ)
      rw [toeplitzForm_two_singles] at h
      simp only [Fin.val_zero, Fin.val_last, Nat.cast_zero, sub_self, zero_sub, sub_zero,
        hermExt_natCast, hermExt_zero, map_one, one_mul, mul_one] at h
      rw [hermExt_neg_natCast _ hk] at h
      have hmc : (xiCoeff s k) * (starRingEnd ℂ) (xiCoeff s k)
          = (‖xiCoeff s k‖ : ℂ) * (‖xiCoeff s k‖ : ℂ) := by
        rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; ring
      have hθ1 : θ * (starRingEnd ℂ) (xiCoeff s k) = -(‖xiCoeff s k‖ : ℂ) := by
        rw [hθ, show -xiCoeff s k / (‖xiCoeff s k‖ : ℂ) * (starRingEnd ℂ) (xiCoeff s k)
            = -(xiCoeff s k * (starRingEnd ℂ) (xiCoeff s k)) / (‖xiCoeff s k‖ : ℂ) by ring,
          hmc, neg_div, mul_div_assoc, div_self hn, mul_one]
      have hθ2 : (starRingEnd ℂ) θ * xiCoeff s k = -(‖xiCoeff s k‖ : ℂ) := by
        rw [hθ, map_div₀, map_neg, Complex.conj_ofReal,
          show -(starRingEnd ℂ) (xiCoeff s k) / (‖xiCoeff s k‖ : ℂ) * xiCoeff s k
            = -(xiCoeff s k * (starRingEnd ℂ) (xiCoeff s k)) / (‖xiCoeff s k‖ : ℂ) by ring,
          hmc, neg_div, mul_div_assoc, div_self hn, mul_one]
      have hθ3 : (starRingEnd ℂ) θ * θ = 1 := by
        rw [hθ, map_div₀, map_neg, Complex.conj_ofReal,
          show -(starRingEnd ℂ) (xiCoeff s k) / (‖xiCoeff s k‖ : ℂ)
              * (-xiCoeff s k / (‖xiCoeff s k‖ : ℂ))
            = (xiCoeff s k * (starRingEnd ℂ) (xiCoeff s k))
              / ((‖xiCoeff s k‖ : ℂ) * (‖xiCoeff s k‖ : ℂ)) by ring,
          hmc, div_self (mul_ne_zero hn hn)]
      rw [hθ1, hθ2, hθ3] at h
      have hre := h.2
      simp only [Complex.add_re, Complex.neg_re, Complex.ofReal_re, one_mul] at hre
      linarith

/-! ## The transported atoms -/

/-- `‖w_ρ‖² = 1 + (2 Re ρ − 1)(2 Re s − 1)/|s − ρ|²`. -/
theorem norm_transport_sq (s ρ : ℂ) (h : s - ρ ≠ 0) :
    ‖transport s ρ‖ ^ 2 = 1 + (2 * ρ.re - 1) * (2 * s.re - 1) / Complex.normSq (s - ρ) := by
  have hn : Complex.normSq (s - ρ) ≠ 0 := by rwa [Ne, Complex.normSq_eq_zero]
  unfold transport
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_div, ← normSq_sub_mirror]
  field_simp
  ring

/-- In the channel, the transported atom lies outside the circle iff the zero is left of the line. -/
theorem one_lt_norm_transport_iff {s ρ : ℂ} (hs : s.re < 1 / 2) (h : s - ρ ≠ 0) :
    1 < ‖transport s ρ‖ ↔ ρ.re < 1 / 2 := by
  have hn : 0 < Complex.normSq (s - ρ) := by rw [Complex.normSq_pos]; exact h
  have hsq := norm_transport_sq s ρ h
  have hd : 2 * s.re - 1 < 0 := by linarith
  constructor
  · intro h1
    have : 1 < ‖transport s ρ‖ ^ 2 := by nlinarith [norm_nonneg (transport s ρ)]
    rw [hsq] at this
    have hpos : 0 < (2 * ρ.re - 1) * (2 * s.re - 1) / Complex.normSq (s - ρ) := by linarith
    have : 0 < (2 * ρ.re - 1) * (2 * s.re - 1) := (div_pos_iff_of_pos_right hn).mp hpos
    nlinarith
  · intro hρ
    have hpos : 0 < (2 * ρ.re - 1) * (2 * s.re - 1) := by nlinarith
    have : 1 < ‖transport s ρ‖ ^ 2 := by rw [hsq]; have := div_pos hpos hn; linarith
    nlinarith [norm_nonneg (transport s ρ)]

/-- The mirror `1 − ρ̄` of a nontrivial zero is a nontrivial zero. -/
theorem mirror_mem_nontrivialZeros {ρ : ℂ} (hρ : ρ ∈ ZD.NontrivialZeros) :
    1 - (starRingEnd ℂ) ρ ∈ ZD.NontrivialZeros := by
  apply (ZD.riemannXi_eq_zero_iff _).mp
  rw [CriticalLinePhasor.ContourArgument.riemannXi_one_sub_conj,
    (ZD.riemannXi_eq_zero_iff ρ).mpr hρ, map_zero]

theorem mirror_notMem_nontrivialZeros {s : ℂ} (hs : s ∉ ZD.NontrivialZeros) :
    1 - (starRingEnd ℂ) s ∉ ZD.NontrivialZeros := by
  intro h
  have := mirror_mem_nontrivialZeros h
  simp only [map_sub, map_one, Complex.conj_conj, sub_sub_cancel] at this
  exact hs this

/-- The transport is injective (a Möbius map). -/
theorem transport_injective {s ρ ρ' : ℂ} (hs : s.re ≠ 1 / 2) (h1 : s - ρ ≠ 0) (h2 : s - ρ' ≠ 0)
    (h : transport s ρ = transport s ρ') : ρ = ρ' := by
  unfold transport at h
  rw [div_eq_div_iff h1 h2] at h
  have hd : s - (1 - (starRingEnd ℂ) s) ≠ 0 := by
    rw [mirror_d]
    have : (2 * s.re - 1 : ℝ) ≠ 0 := by intro h0; apply hs; linarith
    exact_mod_cast this
  have : (ρ - ρ') * (s - (1 - (starRingEnd ℂ) s)) = 0 := by linear_combination h
  rcases mul_eq_zero.mp this with h0 | h0
  · exact sub_eq_zero.mp h0
  · exact absurd h0 hd

theorem atomWeight_ne_zero {s ρ : ℂ} (h1 : s - ρ ≠ 0) (h2 : ρ - (1 - (starRingEnd ℂ) s) ≠ 0) :
    atomWeight s ρ ≠ 0 := by
  unfold atomWeight; exact inv_ne_zero (mul_ne_zero h1 h2)

/-- A positive constant `κ` with `κ‖ρ‖ ≤ ‖s − ρ‖` on the zeros, for `s` off the zero set. -/
theorem exists_kappa {s : ℂ} (hs : s ∉ ZD.NontrivialZeros) :
    ∃ κ > 0, ∀ ρ ∈ ZD.NontrivialZeros, κ * ‖ρ‖ ≤ ‖s - ρ‖ := by
  obtain ⟨δ, hδ, hball⟩ := exists_zero_free_ball hs
  refine ⟨δ / (‖s‖ + δ), by positivity, fun ρ hρ => ?_⟩
  rcases le_or_gt ‖ρ‖ (‖s‖ + δ) with h | h
  · calc δ / (‖s‖ + δ) * ‖ρ‖ ≤ δ / (‖s‖ + δ) * (‖s‖ + δ) := by gcongr
      _ = δ := by field_simp
      _ ≤ ‖s - ρ‖ := hball ρ hρ
  · have h1 : ‖ρ‖ - ‖s‖ ≤ ‖s - ρ‖ := by
      have := norm_sub_norm_le ρ s
      rw [norm_sub_rev] at this; linarith
    have h2 : δ / (‖s‖ + δ) * ‖ρ‖ ≤ ‖ρ‖ - ‖s‖ := by
      rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
      nlinarith [norm_nonneg s]
    linarith

/-- The absolute weights `m_ρ ‖ω_ρ‖` are summable (`s` off the zeros, hence so is its mirror). -/
theorem summable_absWeight {s : ℂ} (hs : s ∉ ZD.NontrivialZeros) :
    Summable (fun ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros} =>
      (ZD.xiOrderNat ρ.val : ℝ) * ‖atomWeight s ρ.val‖) := by
  obtain ⟨κ, hκ, hκs⟩ := exists_kappa hs
  obtain ⟨κ', hκ', hκc⟩ := exists_kappa (mirror_notMem_nontrivialZeros hs)
  have hbase := ZD.summable_xiOrderNat_div_norm_sq_nontrivialZeros
  refine Summable.of_nonneg_of_le (fun ρ => by positivity) (fun ρ => ?_)
    (hbase.mul_left (1 / (κ * κ')))
  have hρne : ρ.val ≠ 0 := by
    intro h; have := ρ.property; rw [h] at this; obtain ⟨h1, -, -⟩ := this; simp at h1
  have hρpos : 0 < ‖ρ.val‖ := norm_pos_iff.mpr hρne
  have hA := hκs ρ.val ρ.property
  have hB : κ' * ‖ρ.val‖ ≤ ‖ρ.val - (1 - (starRingEnd ℂ) s)‖ := by
    rw [norm_sub_rev]; exact hκc ρ.val ρ.property
  have hw : ‖atomWeight s ρ.val‖ = (‖s - ρ.val‖ * ‖ρ.val - (1 - (starRingEnd ℂ) s)‖)⁻¹ := by
    unfold atomWeight; rw [norm_inv, norm_mul]
  rw [hw]
  have hprod : (κ * ‖ρ.val‖) * (κ' * ‖ρ.val‖) ≤ ‖s - ρ.val‖ * ‖ρ.val - (1 - (starRingEnd ℂ) s)‖ :=
    mul_le_mul hA hB (by positivity) (norm_nonneg _)
  calc (ZD.xiOrderNat ρ.val : ℝ) * (‖s - ρ.val‖ * ‖ρ.val - (1 - (starRingEnd ℂ) s)‖)⁻¹
      ≤ (ZD.xiOrderNat ρ.val : ℝ) * ((κ * ‖ρ.val‖) * (κ' * ‖ρ.val‖))⁻¹ := by
        gcongr
    _ = 1 / (κ * κ') * ((ZD.xiOrderNat ρ.val : ℝ) / ‖ρ.val‖ ^ 2) := by
        field_simp

/-- A uniform bound on the transported atoms, for `s` off the zeros. -/
theorem exists_transport_bound {s : ℂ} (hs : s ∉ ZD.NontrivialZeros) :
    ∃ R₀ : ℝ, ∀ ρ ∈ ZD.NontrivialZeros, ‖transport s ρ‖ ≤ R₀ := by
  obtain ⟨δ, hδ, hball⟩ := exists_zero_free_ball hs
  refine ⟨Real.sqrt (1 + |2 * s.re - 1| / δ ^ 2), fun ρ hρ => ?_⟩
  have h : s - ρ ≠ 0 := sub_ne_zero_of_notMem hs hρ
  rw [← Real.sqrt_sq (norm_nonneg (transport s ρ)), norm_transport_sq s ρ h]
  apply Real.sqrt_le_sqrt
  have hn : δ ^ 2 ≤ Complex.normSq (s - ρ) := by
    rw [Complex.normSq_eq_norm_sq]; exact pow_le_pow_left₀ hδ.le (hball ρ hρ) 2
  have hnpos : 0 < Complex.normSq (s - ρ) := by rw [Complex.normSq_pos]; exact h
  have hnum : (2 * ρ.re - 1) * (2 * s.re - 1) ≤ |2 * s.re - 1| := by
    obtain ⟨h1, h2, -⟩ := hρ
    calc (2 * ρ.re - 1) * (2 * s.re - 1) ≤ |(2 * ρ.re - 1) * (2 * s.re - 1)| := le_abs_self _
      _ = |2 * ρ.re - 1| * |2 * s.re - 1| := abs_mul _ _
      _ ≤ 1 * |2 * s.re - 1| := by gcongr; rw [abs_le]; constructor <;> linarith
      _ = |2 * s.re - 1| := one_mul _
  have : (2 * ρ.re - 1) * (2 * s.re - 1) / Complex.normSq (s - ρ) ≤ |2 * s.re - 1| / δ ^ 2 := by
    calc (2 * ρ.re - 1) * (2 * s.re - 1) / Complex.normSq (s - ρ)
        ≤ |2 * s.re - 1| / Complex.normSq (s - ρ) := by gcongr
      _ ≤ |2 * s.re - 1| / δ ^ 2 := by gcongr
  linarith

end CriticalLinePhasor.SeatingLedger

#print axioms CriticalLinePhasor.SeatingLedger.ladder_coeff_bound
#print axioms CriticalLinePhasor.SeatingLedger.one_lt_norm_transport_iff
#print axioms CriticalLinePhasor.SeatingLedger.summable_absWeight
#print axioms CriticalLinePhasor.SeatingLedger.exists_transport_bound
