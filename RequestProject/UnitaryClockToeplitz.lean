import RequestProject.UnitaryClockJets

/-!
# Toeplitz positivity of the unitary clock at every degree (ledger 624, stage 2)

At an anchor `s` on the channel `Re s < ½`, the unitary clock's Toeplitz coefficients
(`toeplitzCoeff` of ledger 622, evaluated on the clock's jets) are the Fourier coefficients of the
**positive unimodular measure** `μ = Σ_n ω_n δ_{w_n}` on the unit circle, where `w_n = transport s
(tick n)` is the Cayley transport of the clock's `n`-th line zero and `ω_n = 1/|s − tick n|²` its
weight:

* `clock_toeplitzCoeff`: `μ̂_k = Σ_n ω_n w_n^k` for every `k` — the zeroth from the clock's mass
  (`clockS_re_logDeriv`), the higher ones from the jets (`clockS_jet`) through the per-zero binomial
  identity `transport_pow_identity`;
* `toeplitzForm_atomCoeff` (Gram identity): the Toeplitz form of such a measure is
  `Σ_n ω_n |Σ_j c̄_j w_n^j|²`;
* `unitaryClock_toeplitz_psd`: **the clock's Toeplitz form is real and nonnegative at every degree
  `N` and every vector `c`.**

The Toeplitz form is linear in the coefficient sequence (`toeplitzForm_add`, `hermExt_add`), so this
is the clock-face summand of the seat's degree-`N` marriage.
-/

open Complex Finset Filter Topology Real
open CriticalLinePhasor.ChiralityHB

namespace CriticalLinePhasor.SeatingLedger

/-! ## The Toeplitz form of a two-sided coefficient sequence -/

/-- Fourier coefficients of the positive unimodular measure `Σ_n ω_n δ_{w_n}`. -/
noncomputable def atomCoeff (ω : ℤ → ℝ) (w : ℤ → ℂ) (k : ℤ) : ℂ := ∑' n : ℤ, (ω n : ℂ) * w n ^ k

/-- The Toeplitz form `Σ_{j,l} c̄_j c_l μ_{j−l}` of a two-sided coefficient sequence on `Fin N`. -/
noncomputable def toeplitzForm (μ : ℤ → ℂ) {N : ℕ} (c : Fin N → ℂ) : ℂ :=
  ∑ j : Fin N, ∑ l : Fin N, (starRingEnd ℂ) (c j) * c l * μ ((j : ℤ) - (l : ℤ))

/-- The Hermitian extension of one-sided coefficients: `μ_{−k} = conj μ_k`. -/
noncomputable def hermExt (μ : ℕ → ℂ) : ℤ → ℂ :=
  fun k => if 0 ≤ k then μ k.toNat else (starRingEnd ℂ) (μ (-k).toNat)

theorem toeplitzForm_add (μ μ' : ℤ → ℂ) {N : ℕ} (c : Fin N → ℂ) :
    toeplitzForm (μ + μ') c = toeplitzForm μ c + toeplitzForm μ' c := by
  unfold toeplitzForm
  simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem hermExt_add (μ μ' : ℕ → ℂ) : hermExt (μ + μ') = hermExt μ + hermExt μ' := by
  funext k
  unfold hermExt
  by_cases hk : 0 ≤ k <;> simp [hk]

/-! ## The Gram identity for a positive unimodular measure -/

section Gram
variable {ω : ℤ → ℝ} {w : ℤ → ℂ}

theorem summable_atom (hs : Summable ω) (hw : ∀ n, ‖w n‖ = 1) (k : ℤ) :
    Summable (fun n : ℤ => (ω n : ℂ) * w n ^ k) := by
  refine Summable.of_norm_bounded hs.abs (fun n => le_of_eq ?_)
  rw [norm_mul, norm_zpow, hw, one_zpow, mul_one, Complex.norm_real, Real.norm_eq_abs]

theorem atom_ne_zero (hw : ∀ n, ‖w n‖ = 1) (n : ℤ) : w n ≠ 0 := by
  intro h
  have := hw n
  rw [h, norm_zero] at this
  exact zero_ne_one this

theorem atom_zpow_inv (hw : ∀ n, ‖w n‖ = 1) (n : ℤ) (k : ℤ) :
    (w n ^ k)⁻¹ = (starRingEnd ℂ) (w n ^ k) :=
  Complex.inv_eq_conj (by rw [norm_zpow, hw, one_zpow])

/-- The coefficients are Hermitian: `μ̂_{−k} = conj μ̂_k`. -/
theorem atomCoeff_conj (hs : Summable ω) (hw : ∀ n, ‖w n‖ = 1) (k : ℤ) :
    (starRingEnd ℂ) (atomCoeff ω w k) = atomCoeff ω w (-k) := by
  unfold atomCoeff
  have h := ((summable_atom hs hw k).hasSum.map (starRingEnd ℂ) Complex.continuous_conj).tsum_eq
  rw [← h]
  apply tsum_congr
  intro n
  simp only [Function.comp_apply, map_mul, Complex.conj_ofReal]
  rw [← atom_zpow_inv hw n k, zpow_neg]

/-- **Gram identity**: the Toeplitz form of `Σ ω_n δ_{w_n}` is `Σ_n ω_n |Σ_j c̄_j w_n^j|²`. -/
theorem toeplitzForm_atomCoeff (hs : Summable ω) (hw : ∀ n, ‖w n‖ = 1) {N : ℕ} (c : Fin N → ℂ) :
    toeplitzForm (atomCoeff ω w) c
      = ∑' n : ℤ, ((ω n * Complex.normSq
          (∑ j : Fin N, (starRingEnd ℂ) (c j) * w n ^ (j : ℤ)) : ℝ) : ℂ) := by
  unfold toeplitzForm atomCoeff
  have hsum : ∀ (j l : Fin N), Summable (fun n : ℤ =>
      (starRingEnd ℂ) (c j) * c l * ((ω n : ℂ) * w n ^ ((j : ℤ) - (l : ℤ)))) :=
    fun j l => (summable_atom hs hw _).mul_left _
  have step1 : ∀ j : Fin N,
      ∑ l : Fin N, (starRingEnd ℂ) (c j) * c l * ∑' n : ℤ, (ω n : ℂ) * w n ^ ((j : ℤ) - (l : ℤ))
        = ∑' n : ℤ, ∑ l : Fin N,
            (starRingEnd ℂ) (c j) * c l * ((ω n : ℂ) * w n ^ ((j : ℤ) - (l : ℤ))) := by
    intro j
    rw [Summable.tsum_finsetSum (fun l _ => hsum j l)]
    exact Finset.sum_congr rfl (fun l _ => (tsum_mul_left).symm)
  rw [Finset.sum_congr rfl (fun j _ => step1 j),
    ← Summable.tsum_finsetSum (fun j _ => summable_sum (fun l _ => hsum j l))]
  apply tsum_congr
  intro n
  have hterm : ∀ (j l : ℤ), (ω n : ℂ) * w n ^ (j - l)
      = (ω n : ℂ) * (w n ^ j * (starRingEnd ℂ) (w n ^ l)) := by
    intro j l
    rw [zpow_sub₀ (atom_ne_zero hw n), div_eq_mul_inv, atom_zpow_inv hw n l]
  simp_rw [hterm]
  rw [Complex.ofReal_mul, ← Complex.mul_conj, map_sum, Finset.sum_mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  simp only [map_mul, Complex.conj_conj]
  ring

/-- **Positivity at every degree**: the Toeplitz form of a positive unimodular measure is real and
nonnegative. -/
theorem toeplitzForm_atomCoeff_nonneg (hω : ∀ n, 0 ≤ ω n) (hs : Summable ω)
    (hw : ∀ n, ‖w n‖ = 1) {N : ℕ} (c : Fin N → ℂ) :
    (toeplitzForm (atomCoeff ω w) c).im = 0 ∧ 0 ≤ (toeplitzForm (atomCoeff ω w) c).re := by
  rw [toeplitzForm_atomCoeff hs hw c, ← Complex.ofReal_tsum]
  refine ⟨Complex.ofReal_im _, ?_⟩
  rw [Complex.ofReal_re]
  exact tsum_nonneg (fun n => mul_nonneg (hω n) (Complex.normSq_nonneg _))

end Gram

/-! ## The unitary clock's coefficients are those of `Σ_n ω_n δ_{w_n}` -/

/-- The jets of the unitary clock at `s`: `S_1 = logDeriv`, `S_m = Σ_n (s − tick n)^{−m}` (`m ≥ 2`). -/
noncomputable def clockJet (θ ℓ : ℝ) (s : ℂ) : ℕ → ℂ
  | 0 => 0
  | 1 => logDeriv (clockS θ ℓ) s
  | m + 2 => ∑' n : ℤ, ((s - tick θ ℓ n)⁻¹) ^ (m + 2)

theorem clockJet_one (θ ℓ : ℝ) (s : ℂ) : clockJet θ ℓ s 1 = logDeriv (clockS θ ℓ) s := rfl

theorem clockJet_of_two_le (θ ℓ : ℝ) (s : ℂ) {m : ℕ} (hm : 2 ≤ m) :
    clockJet θ ℓ s m = ∑' n : ℤ, ((s - tick θ ℓ n)⁻¹) ^ m := by
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 2 := ⟨m - 2, by omega⟩
  rfl

/-- The jets are the iterated log-derivatives (`m ≥ 2`). -/
theorem clockJet_eq_iteratedDeriv {θ ℓ : ℝ} (hℓ : 0 < ℓ) {s : ℂ} (hs : s.re < 1 / 2) {m : ℕ}
    (hm : 2 ≤ m) :
    iteratedDeriv (m - 1) (logDeriv (clockS θ ℓ)) s
      = (-1) ^ (m - 1) * ((m - 1).factorial : ℂ) * clockJet θ ℓ s m := by
  rw [clockJet_of_two_le θ ℓ s hm, clockS_jet hℓ (k := m - 1) (by omega) hs,
    show m - 1 + 1 = m by omega]

/-- `s − tick n ≠ 0` on the channel. -/
theorem sub_tick_ne_zero {θ ℓ : ℝ} (hℓ : 0 < ℓ) {s : ℂ} (hs : s.re < 1 / 2) (n : ℤ) :
    s - tick θ ℓ n ≠ 0 := by
  intro h
  have := congrArg Complex.re h
  rw [Complex.sub_re, tick_re θ hℓ n, Complex.zero_re] at this
  linarith

/-- On the line, the mirror displacement is the conjugate of the anchor displacement:
`ρ − c = conj (s − ρ)`, `c = 1 − s̄`. -/
theorem sub_mirror_eq_conj {s ρ : ℂ} (hρ : ρ.re = 1 / 2) :
    ρ - (1 - (starRingEnd ℂ) s) = (starRingEnd ℂ) (s - ρ) := by
  apply Complex.ext
  · simp [hρ]; ring
  · simp; ring

/-- `d = s − c = 2σ − 1`. -/
theorem mirror_d (s : ℂ) : s - (1 - (starRingEnd ℂ) s) = ((2 * s.re - 1 : ℝ) : ℂ) := by
  apply Complex.ext
  · simp; ring
  · simp

/-- The transport of a line point is unimodular. -/
theorem transport_line_norm {s ρ : ℂ} (hρ : ρ.re = 1 / 2) (h : s - ρ ≠ 0) :
    ‖transport s ρ‖ = 1 := by
  unfold transport
  rw [sub_mirror_eq_conj hρ, norm_div, Complex.norm_conj, div_self (norm_ne_zero_iff.mpr h)]

theorem norm_inv_sub_tick_le {θ ℓ : ℝ} (hℓ : 0 < ℓ) {s : ℂ} (hs : s.re < 1 / 2) (n : ℤ) :
    ‖(s - tick θ ℓ n)⁻¹‖ ≤ 1 / (1 / 2 - s.re) := by
  rw [norm_inv, ← one_div]
  have hre : 1 / 2 - s.re ≤ ‖s - tick θ ℓ n‖ := by
    have := Complex.abs_re_le_norm (s - tick θ ℓ n)
    rw [Complex.sub_re, tick_re θ hℓ n] at this
    calc 1 / 2 - s.re = |s.re - 1 / 2| := by rw [abs_sub_comm, abs_of_pos (by linarith)]
      _ ≤ _ := this
  exact one_div_le_one_div_of_le (by linarith) hre

theorem norm_inv_sub_tick_sq (θ ℓ : ℝ) (s : ℂ) (n : ℤ) :
    ‖(s - tick θ ℓ n)⁻¹‖ ^ 2 = tickWeight θ ℓ s n := by
  rw [norm_inv, inv_pow, ← Complex.normSq_eq_norm_sq]
  unfold tickWeight
  rw [one_div]

/-- The pure powers `(s − tick n)^{−m}`, `m ≥ 2`, are summable. -/
theorem summable_tickPow {θ ℓ : ℝ} (hℓ : 0 < ℓ) {s : ℂ} (hs : s.re < 1 / 2) {m : ℕ} (hm : 2 ≤ m) :
    Summable (fun n : ℤ => ((s - tick θ ℓ n)⁻¹) ^ m) := by
  obtain ⟨j, rfl⟩ : ∃ j, m = j + 2 := ⟨m - 2, by omega⟩
  refine Summable.of_norm_bounded
    ((summable_tickWeight θ hℓ s).mul_left ((1 / (1 / 2 - s.re)) ^ j)) (fun n => ?_)
  rw [norm_pow, pow_add, norm_inv_sub_tick_sq θ ℓ s n]
  exact mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ (norm_nonneg _) (norm_inv_sub_tick_le hℓ hs n) j) (tickWeight_nonneg θ ℓ s n)

/-- **The clock's Toeplitz coefficients are the Fourier coefficients of `Σ_n ω_n δ_{w_n}`.** -/
theorem clock_toeplitzCoeff {θ ℓ : ℝ} (hℓ : 0 < ℓ) {s : ℂ} (hs : s.re < 1 / 2) (k : ℕ) :
    toeplitzCoeff ((2 * s.re - 1 : ℝ) : ℂ) (clockJet θ ℓ s) k
      = atomCoeff (tickWeight θ ℓ s) (fun n => transport s (tick θ ℓ n)) k := by
  have hz := sub_tick_ne_zero (θ := θ) hℓ hs
  cases k with
  | zero =>
    simp only [toeplitzCoeff, clockJet_one, atomCoeff, Nat.cast_zero, zpow_zero, mul_one]
    rw [clockS_re_logDeriv hℓ hs, ← Complex.ofReal_tsum]
    have hd : (2 * (s.re : ℂ) - 1) ≠ 0 := by
      have : (2 * s.re - 1 : ℝ) ≠ 0 := by intro h; linarith
      exact_mod_cast this
    push_cast
    field_simp
  | succ k =>
    simp only [toeplitzCoeff]
    have hjet : ∀ i ∈ range (k + 1),
        clockJet θ ℓ s (k + 2 - i) = ∑' n : ℤ, ((s - tick θ ℓ n)⁻¹) ^ (k + 2 - i) := by
      intro i hi
      rw [mem_range] at hi
      exact clockJet_of_two_le θ ℓ s (by omega)
    have hL : ∑ i ∈ range (k + 1), ((k.choose i : ℂ) * ((2 * s.re - 1 : ℝ) : ℂ) ^ (k - i)
          * (-1) ^ i * clockJet θ ℓ s (k + 2 - i))
        = ∑' n : ℤ, ∑ i ∈ range (k + 1), ((k.choose i : ℂ) * ((2 * s.re - 1 : ℝ) : ℂ) ^ (k - i)
          * (-1) ^ i * ((s - tick θ ℓ n)⁻¹) ^ (k + 2 - i)) := by
      rw [Summable.tsum_finsetSum (fun i hi => (summable_tickPow hℓ hs
        (by rw [mem_range] at hi; omega)).mul_left _)]
      exact Finset.sum_congr rfl (fun i hi => by rw [hjet i hi, tsum_mul_left])
    rw [hL]
    unfold atomCoeff
    apply tsum_congr
    intro n
    have hid := transport_pow_identity s (tick θ ℓ n) (hz n) k
    rw [mirror_d] at hid
    rw [← hid, zpow_natCast, sub_mirror_eq_conj (tick_re θ hℓ n)]
    simp only [transport]
    rw [sub_mirror_eq_conj (tick_re θ hℓ n)]
    unfold tickWeight
    rw [Complex.ofReal_div, Complex.ofReal_one, ← Complex.mul_conj]
    have hc : (starRingEnd ℂ) (s - tick θ ℓ n) ≠ 0 := (map_ne_zero _).mpr (hz n)
    have hz' := hz n
    clear hid hL hjet hz
    generalize s - tick θ ℓ n = z at hc hz' ⊢
    have hck : (starRingEnd ℂ) z ^ k = ((starRingEnd ℂ) z)⁻¹ * (starRingEnd ℂ) z ^ (k + 1) := by
      rw [pow_succ', inv_mul_cancel_left₀ hc]
    rw [hck]
    ring

/-- **Toeplitz positivity of the unitary clock at every degree.** For every anchor on the channel,
every degree `N` and every `c : Fin N → ℂ`, the Toeplitz form of the clock's (Hermitian-extended)
coefficients is real and nonnegative. -/
theorem unitaryClock_toeplitz_psd {θ ℓ : ℝ} (hℓ : 0 < ℓ) {s : ℂ} (hs : s.re < 1 / 2) {N : ℕ}
    (c : Fin N → ℂ) :
    (toeplitzForm (hermExt (toeplitzCoeff ((2 * s.re - 1 : ℝ) : ℂ) (clockJet θ ℓ s))) c).im = 0 ∧
    0 ≤ (toeplitzForm (hermExt (toeplitzCoeff ((2 * s.re - 1 : ℝ) : ℂ) (clockJet θ ℓ s))) c).re := by
  have hw : ∀ n : ℤ, ‖transport s (tick θ ℓ n)‖ = 1 :=
    fun n => transport_line_norm (tick_re θ hℓ n) (sub_tick_ne_zero hℓ hs n)
  have hsw := summable_tickWeight θ hℓ s
  have hext : hermExt (toeplitzCoeff ((2 * s.re - 1 : ℝ) : ℂ) (clockJet θ ℓ s))
      = atomCoeff (tickWeight θ ℓ s) (fun n => transport s (tick θ ℓ n)) := by
    funext k
    unfold hermExt
    split_ifs with hk
    · rw [clock_toeplitzCoeff hℓ hs, Int.toNat_of_nonneg hk]
    · rw [clock_toeplitzCoeff hℓ hs, atomCoeff_conj hsw hw, Int.toNat_of_nonneg (by omega), neg_neg]
  rw [hext]
  exact toeplitzForm_atomCoeff_nonneg (tickWeight_nonneg θ ℓ s) hsw hw c

end CriticalLinePhasor.SeatingLedger

#print axioms CriticalLinePhasor.SeatingLedger.toeplitzForm_atomCoeff_nonneg
#print axioms CriticalLinePhasor.SeatingLedger.clock_toeplitzCoeff
#print axioms CriticalLinePhasor.SeatingLedger.unitaryClock_toeplitz_psd
