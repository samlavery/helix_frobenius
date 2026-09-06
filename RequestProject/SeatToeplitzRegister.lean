import RequestProject.SeatingMassWrap
import RequestProject.FaceMarriageIdentity

/-!
# The seat form in the Toeplitz (Cayley) register (ledger 622)

At an anchor `s` with mirror `c = 1 − s̄` and `d = s − c = 2σ − 1`, the Möbius map
`transport s ρ = (ρ − c)/(s − ρ)` sends the critical line to the unit circle and nothing else to it
(`transport_norm_eq_one_iff`): the seat's own Cayley step, the 3D → 2D descent of the zeros at
anchor `s`. With `x = 1/(s−ρ)`, `x′ = 1/(ρ−c)` one has `(s−ρ) + (ρ−c) = d`, so the degree-N seat
form is the Toeplitz form of the measure `μ_s = Σ_ρ x x′ · δ_{transport s ρ}` with Fourier
coefficients `μ̂_n = Σ_ρ x^{n+1} x′^{1−n}`. Per zero (`transport_pow_identity`) `x^{n+1}(1/x′)^{n−1}`
is a binomial combination of the pure powers `x^m`, `2 ≤ m ≤ n+1`; hence the higher coefficients
are combinations of the jets `S_m = Σ_ρ (s−ρ)^{−m}`, `m ≥ 2`, only, and the zeroth is
`2 Re S_1/d = seatMass s` (`toeplitzCoeff_zero_eq_seatMass`). The functional is linear in the jets
(`toeplitzCoeff_add`), so the face marriage `logDeriv ξ = E + M_Q + A_Q` splits the Toeplitz matrix
into three faces exactly. Measured (att622b, RH-verified range): the total is PSD with a tiny
minimum (the transported measure is nearly a point mass at `w = 1` near the line), the ends face
is a negative scalar, the clock face negative-definite, the ordered face positive-definite.
-/

open Complex Finset

namespace CriticalLinePhasor.SeatingLedger

/-- The transported point of `ρ` at anchor `s`: `(ρ − c)/(s − ρ)`, `c = 1 − s̄`. -/
noncomputable def transport (s ρ : ℂ) : ℂ := (ρ - (1 - (starRingEnd ℂ) s)) / (s - ρ)

/-- `‖ρ − c‖² − ‖s − ρ‖² = (2 Re ρ − 1)(2 Re s − 1)`. -/
theorem normSq_sub_mirror (s ρ : ℂ) :
    Complex.normSq (ρ - (1 - (starRingEnd ℂ) s)) - Complex.normSq (s - ρ)
      = (2 * ρ.re - 1) * (2 * s.re - 1) := by
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im,
    Complex.conj_re, Complex.conj_im]
  ring

/-- **The transported point is unimodular exactly on the line** (anchor off the line). -/
theorem transport_norm_eq_one_iff {s ρ : ℂ} (hs : s.re ≠ 1 / 2) (h : s - ρ ≠ 0) :
    ‖transport s ρ‖ = 1 ↔ ρ.re = 1 / 2 := by
  unfold transport
  rw [norm_div, div_eq_one_iff_eq (norm_ne_zero_iff.mpr h)]
  have hkey := normSq_sub_mirror s ρ
  have hs' : 2 * s.re - 1 ≠ 0 := by
    intro h0; apply hs; linarith
  constructor
  · intro heq
    have hsq : Complex.normSq (ρ - (1 - (starRingEnd ℂ) s)) = Complex.normSq (s - ρ) := by
      rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq, heq]
    have : (2 * ρ.re - 1) * (2 * s.re - 1) = 0 := by linarith
    rcases mul_eq_zero.mp this with h1 | h1
    · linarith
    · exact absurd h1 hs'
  · intro hρ
    have : (2 * ρ.re - 1) * (2 * s.re - 1) = 0 := by rw [hρ]; ring
    have hsq : Complex.normSq (ρ - (1 - (starRingEnd ℂ) s)) = Complex.normSq (s - ρ) := by
      linarith
    rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq] at hsq
    exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp hsq

/-- The mirror sum: `(s − ρ) + (ρ − c) = d`. -/
theorem mirror_sum (s ρ : ℂ) :
    (s - ρ) + (ρ - (1 - (starRingEnd ℂ) s)) = s - (1 - (starRingEnd ℂ) s) := by
  ring

/-- **Per zero, the transported power is a binomial combination of the pure powers**:
`x^{n+2} (ρ − c)^{n} = Σ_{i ≤ n} C(n,i) d^{n−i} (−1)^i x^{n+2−i}`, `x = (s−ρ)⁻¹`, `d = s − c`. This is
`μ̂_{n+1}`'s per-zero term written in the jets `S_2, …, S_{n+2}`. -/
theorem transport_pow_identity (s ρ : ℂ) (h : s - ρ ≠ 0) (n : ℕ) :
    (s - ρ)⁻¹ ^ (n + 2) * (ρ - (1 - (starRingEnd ℂ) s)) ^ n
      = ∑ i ∈ range (n + 1), (n.choose i : ℂ) * (s - (1 - (starRingEnd ℂ) s)) ^ (n - i)
          * (-1) ^ i * (s - ρ)⁻¹ ^ (n + 2 - i) := by
  have hc : ρ - (1 - (starRingEnd ℂ) s) = -(s - ρ) + (s - (1 - (starRingEnd ℂ) s)) := by ring
  rw [hc, add_pow, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i hi => ?_)
  rw [Finset.mem_range] at hi
  have hi' : i ≤ n := by omega
  have hsplit : (s - ρ)⁻¹ ^ (n + 2) = (s - ρ)⁻¹ ^ (n + 2 - i) * (s - ρ)⁻¹ ^ i := by
    rw [← pow_add]; congr 1; omega
  have hcancel : (s - ρ)⁻¹ ^ i * (s - ρ) ^ i = 1 := by
    rw [← mul_pow, inv_mul_cancel₀ h, one_pow]
  rw [neg_pow, hsplit]
  calc (s - ρ)⁻¹ ^ (n + 2 - i) * (s - ρ)⁻¹ ^ i
        * ((-1) ^ i * (s - ρ) ^ i * (s - (1 - (starRingEnd ℂ) s)) ^ (n - i) * (n.choose i : ℂ))
      = (n.choose i : ℂ) * (s - (1 - (starRingEnd ℂ) s)) ^ (n - i) * (-1) ^ i
          * (s - ρ)⁻¹ ^ (n + 2 - i) * ((s - ρ)⁻¹ ^ i * (s - ρ) ^ i) := by ring
    _ = _ := by rw [hcancel, mul_one]

/-- The Fourier coefficients of the transported measure from a jet sequence `S`
(`S m = Σ_ρ (s−ρ)^{−m}`): `μ̂_0 = 2 Re S_1/d`, `μ̂_{n+1} = Σ_{i≤n} C(n,i) d^{n−i} (−1)^i S_{n+2−i}`. -/
noncomputable def toeplitzCoeff (d : ℂ) (S : ℕ → ℂ) : ℕ → ℂ
  | 0 => (2 * ((S 1).re : ℂ)) / d
  | n + 1 => ∑ i ∈ range (n + 1), (n.choose i : ℂ) * d ^ (n - i) * (-1) ^ i * S (n + 2 - i)

/-- **The functional is linear in the jets**: the face marriage splits the Toeplitz form. -/
theorem toeplitzCoeff_add (d : ℂ) (S S' : ℕ → ℂ) (n : ℕ) :
    toeplitzCoeff d (S + S') n = toeplitzCoeff d S n + toeplitzCoeff d S' n := by
  cases n with
  | zero =>
    simp only [toeplitzCoeff, Pi.add_apply, Complex.add_re]
    push_cast
    ring
  | succ n =>
    simp only [toeplitzCoeff, Pi.add_apply, mul_add, Finset.sum_add_distrib]

/-- **The zeroth coefficient is the seat mass.** -/
theorem toeplitzCoeff_zero_eq_seatMass {s : ℂ} (hs : s.re ≠ 1 / 2) (S : ℕ → ℂ)
    (hS : S 1 = logDeriv ZD.riemannXi s) :
    toeplitzCoeff ((2 * s.re - 1 : ℝ) : ℂ) S 0 = ((seatMass s : ℝ) : ℂ) := by
  simp only [toeplitzCoeff, hS, seatMass]
  have hd : (2 * s.re - 1 : ℝ) ≠ 0 := by
    intro h0; apply hs; linarith
  have hd' : (s.re - 1 / 2 : ℝ) ≠ 0 := by
    intro h0; apply hs; linarith
  rw [← Complex.ofReal_ofNat, ← Complex.ofReal_mul, ← Complex.ofReal_div, Complex.ofReal_inj]
  field_simp

end CriticalLinePhasor.SeatingLedger

#print axioms CriticalLinePhasor.SeatingLedger.transport_norm_eq_one_iff
#print axioms CriticalLinePhasor.SeatingLedger.transport_pow_identity
#print axioms CriticalLinePhasor.SeatingLedger.toeplitzCoeff_add
#print axioms CriticalLinePhasor.SeatingLedger.toeplitzCoeff_zero_eq_seatMass
