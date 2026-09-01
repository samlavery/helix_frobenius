import RequestProject.ChiralityHB
import RequestProject.HilbertPolyaResolventTrace

/-!
# Finite-bank mass positivity: arrow 1 of the kill tree, unconditional

The gauge audit closed symbolically: `symClock α ℓ = 2i·e^{iθ/2}·sin((zℓ−θ)/2)`
is a CONSTANT times a sine, so its log-derivative carries no entire background
at all — the registration gauge `g′` is identically zero per factor, and any
self-duality-preserving registration keeps it zero (an even order-1 function
has odd log-derivative; an odd linear term vanishes — the same mechanism as
the compiled `xiLogDeriv_odd` killing Ξ's Hadamard constant).  What survives
is the exact per-factor identity: with `‖A‖² = e^{−yℓ}`, `‖G‖² = e^{yℓ}`,

  `Im[logDeriv(symClock α ℓ) z] = (ℓ/2)·(‖A‖² − ‖G‖²)/‖A−G‖² ≤ 0`  on `y > 0`.

Compiled here:
* `symClock_logDeriv_im_nonpos` — the per-clock mass sign, exact;
* `finiteBank_logDeriv_im_nonpos` — every finite unitary clock bank is
  anti-Herglotz on the upper half-plane (sum of the factors, `logDeriv_prod`);
* `finiteBank_seatMass_nonneg` — **the finite-bank seat mass is nonnegative
  on the whole half-plane `σ < ½`, unconditionally**: in the seat chart
  `s = ½ + i·z` (the compiled `spectralCoord` rotation), the bank's
  `Re[logDeriv]/(σ−½)` has the seatMass sign for every finite bank of
  unitary clocks.  Even multiplicities never appear — the mass register is
  parity-blind at finite rank exactly as at the limit
  (`seatMass_nonneg_of_online`).

The kill tree's remaining content is the middle arrow alone: a registered
self-dual family with line-supported zero measure and locally-uniform
log-derivative convergence to `Ξ′/Ξ` on channel compacts.

No `sorry`, no `axiom`.
-/

open Complex Filter Topology

noncomputable section

namespace CriticalLinePhasor.ChiralityHB

/-- The exponent's real part: the clock's radial rate. -/
theorem clock_exponent_re (z : ℂ) (ℓ : ℝ) :
    (Complex.I * z * (ℓ:ℂ) / 2).re = -(z.im * ℓ) / 2 := by
  have h2 : Complex.I * z * (ℓ:ℂ) / 2 = ((ℓ/2 : ℝ) : ℂ) * (Complex.I * z) := by
    push_cast
    ring
  rw [h2, Complex.re_ofReal_mul,
    show (Complex.I * z).re = -z.im by simp [Complex.mul_re]]
  ring

/-- The symmetrized clock's derivative: `(iℓ/2)·(A + G)` — the mirror SUM of
the two strands. -/
theorem symClock_hasDerivAt (α : ℂ) (ℓ : ℝ) (z : ℂ) :
    HasDerivAt (symClock α ℓ)
      (Complex.I * ℓ / 2 * (Complex.exp (Complex.I * z * ℓ / 2)
        + α * Complex.exp (-(Complex.I * z * ℓ / 2)))) z := by
  have hin : HasDerivAt (fun w : ℂ => Complex.I * w * ℓ / 2)
      (Complex.I * ℓ / 2) z := by
    have h := (((hasDerivAt_id z).const_mul Complex.I).mul_const
      ((ℓ:ℝ) : ℂ)).div_const 2
    simpa using h
  have h1 := hin.cexp
  have h2 := (hin.neg.cexp).const_mul α
  have hD : HasDerivAt (symClock α ℓ)
      (Complex.exp (Complex.I * z * ℓ / 2) * (Complex.I * ℓ / 2)
        - α * (Complex.exp (-(Complex.I * z * ℓ / 2)) * -(Complex.I * ℓ / 2))) z := by
    unfold symClock
    exact h1.sub h2
  have hval : Complex.exp (Complex.I * z * ℓ / 2) * (Complex.I * ℓ / 2)
      - α * (Complex.exp (-(Complex.I * z * ℓ / 2)) * -(Complex.I * ℓ / 2))
      = Complex.I * ℓ / 2 * (Complex.exp (Complex.I * z * ℓ / 2)
        + α * Complex.exp (-(Complex.I * z * ℓ / 2))) := by
    ring
  rw [hval] at hD
  exact hD

theorem symClock_differentiableAt (α : ℂ) (ℓ : ℝ) (z : ℂ) :
    DifferentiableAt ℂ (symClock α ℓ) z :=
  (symClock_hasDerivAt α ℓ z).differentiableAt

/-- Off the conjugation axis a unitary clock never vanishes — the
contrapositive of `clock_zeros_real`. -/
theorem symClock_ne_zero_off_axis {α : ℂ} (hα : ‖α‖ = 1) {ℓ : ℝ}
    (hℓ : 0 < ℓ) {z : ℂ} (hz : z.im ≠ 0) : symClock α ℓ z ≠ 0 :=
  fun h0 => hz (clock_zeros_real hα hℓ h0)

/-- **The per-clock mass sign, exact**: on the upper half-plane the
symmetrized unitary clock's log-derivative has nonpositive imaginary part —
the anti-Herglotz property carried by the strand imbalance
`e^{−yℓ} − e^{yℓ}` alone.  Gauge-free: no background term exists. -/
theorem symClock_logDeriv_im_nonpos {α : ℂ} (hα : ‖α‖ = 1) {ℓ : ℝ}
    (hℓ : 0 < ℓ) {z : ℂ} (hy : 0 < z.im) :
    (logDeriv (symClock α ℓ) z).im ≤ 0 := by
  set A := Complex.exp (Complex.I * z * ℓ / 2) with hA
  set G := α * Complex.exp (-(Complex.I * z * ℓ / 2)) with hG
  have hAn : ‖A‖ = Real.exp (-(z.im * ℓ) / 2) := by
    rw [hA, Complex.norm_exp, clock_exponent_re]
  have hGn : ‖G‖ = Real.exp (z.im * ℓ / 2) := by
    rw [hG, norm_mul, hα, one_mul, Complex.norm_exp]
    congr 1
    rw [Complex.neg_re, clock_exponent_re]
    ring
  have hQeq : symClock α ℓ z = A - G := rfl
  have hAGne : A - G ≠ 0 := by
    rw [← hQeq]
    exact symClock_ne_zero_off_axis hα hℓ (ne_of_gt hy)
  have hD := symClock_hasDerivAt α ℓ z
  have hlog : logDeriv (symClock α ℓ) z
      = ((ℓ/2 : ℝ) : ℂ) * (Complex.I * ((A + G) / (A - G))) := by
    rw [logDeriv_apply, hD.deriv, hQeq, ← hA, ← hG]
    push_cast
    ring
  clear_value A G
  rw [hlog, Complex.im_ofReal_mul, Complex.I_mul_im]
  have hre_nonpos : ((A + G) / (A - G)).re ≤ 0 := by
    have hq : (A + G) / (A - G)
        = (((Complex.normSq (A - G))⁻¹ : ℝ) : ℂ)
            * ((A + G) * (starRingEnd ℂ) (A - G)) := by
      rw [div_eq_mul_inv, Complex.inv_def]
      push_cast
      ring
    have hcross : ((A + G) * (starRingEnd ℂ) (A - G)).re
        = Complex.normSq A - Complex.normSq G := by
      have hexp : (A + G) * (starRingEnd ℂ) (A - G)
          = A * (starRingEnd ℂ) A - G * (starRingEnd ℂ) G
            + (G * (starRingEnd ℂ) A - (starRingEnd ℂ) (G * (starRingEnd ℂ) A)) := by
        rw [map_sub, map_mul, Complex.conj_conj]
        ring
      rw [hexp, Complex.mul_conj, Complex.mul_conj]
      simp [Complex.add_re, Complex.sub_re, Complex.conj_re]
    have hAG : Complex.normSq A - Complex.normSq G < 0 := by
      rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq, hAn, hGn]
      have h1 : (0:ℝ) < z.im * ℓ := mul_pos hy hℓ
      have h2 : Real.exp (-(z.im * ℓ) / 2) < Real.exp (z.im * ℓ / 2) :=
        Real.exp_lt_exp.mpr (by linarith)
      have h3 : (0:ℝ) < Real.exp (-(z.im * ℓ) / 2) := Real.exp_pos _
      nlinarith [h2, h3, Real.exp_pos (z.im * ℓ / 2)]
    rw [hq, Complex.re_ofReal_mul, hcross]
    exact mul_nonpos_iff.mpr
      (Or.inl ⟨inv_nonneg.mpr (Complex.normSq_nonneg _), hAG.le⟩)
  exact mul_nonpos_iff.mpr (Or.inl ⟨by linarith, hre_nonpos⟩)

/-- **The finite bank is anti-Herglotz on the upper half-plane**: the carrier
product's log-derivative is the sum of its clocks' (`logDeriv_prod`), each
nonpositive.  Unconditional, every finite rank, any multiplicity pattern. -/
theorem finiteBank_logDeriv_im_nonpos {ι : Type*} (t : Finset ι)
    (α : ι → ℂ) (ℓ : ι → ℝ)
    (hα : ∀ i ∈ t, ‖α i‖ = 1) (hℓ : ∀ i ∈ t, 0 < ℓ i)
    {z : ℂ} (hy : 0 < z.im) :
    (logDeriv (fun w => ∏ i ∈ t, symClock (α i) (ℓ i) w) z).im ≤ 0 := by
  rw [logDeriv_prod
    (fun i hi => symClock_ne_zero_off_axis (hα i hi) (hℓ i hi) (ne_of_gt hy))
    (fun i hi => symClock_differentiableAt (α i) (ℓ i) z)]
  rw [Complex.im_sum]
  apply Finset.sum_nonpos
  intro i hi
  exact symClock_logDeriv_im_nonpos (hα i hi) (hℓ i hi) hy

/-- The seat chart puts the left channel on the upper half-plane. -/
theorem spectralCoord_im (s : ℂ) :
    (HilbertPolya.spectralCoord s).im = 1/2 - s.re := by
  unfold HilbertPolya.spectralCoord
  have h12 : ((1:ℂ) / 2).re = 1/2 := by
    norm_num [Complex.div_re, Complex.normSq_apply]
  simp [Complex.mul_im, Complex.sub_re, Complex.sub_im, h12]

theorem spectralCoord_hasDerivAt (s : ℂ) :
    HasDerivAt HilbertPolya.spectralCoord (-Complex.I) s := by
  unfold HilbertPolya.spectralCoord
  have h := ((hasDerivAt_id s).sub_const ((1:ℂ)/2)).const_mul (-Complex.I)
  simpa using h

/-- **Finite-bank seat mass is nonnegative on the whole half-plane `σ < ½`,
unconditionally** — arrow 1 of the kill tree.  In the seat chart the finite
unitary bank's `Re[logDeriv]/(σ−½)` has the seatMass sign everywhere left of
the line: finite helix positivity, from `carrier_zeros_real`'s geometry and
nothing else.  Even multiplicities are invisible, exactly as at the limit. -/
theorem finiteBank_seatMass_nonneg {ι : Type*} (t : Finset ι)
    (α : ι → ℂ) (ℓ : ι → ℝ)
    (hα : ∀ i ∈ t, ‖α i‖ = 1) (hℓ : ∀ i ∈ t, 0 < ℓ i)
    {s : ℂ} (hσ : s.re < 1/2) :
    0 ≤ (logDeriv (fun w => ∏ i ∈ t,
          symClock (α i) (ℓ i) (HilbertPolya.spectralCoord w)) s).re
        / (s.re - 1/2) := by
  have hzim : 0 < (HilbertPolya.spectralCoord s).im := by
    rw [spectralCoord_im]
    linarith
  have hcomp : logDeriv (fun w => ∏ i ∈ t,
        symClock (α i) (ℓ i) (HilbertPolya.spectralCoord w)) s
      = logDeriv (fun z => ∏ i ∈ t, symClock (α i) (ℓ i) z)
          (HilbertPolya.spectralCoord s) * deriv HilbertPolya.spectralCoord s := by
    exact logDeriv_comp
      (DifferentiableAt.fun_finset_prod
        (fun i _ => symClock_differentiableAt (α i) (ℓ i) _))
      (spectralCoord_hasDerivAt s).differentiableAt
  rw [hcomp, (spectralCoord_hasDerivAt s).deriv]
  have hre : (logDeriv (fun z => ∏ i ∈ t, symClock (α i) (ℓ i) z)
        (HilbertPolya.spectralCoord s) * -Complex.I).re
      = (logDeriv (fun z => ∏ i ∈ t, symClock (α i) (ℓ i) z)
          (HilbertPolya.spectralCoord s)).im := by
    simp [Complex.mul_re]
  rw [hre]
  have hnp := finiteBank_logDeriv_im_nonpos t α ℓ hα hℓ hzim
  exact div_nonneg_iff.mpr (Or.inr ⟨hnp, by linarith⟩)

/-- The clock's log-derivative in strand-quotient form. -/
theorem symClock_logDeriv_eq (α : ℂ) (ℓ : ℝ) (z : ℂ) :
    logDeriv (symClock α ℓ) z
      = (Complex.I * ℓ / 2) *
          ((Complex.exp (Complex.I * z * ℓ / 2)
              + α * Complex.exp (-(Complex.I * z * ℓ / 2)))
            / (Complex.exp (Complex.I * z * ℓ / 2)
              - α * Complex.exp (-(Complex.I * z * ℓ / 2)))) := by
  rw [logDeriv_apply, (symClock_hasDerivAt α ℓ z).deriv,
    show symClock α ℓ z = Complex.exp (Complex.I * z * ℓ / 2)
      - α * Complex.exp (-(Complex.I * z * ℓ / 2)) from rfl]
  ring

/-- **The carrier has the Euler product — at readout level, in the
channel's own chart**: on the upper half-plane each unitary clock's
log-derivative is an absolutely convergent lattice readout with unimodular
teeth,
`logDeriv(symClock α ℓ) z = −iℓ/2 − iℓ·Σ_{k≥1} ᾱᵏ e^{ikℓz}` —
the local Euler factor's Dirichlet expansion, valid exactly where the
channel lives.  The multiplicative endpoint of the Phase-B transport in
the same register as the σ>1 rigidity class. -/
theorem symClock_logDeriv_expansion {α : ℂ} (hα : ‖α‖ = 1) {ℓ : ℝ}
    (hℓ : 0 < ℓ) {z : ℂ} (hy : 0 < z.im) :
    logDeriv (symClock α ℓ) z
      = -(Complex.I * ℓ / 2)
        - Complex.I * ℓ *
          ∑' k : ℕ,
            ((starRingEnd ℂ) α * Complex.exp (Complex.I * ℓ * z))^(k+1) := by
  set A : ℂ := Complex.exp (Complex.I * z * ℓ / 2) with hA
  set G : ℂ := α * Complex.exp (-(Complex.I * z * ℓ / 2)) with hG
  set w : ℂ := (starRingEnd ℂ) α * Complex.exp (Complex.I * ℓ * z) with hw
  have hα0 : α ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hα
    norm_num at hα
  have hinv : (starRingEnd ℂ) α * α = 1 := by
    rw [← Complex.inv_eq_conj hα, inv_mul_cancel₀ hα0]
  have hGne : G ≠ 0 := by
    rw [hG]
    exact mul_ne_zero hα0 (Complex.exp_ne_zero _)
  have hAwG : A = w * G := by
    rw [hA, hw, hG]
    rw [show (starRingEnd ℂ) α * Complex.exp (Complex.I * ℓ * z)
        * (α * Complex.exp (-(Complex.I * z * ℓ / 2)))
      = ((starRingEnd ℂ) α * α)
        * (Complex.exp (Complex.I * ℓ * z)
            * Complex.exp (-(Complex.I * z * ℓ / 2))) by ring,
      hinv, one_mul, ← Complex.exp_add]
    congr 1
    ring
  have hwnorm : ‖w‖ < 1 := by
    rw [hw, norm_mul, RCLike.norm_conj, hα, one_mul, Complex.norm_exp]
    have hre : (Complex.I * (ℓ:ℂ) * z).re = -(ℓ * z.im) := by
      simp [Complex.mul_re, Complex.mul_im]
    rw [hre, show (1:ℝ) = Real.exp 0 from Real.exp_zero.symm]
    apply Real.exp_lt_exp.mpr
    nlinarith
  have h1w : (1:ℂ) - w ≠ 0 := by
    intro h
    have hweq : w = 1 := by linear_combination -h
    rw [hweq] at hwnorm
    simp at hwnorm
  have hw1 : w - 1 ≠ 0 := by
    intro h
    have hweq : w = 1 := by linear_combination h
    rw [hweq] at hwnorm
    simp at hwnorm
  have hquot : (A + G)/(A - G) = (w + 1)/(w - 1) := by
    rw [hAwG, show w*G + G = G*(w+1) by ring, show w*G - G = G*(w-1) by ring,
      mul_div_mul_left _ _ hGne]
  have hgeo : ∑' k : ℕ, w^(k+1) = w * (1-w)⁻¹ := by
    have h := tsum_geometric_of_norm_lt_one hwnorm
    calc ∑' k : ℕ, w^(k+1) = ∑' k : ℕ, w * w^k := by
          apply tsum_congr
          intro k
          rw [pow_succ]
          ring
      _ = w * ∑' k : ℕ, w^k := tsum_mul_left
      _ = w * (1-w)⁻¹ := by rw [h]
  rw [symClock_logDeriv_eq α ℓ z, ← hA, ← hG, hquot, hgeo]
  field_simp
  ring

/-- **The whole bank in the rigidity register**: on the upper half-plane a
finite unitary bank's log-derivative is the finite sum of its clocks'
Euler expansions — an absolutely convergent lattice readout with
unimodular teeth `ℓᵢ·ᾱᵢᵏ` at frequencies `kℓᵢ`.  With
`finiteBank_logDeriv_im_nonpos`, the compiled loop closes at finite rank:
clock-product structure ⟹ lattice readout with unimodular teeth ⟹
anti-Herglotz ⟹ seat mass ≥ 0. -/
theorem finiteBank_logDeriv_expansion {ι : Type*} (t : Finset ι)
    (α : ι → ℂ) (ℓ : ι → ℝ)
    (hα : ∀ i ∈ t, ‖α i‖ = 1) (hℓ : ∀ i ∈ t, 0 < ℓ i)
    {z : ℂ} (hy : 0 < z.im) :
    logDeriv (fun w => ∏ i ∈ t, symClock (α i) (ℓ i) w) z
      = ∑ i ∈ t, (-(Complex.I * ℓ i / 2)
          - Complex.I * ℓ i *
            ∑' k : ℕ,
              ((starRingEnd ℂ) (α i)
                * Complex.exp (Complex.I * ℓ i * z))^(k+1)) := by
  rw [logDeriv_prod
    (fun i hi => symClock_ne_zero_off_axis (hα i hi) (hℓ i hi) (ne_of_gt hy))
    (fun i hi => symClock_differentiableAt (α i) (ℓ i) z)]
  apply Finset.sum_congr rfl
  intro i hi
  exact symClock_logDeriv_expansion (hα i hi) (hℓ i hi) hy

end CriticalLinePhasor.ChiralityHB

#print axioms CriticalLinePhasor.ChiralityHB.finiteBank_logDeriv_expansion
#print axioms CriticalLinePhasor.ChiralityHB.symClock_logDeriv_expansion
#print axioms CriticalLinePhasor.ChiralityHB.symClock_hasDerivAt
#print axioms CriticalLinePhasor.ChiralityHB.symClock_logDeriv_im_nonpos
#print axioms CriticalLinePhasor.ChiralityHB.finiteBank_logDeriv_im_nonpos
#print axioms CriticalLinePhasor.ChiralityHB.finiteBank_seatMass_nonneg
