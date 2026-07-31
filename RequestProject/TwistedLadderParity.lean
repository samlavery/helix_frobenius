import RequestProject.RankLadderParity

/-!
# The twisted rank-ladder parity closure: two clocks, one channel law

The λ_τ-weighted extension of `RankLadderParity`.  Twisting the rank-`r` elliptic dual
term by a rank-`m` twist clock multiplies the kernel by the second Chebyshev character
(the two-clock weight law) and re-weights the crossing lattice by the twist's
coefficients `v = λ_τ`-data, which carry a reflection sign `σ` (`v(-ξ) = σ·v(ξ)`):

  `dual_ξ = v(ξ) · ∫_{-1}^{1} Φ(x) · U_r(x)·U_m(x) · e^{-2πi x ξ c} dx`.

This file proves, uniformly in both ranks and in the twist sign:

* `chebU_mul_neg`, `twistedIntegral_neg` — the **two-clock μ₂ parity**:
  `I_{r,m}(-ξ) = (-1)^{r+m} I_{r,m}(ξ)` — the twist composes clocks, parities multiply.
* `twistedIntegral_zero_odd` — the DC term vanishes at odd *total* clock `r + m`.
* `twistedSymmWindowSum_eq_zero` — **the master channel law**: over any symmetric
  window of the crossing lattice, the λ_τ-weighted dual sum is a fixed point of the
  combined parity involution, hence vanishes EXACTLY whenever
  `σ · (-1)^{r+m} ≠ 1`.  This is the parity shadow of the measured
  channel-multiplicative root-number ladder: the extinction channel of the twisted rung
  is the *product* of the seed clock parity, the twist clock parity, and the lattice
  sign — nothing else.
* `twistedLatticeSum_eq_zero`, `twistedTsum_eq_zero` — window and full-lattice versions
  (the full versions include the DC term: when the total clock is even but `σ ≠ 1`, the
  sign law itself forces `v(0) = 0`, so the flip argument covers the whole lattice).
* `twistedLatticeSum_eq_zero_odd_total` / `..._even_total` — the two sign
  specializations: even lattice weights extinguish the odd total channel (the untwisted
  law at `m = 0`), odd lattice weights FLIP the channel — even total clocks extinguish.
* `twistedIntegral_eq_dualIntegral` — the tower compatibility: the twisted kernel *is*
  the untwisted kernel of the clock-deformed profile `Φ·U_m`; for even `m` the twist is
  a profile deformation (channel unchanged), for odd `m` the deformed profile is odd and
  the channel flips — handled natively here.

All identities are unconditional: the substitution `x ↦ -x` is an identity of interval
integrals and the lattice flip is a reindexing; no integrability or summability is
consumed anywhere (the `tsum` version needs none — scalar factors pass through `tsum`
unconditionally).
-/

open Complex intervalIntegral

namespace CriticalLinePhasor.TwistedLadderParity

open CriticalLinePhasor.RankLadderParity

/-- `a = c·a` with `c ≠ 1` forces `a = 0` in `ℂ` — the fixed-point extinction step. -/
private theorem eq_zero_of_self_eq_mul {a c : ℂ} (h : a = c * a) (hc : c ≠ 1) : a = 0 := by
  have h2 : (c - 1) * a = 0 := by linear_combination -h
  rcases mul_eq_zero.mp h2 with h' | h'
  · exact absurd (by linear_combination h' : c = 1) hc
  · exact h'

/-- The two clocks compose: `(U_r·U_m)(-x) = (-1)^{r+m} (U_r·U_m)(x)` — parities
multiply across the twist. -/
theorem chebU_mul_neg (r m : ℕ) (x : ℝ) :
    chebU r (-x) * chebU m (-x) = (-1) ^ (r + m) * (chebU r x * chebU m x) := by
  rw [chebU_neg, chebU_neg, pow_add]
  ring

/-- The twisted dual integrand: seed clock `U_r` times twist clock `U_m` on the same
elliptic band, at frequency `ξ` and scale `c`. -/
noncomputable def twistedKernel (Φ : ℝ → ℝ) (r m : ℕ) (c ξ : ℝ) (x : ℝ) : ℂ :=
  ((Φ x * (chebU r x * chebU m x) : ℝ) : ℂ) * Complex.exp (-2 * Real.pi * I * x * ξ * c)

/-- The twisted dual integral `I_{r,m}(ξ)`. -/
noncomputable def twistedIntegral (Φ : ℝ → ℝ) (r m : ℕ) (c ξ : ℝ) : ℂ :=
  ∫ x in (-1 : ℝ)..1, twistedKernel Φ r m c ξ x

/-- **Tower compatibility**: the twisted kernel is the untwisted kernel of the
clock-deformed profile `Φ·U_m`.  Even twists are profile deformations; odd twists make
the deformed profile odd — the channel flip, handled natively below. -/
theorem twistedIntegral_eq_dualIntegral (Φ : ℝ → ℝ) (r m : ℕ) (c ξ : ℝ) :
    twistedIntegral Φ r m c ξ =
      dualIntegral (fun x => Φ x * chebU m x) r c ξ := by
  unfold twistedIntegral dualIntegral twistedKernel dualKernel
  apply intervalIntegral.integral_congr
  intro x _
  simp only [Complex.ofReal_mul]
  ring

/-- The `-ξ` twisted kernel at `x` is `(-1)^{r+m}` times the `ξ` kernel at `-x`. -/
theorem twistedKernel_neg_eq (Φ : ℝ → ℝ) (hΦ : ∀ x, Φ (-x) = Φ x)
    (r m : ℕ) (c ξ x : ℝ) :
    twistedKernel Φ r m c (-ξ) x =
      ((-1 : ℂ) ^ (r + m)) * twistedKernel Φ r m c ξ (-x) := by
  unfold twistedKernel
  rw [hΦ, chebU_mul_neg]
  have h2 : ((-1 : ℂ)) ^ (r + m) * ((-1 : ℂ)) ^ (r + m) = 1 := by
    rw [← mul_pow]
    norm_num
  have hexp : Complex.exp (-2 * (Real.pi : ℂ) * I * (x : ℝ) * ((-ξ : ℝ) : ℂ) * (c : ℝ)) =
      Complex.exp (-2 * (Real.pi : ℂ) * I * ((-x : ℝ) : ℂ) * (ξ : ℝ) * (c : ℝ)) := by
    push_cast
    ring_nf
  rw [hexp]
  push_cast
  linear_combination (-((Φ x : ℂ) * (((chebU r x : ℝ) : ℂ) * ((chebU m x : ℝ) : ℂ))) *
    Complex.exp (-2 * (Real.pi : ℂ) * I * (-(x : ℂ)) * (ξ : ℂ) * (c : ℂ))) * h2

/-- **The two-clock μ₂ parity on the dual variable**:
`I_{r,m}(-ξ) = (-1)^{r+m} I_{r,m}(ξ)`.  Unconditional — the substitution `x ↦ -x` is an
identity of interval integrals, no integrability consumed. -/
theorem twistedIntegral_neg (Φ : ℝ → ℝ) (hΦ : ∀ x, Φ (-x) = Φ x)
    (r m : ℕ) (c ξ : ℝ) :
    twistedIntegral Φ r m c (-ξ) = ((-1 : ℂ) ^ (r + m)) * twistedIntegral Φ r m c ξ := by
  unfold twistedIntegral
  calc
    (∫ x in (-1 : ℝ)..1, twistedKernel Φ r m c (-ξ) x)
        = ∫ x in (-1 : ℝ)..1, ((-1 : ℂ) ^ (r + m)) * twistedKernel Φ r m c ξ (-x) := by
          apply intervalIntegral.integral_congr
          intro x _
          exact twistedKernel_neg_eq Φ hΦ r m c ξ x
    _ = ((-1 : ℂ) ^ (r + m)) * ∫ x in (-1 : ℝ)..1, twistedKernel Φ r m c ξ (-x) :=
          intervalIntegral.integral_const_mul _ _
    _ = ((-1 : ℂ) ^ (r + m)) * ∫ x in (-1 : ℝ)..1, twistedKernel Φ r m c ξ x := by
          congr 1
          set_option linter.unnecessarySimpa false in
          simpa using intervalIntegral.integral_comp_neg
            (a := (-1 : ℝ)) (b := 1) (fun x => twistedKernel Φ r m c ξ x)

/-- **The DC term vanishes at every odd total clock** — the composed character
`U_r·U_m` is odd, killing the zero-frequency channel. -/
theorem twistedIntegral_zero_odd (Φ : ℝ → ℝ) (hΦ : ∀ x, Φ (-x) = Φ x)
    {r m : ℕ} (hrm : Odd (r + m)) (c : ℝ) :
    twistedIntegral Φ r m c 0 = 0 := by
  have h := twistedIntegral_neg Φ hΦ r m c 0
  rw [neg_zero, hrm.neg_one_pow] at h
  have h2 : (2 : ℂ) * twistedIntegral Φ r m c 0 = 0 := by linear_combination h
  rcases mul_eq_zero.mp h2 with h' | h'
  · norm_num at h'
  · exact h'

/-- **The master channel law of the twisted ladder.**  Over any symmetric window of the
crossing lattice, the λ_τ-weighted dual sum is a fixed point of the combined parity
involution `ξ ↦ -ξ`; it therefore vanishes EXACTLY whenever the total channel factor
`σ·(-1)^{r+m}` differs from `1`.  The extinction channel of the twisted rung is the
product of the seed clock parity, the twist clock parity, and the lattice sign — the
parity shadow of the channel-multiplicative root-number ladder. -/
theorem twistedSymmWindowSum_eq_zero (Φ : ℝ → ℝ) (hΦ : ∀ x, Φ (-x) = Φ x)
    (r m : ℕ) (c : ℝ) (v : ℤ → ℂ) (σ : ℂ) (hv : ∀ ξ : ℤ, v (-ξ) = σ * v ξ)
    (hchan : σ * (-1 : ℂ) ^ (r + m) ≠ 1)
    (S : Finset ℤ) (hsym : ∀ ξ : ℤ, ξ ∈ S ↔ -ξ ∈ S) :
    (∑ ξ ∈ S, v ξ * twistedIntegral Φ r m c (ξ : ℝ)) = 0 := by
  have hflip : (∑ ξ ∈ S, v ξ * twistedIntegral Φ r m c (ξ : ℝ)) =
      ∑ ξ ∈ S, v (-ξ) * twistedIntegral Φ r m c ((-ξ : ℤ) : ℝ) := by
    apply Finset.sum_nbij' (fun ξ => -ξ) (fun ξ => -ξ)
    · intro ξ hξ
      exact (hsym ξ).mp hξ
    · intro ξ hξ
      simpa using (hsym (-ξ)).mpr (by simpa using hξ)
    · intro ξ _
      simp
    · intro ξ _
      simp
    · intro ξ _
      simp
  have hterm : ∀ ξ : ℤ, v (-ξ) * twistedIntegral Φ r m c ((-ξ : ℤ) : ℝ) =
      (σ * (-1 : ℂ) ^ (r + m)) * (v ξ * twistedIntegral Φ r m c (ξ : ℝ)) := by
    intro ξ
    rw [hv ξ]
    push_cast
    rw [twistedIntegral_neg Φ hΦ r m c (ξ : ℝ)]
    ring
  have h : (∑ ξ ∈ S, v ξ * twistedIntegral Φ r m c (ξ : ℝ)) =
      (σ * (-1 : ℂ) ^ (r + m)) * ∑ ξ ∈ S, v ξ * twistedIntegral Φ r m c (ξ : ℝ) := by
    calc
      (∑ ξ ∈ S, v ξ * twistedIntegral Φ r m c (ξ : ℝ))
          = ∑ ξ ∈ S, v (-ξ) * twistedIntegral Φ r m c ((-ξ : ℤ) : ℝ) := hflip
      _ = ∑ ξ ∈ S, (σ * (-1 : ℂ) ^ (r + m)) *
            (v ξ * twistedIntegral Φ r m c (ξ : ℝ)) :=
            Finset.sum_congr rfl fun ξ _ => hterm ξ
      _ = (σ * (-1 : ℂ) ^ (r + m)) *
            ∑ ξ ∈ S, v ξ * twistedIntegral Φ r m c (ξ : ℝ) :=
            (Finset.mul_sum _ _ _).symm
  exact eq_zero_of_self_eq_mul h hchan

/-- The full symmetric window (DC included): the λ_τ-weighted twisted lattice sum over
`[-N, N]` vanishes whenever the channel factor differs from `1`. -/
theorem twistedLatticeSum_eq_zero (Φ : ℝ → ℝ) (hΦ : ∀ x, Φ (-x) = Φ x)
    (r m : ℕ) (c : ℝ) (v : ℤ → ℂ) (σ : ℂ) (hv : ∀ ξ : ℤ, v (-ξ) = σ * v ξ)
    (hchan : σ * (-1 : ℂ) ^ (r + m) ≠ 1) (N : ℕ) :
    (∑ ξ ∈ Finset.Icc (-(N : ℤ)) N, v ξ * twistedIntegral Φ r m c (ξ : ℝ)) = 0 := by
  refine twistedSymmWindowSum_eq_zero Φ hΦ r m c v σ hv hchan _ fun ξ => ?_
  simp only [Finset.mem_Icc]
  omega

/-- The punctured symmetric window (`0` removed) — the ξ≠0 channel form matching the
untwisted interface. -/
theorem twistedLatticeSum_erase_eq_zero (Φ : ℝ → ℝ) (hΦ : ∀ x, Φ (-x) = Φ x)
    (r m : ℕ) (c : ℝ) (v : ℤ → ℂ) (σ : ℂ) (hv : ∀ ξ : ℤ, v (-ξ) = σ * v ξ)
    (hchan : σ * (-1 : ℂ) ^ (r + m) ≠ 1) (N : ℕ) :
    (∑ ξ ∈ (Finset.Icc (-(N : ℤ)) N).erase 0,
      v ξ * twistedIntegral Φ r m c (ξ : ℝ)) = 0 := by
  refine twistedSymmWindowSum_eq_zero Φ hΦ r m c v σ hv hchan _ fun ξ => ?_
  simp only [Finset.mem_erase, Finset.mem_Icc, neg_ne_zero]
  omega

/-- **The full-lattice closure**: the complete λ_τ-weighted twisted dual sum over `ℤ`
vanishes whenever the channel factor differs from `1`.  No summability is consumed:
the lattice flip is a reindexing and scalars pass through `tsum` unconditionally. -/
theorem twistedTsum_eq_zero (Φ : ℝ → ℝ) (hΦ : ∀ x, Φ (-x) = Φ x)
    (r m : ℕ) (c : ℝ) (v : ℤ → ℂ) (σ : ℂ) (hv : ∀ ξ : ℤ, v (-ξ) = σ * v ξ)
    (hchan : σ * (-1 : ℂ) ^ (r + m) ≠ 1) :
    (∑' ξ : ℤ, v ξ * twistedIntegral Φ r m c (ξ : ℝ)) = 0 := by
  set g : ℤ → ℂ := fun ξ => v ξ * twistedIntegral Φ r m c (ξ : ℝ) with hg
  have hterm : ∀ ξ : ℤ, g (-ξ) = (σ * (-1 : ℂ) ^ (r + m)) * g ξ := by
    intro ξ
    simp only [hg]
    rw [hv ξ]
    push_cast
    rw [twistedIntegral_neg Φ hΦ r m c (ξ : ℝ)]
    ring
  have hflip : (∑' ξ : ℤ, g ξ) = ∑' ξ : ℤ, g (-ξ) :=
    ((Equiv.neg ℤ).tsum_eq g).symm
  have h : (∑' ξ : ℤ, g ξ) = (σ * (-1 : ℂ) ^ (r + m)) * ∑' ξ : ℤ, g ξ := by
    calc
      (∑' ξ : ℤ, g ξ) = ∑' ξ : ℤ, g (-ξ) := hflip
      _ = ∑' ξ : ℤ, (σ * (-1 : ℂ) ^ (r + m)) * g ξ := tsum_congr hterm
      _ = (σ * (-1 : ℂ) ^ (r + m)) * ∑' ξ : ℤ, g ξ := tsum_mul_left
  exact eq_zero_of_self_eq_mul h hchan

/-- **Even lattice weights, odd total clock**: the untwisted extinction law extended to
the twisted rung — the channel is `r + m`, not `r`.  At `m = 0` this is
`RankLadderParity.latticeSum_eq_zero_odd` on the full window. -/
theorem twistedLatticeSum_eq_zero_odd_total (Φ : ℝ → ℝ) (hΦ : ∀ x, Φ (-x) = Φ x)
    {r m : ℕ} (hrm : Odd (r + m)) (c : ℝ) (v : ℤ → ℂ)
    (hv : ∀ ξ : ℤ, v (-ξ) = v ξ) (N : ℕ) :
    (∑ ξ ∈ Finset.Icc (-(N : ℤ)) N, v ξ * twistedIntegral Φ r m c (ξ : ℝ)) = 0 := by
  refine twistedLatticeSum_eq_zero Φ hΦ r m c v 1 (fun ξ => by rw [one_mul, hv ξ]) ?_ N
  rw [one_mul, hrm.neg_one_pow]
  norm_num

/-- **Odd lattice weights, even total clock — the flipped channel**: a twist whose
lattice data carries the odd sign extinguishes the EVEN total clocks, where the
untwisted detecting channel lives.  The twist sign moves the extinction channel; it
never destroys it. -/
theorem twistedLatticeSum_eq_zero_even_total (Φ : ℝ → ℝ) (hΦ : ∀ x, Φ (-x) = Φ x)
    {r m : ℕ} (hrm : Even (r + m)) (c : ℝ) (v : ℤ → ℂ)
    (hv : ∀ ξ : ℤ, v (-ξ) = -v ξ) (N : ℕ) :
    (∑ ξ ∈ Finset.Icc (-(N : ℤ)) N, v ξ * twistedIntegral Φ r m c (ξ : ℝ)) = 0 := by
  refine twistedLatticeSum_eq_zero Φ hΦ r m c v (-1)
    (fun ξ => by rw [neg_one_mul, hv ξ]) ?_ N
  rw [hrm.neg_one_pow]
  norm_num

end CriticalLinePhasor.TwistedLadderParity

#print axioms CriticalLinePhasor.TwistedLadderParity.chebU_mul_neg
#print axioms CriticalLinePhasor.TwistedLadderParity.twistedIntegral_eq_dualIntegral
#print axioms CriticalLinePhasor.TwistedLadderParity.twistedIntegral_neg
#print axioms CriticalLinePhasor.TwistedLadderParity.twistedIntegral_zero_odd
#print axioms CriticalLinePhasor.TwistedLadderParity.twistedSymmWindowSum_eq_zero
#print axioms CriticalLinePhasor.TwistedLadderParity.twistedLatticeSum_eq_zero
#print axioms CriticalLinePhasor.TwistedLadderParity.twistedTsum_eq_zero
#print axioms CriticalLinePhasor.TwistedLadderParity.twistedLatticeSum_eq_zero_odd_total
#print axioms CriticalLinePhasor.TwistedLadderParity.twistedLatticeSum_eq_zero_even_total
