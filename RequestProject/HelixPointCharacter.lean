import RequestProject.HelixLogFreeFTA

/-!
# The helix point is a multiplicative character; the fiber's phasor is the site over its own area

RH_LEDGER 722m/722bd/722bk.  The carrier's site map `helixPt θ n = √n · wind θ n`
(`HelixLogFreeFTA.lean`) is itself a completely multiplicative character of `ℕ^×`, and at the frequency of an
on-line zero `ρ = ½ + iγ` it is `n ↦ n^{\bar ρ}`.  Dividing by the site's own area `‖radius‖² = n` gives the
fiber's phasor `n^{-ρ}` — no conjugate (722bk corrects an earlier prose slip) — and the scale balance
`‖phasor‖ · radius = 1` then holds EXACTLY at every site, not merely as the limit of `scaleBalanced_iff`.

* `helixPt_mul` — multiplicativity of the site map.
* `windAngle_prime_log` — with `θ p = c·log p` the winding angle is `c·log n` (FTA, no logarithm inside).
* `helixPt_eq_cpow` — at `c = -γ`, `helixPt θ n = n^{½-iγ} = n^{\bar ρ}`.
* `phasor`, `norm_phasor_mul_sqrt` — the phasor, and exact scale balance at every site.
* `phasor_eq_cpow_neg` — the phasor IS `n^{-ρ}`.
* `windAngle_const_pi`, `wind_const_pi_eq_liouville` — the Liouville grading of `LiouvilleChirality.lean` is the
  all-`π` point of the character torus.
-/

open Complex

namespace HelixLogFree

variable (θ : ℕ → ℝ)

/-- **The helix point is a multiplicative character.** -/
theorem helixPt_mul {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) :
    helixPt θ (m * n) = helixPt θ m * helixPt θ n := by
  unfold helixPt
  rw [wind_mul θ hm hn]
  push_cast
  rw [Real.sqrt_mul (Nat.cast_nonneg m)]
  push_cast
  ring

/-- With the prime angle `θ p = c · log p`, the log-free winding angle is `c · log n`. -/
theorem windAngle_prime_log (c : ℝ) {n : ℕ} (hn : n ≠ 0) :
    windAngle (fun p => c * Real.log p) n = c * Real.log n := by
  have hprod : n.factorization.prod (· ^ ·) = n := Nat.factorization_prod_pow_eq_self hn
  have : Real.log n = n.factorization.sum (fun p e => (e : ℝ) * Real.log p) := by
    conv_lhs => rw [← hprod]
    rw [Finsupp.prod, Nat.cast_prod, Real.log_prod]
    · refine Finset.sum_congr rfl (fun p hp => ?_)
      rw [Nat.cast_pow, Real.log_pow]
    · intro p hp
      have hp1 : 1 < p := (Nat.prime_of_mem_primeFactors
        (by simpa [Nat.support_factorization] using hp)).one_lt
      positivity
  rw [windAngle, this, Finsupp.mul_sum]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  ring

/-- **At a zero's frequency the helix point is `n ↦ n^{\bar ρ}`.** -/
theorem helixPt_eq_cpow (γ : ℝ) {n : ℕ} (hn : n ≠ 0) :
    helixPt (fun p => -γ * Real.log p) n = (n : ℂ) ^ ((1 : ℂ) / 2 - γ * Complex.I) := by
  have hposN : (0 : ℕ) < n := Nat.pos_of_ne_zero hn
  have hpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hposN
  have hne : ((n : ℂ)) ≠ 0 := by exact_mod_cast hposN.ne'
  have hlog : Complex.log (n : ℂ) = ((Real.log n : ℝ) : ℂ) := by
    rw [← Complex.ofReal_natCast, Complex.ofReal_log hpos.le]
  have hsqrt : Real.sqrt (n : ℝ) = Real.exp (Real.log n / 2) := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hpos]; ring_nf
  rw [helixPt, wind, windAngle_prime_log _ hn, Complex.cpow_def_of_ne_zero hne, hlog,
    Circle.coe_exp, hsqrt, Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- The fiber's phasor at a site: the carrier point divided by its own area `‖radius‖² = n`. -/
noncomputable def phasor (n : ℕ) : ℂ := helixPt θ n / (n : ℂ)

/-- **Scale balance is an IDENTITY, not a limit.**  `‖phasor n‖ · √n = 1` at every site. -/
theorem norm_phasor_mul_sqrt (n : ℕ) (hn : n ≠ 0) :
    ‖phasor θ n‖ * Real.sqrt n = 1 := by
  have hpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  rw [phasor, norm_div, norm_helixPt, Complex.norm_natCast]
  have h : Real.sqrt n * Real.sqrt n = (n : ℝ) := Real.mul_self_sqrt hpos.le
  field_simp
  linarith [h]

/-- **At a zero's frequency the phasor is `n^{-ρ}`** — the fiber's own term, produced by the carrier's site map
divided by its area.  No conjugate (722bk). -/
theorem phasor_eq_cpow_neg (γ : ℝ) {n : ℕ} (hn : n ≠ 0) :
    phasor (fun p => -γ * Real.log p) n = (n : ℂ) ^ (-((1 : ℂ) / 2 + γ * Complex.I)) := by
  have hne : ((n : ℂ)) ≠ 0 := by exact_mod_cast hn
  have key : ((n : ℂ)) ^ (-((1 : ℂ) / 2 + (γ : ℂ) * Complex.I)) * ((n : ℂ)) ^ (1 : ℂ)
      = ((n : ℂ)) ^ ((1 : ℂ) / 2 - (γ : ℂ) * Complex.I) := by
    rw [← Complex.cpow_add _ _ hne]
    congr 1
    ring
  rw [phasor, helixPt_eq_cpow _ hn, ← key, Complex.cpow_one, mul_div_assoc, div_self hne, mul_one]

open ArithmeticFunction in
/-- With every prime angle equal to `π`, the log-free winding angle is `π · Ω(n)`. -/
theorem windAngle_const_pi (n : ℕ) :
    windAngle (fun _ => Real.pi) n = Real.pi * (cardFactors n) := by
  rw [windAngle, cardFactors_eq_sum_factorization]
  rw [Finsupp.sum, Finsupp.sum, Nat.cast_sum, Finset.mul_sum]
  exact Finset.sum_congr rfl (fun p _ => by ring)

open ArithmeticFunction in
/-- **The Liouville grading is the all-`π` character.** -/
theorem wind_const_pi_eq_liouville (n : ℕ) :
    ((wind (fun _ => Real.pi) n : ℂ)) = (-1) ^ (cardFactors n) := by
  rw [wind, Circle.coe_exp, windAngle_const_pi]
  rw [show ((Real.pi * (cardFactors n) : ℝ) : ℂ) * Complex.I
        = (cardFactors n : ℂ) * (Real.pi * Complex.I) by push_cast; ring]
  rw [Complex.exp_nat_mul, Complex.exp_pi_mul_I]

end HelixLogFree

#print axioms HelixLogFree.helixPt_mul
#print axioms HelixLogFree.helixPt_eq_cpow
#print axioms HelixLogFree.norm_phasor_mul_sqrt
#print axioms HelixLogFree.phasor_eq_cpow_neg
#print axioms HelixLogFree.wind_const_pi_eq_liouville
