import RequestProject.ChiralityHB
import RequestProject.UnitMidpoint

/-!
# The pure carrier's zeros are simple: "clocks do not collide" (ledger 578 → compiled)

Ledger 578 (2026-09-03) recorded this as **header prose only**, "a few lines from
`prime_clocks_incommensurable`", in the same docstring-vs-theorem class as 575.  This is those lines.

The multiplicative carrier is the finite product of symmetrized prime clocks
`symClock α ℓ z = e^{izℓ/2} − α e^{−izℓ/2}`.  `ChiralityHB.carrier_zeros_real` already puts every zero
of a unitary-face product on the conjugation axis.  Here are the two facts that make those zeros
**simple**:

* `symClock_deriv_ne_zero` — every clock's own zeros are simple, for ANY nonzero face: at a zero the
  two strands agree, `e^{izℓ/2} = α e^{−izℓ/2}`, so `E'(z) = iℓ·α·e^{−izℓ/2} ≠ 0`.  No arithmetic input.
* `clocks_no_collision` — two face-`1` clocks at distinct primes share **only** `z = 0`; anywhere else
  a shared zero forces `log p / log q ∈ ℚ`, contradicting `prime_clocks_incommensurable`.

**The `z = 0` caveat is not a technicality and is stated, not hidden:** `symClock 1 ℓ 0 = 0` for every
`ℓ` (`symClock_one_zero_at_origin`), so ALL face-`1` clocks vanish at the origin simultaneously.  The
carrier's zeros are simple away from the origin; at the origin the order is the number of clocks.  A
carrier built from faces `α ≠ 1` has no common zero there (`symClock_zero_ne_of_face_ne_one`).

**Scope — this is NOT a statement about `ζ`.**  Ledger 578 records that in the `½`-centred chart
`s = ½ + iz` the Euler factor `1 − p^{−s}` is the clock with face `p^{−½}`, which is NOT unitary, so
its zeros sit at `Im z = ½` (`clock_zero_depth`).  The identification of carrier zeros with `L`-zeros
is `EveryZeroHasSource`, which is GRH.  No multiplicity statement about `ζ` follows from anything here.
-/

open Complex

namespace CriticalLinePhasor.ChiralityHB

/-! ### Every clock's own zeros are simple -/

/-- The clock's derivative, in closed form. -/
theorem symClock_hasDerivAt (α : ℂ) (ℓ : ℝ) (z : ℂ) :
    HasDerivAt (symClock α ℓ)
      (I * (ℓ : ℂ) / 2 *
        (Complex.exp (I * z * ℓ / 2) + α * Complex.exp (-(I * z * ℓ / 2)))) z := by
  have h1 : HasDerivAt (fun w : ℂ => I * w * (ℓ : ℂ) / 2) (I * (ℓ : ℂ) / 2) z := by
    simpa using (((hasDerivAt_id z).const_mul I).mul_const (ℓ : ℂ)).div_const 2
  have h2 : HasDerivAt (fun w : ℂ => -(I * w * (ℓ : ℂ) / 2)) (-(I * (ℓ : ℂ) / 2)) z := h1.neg
  have key := h1.cexp.sub (h2.cexp.const_mul α)
  have hval :
      I * (ℓ : ℂ) / 2 * (Complex.exp (I * z * ℓ / 2) + α * Complex.exp (-(I * z * ℓ / 2)))
        = Complex.exp (I * z * ℓ / 2) * (I * (ℓ : ℂ) / 2)
          - α * (Complex.exp (-(I * z * ℓ / 2)) * -(I * (ℓ : ℂ) / 2)) := by ring
  rw [hval]
  exact key

/-- **Every zero of a clock with a nonzero face is simple.**  No arithmetic input. -/
theorem symClock_deriv_ne_zero {α : ℂ} (hα : α ≠ 0) {ℓ : ℝ} (hℓ : ℓ ≠ 0) {z : ℂ}
    (hz : symClock α ℓ z = 0) :
    deriv (symClock α ℓ) z ≠ 0 := by
  have hstrand : Complex.exp (I * z * ℓ / 2) = α * Complex.exp (-(I * z * ℓ / 2)) := by
    have h := hz
    unfold symClock at h
    exact sub_eq_zero.mp h
  rw [(symClock_hasDerivAt α ℓ z).deriv, hstrand]
  have hne : Complex.exp (-(I * z * ℓ / 2)) ≠ 0 := Complex.exp_ne_zero _
  have hℓ' : (ℓ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hℓ
  have hcollapse :
      I * (ℓ : ℂ) / 2 *
          (α * Complex.exp (-(I * z * ℓ / 2)) + α * Complex.exp (-(I * z * ℓ / 2)))
        = I * (ℓ : ℂ) * α * Complex.exp (-(I * z * ℓ / 2)) := by ring
  rw [hcollapse]
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero Complex.I_ne_zero hℓ') hα) hne

/-! ### Distinct prime clocks collide only at the origin -/

/-- A face-`1` clock vanishes exactly on the lattice `z ℓ ∈ 2πℤ`. -/
theorem symClock_one_zero_iff (ℓ : ℝ) (z : ℂ) :
    symClock 1 ℓ z = 0 ↔ ∃ n : ℤ, z * (ℓ : ℂ) = 2 * (Real.pi : ℂ) * (n : ℂ) := by
  rw [symClock_zero_iff, Complex.exp_eq_one_iff]
  constructor
  · rintro ⟨n, hn⟩
    exact ⟨n, mul_left_cancel₀ Complex.I_ne_zero (by linear_combination hn)⟩
  · rintro ⟨n, hn⟩
    exact ⟨n, by linear_combination I * hn⟩

/-- The origin is a zero of every face-`1` clock.  (Stated so the caveat stays visible.) -/
theorem symClock_one_zero_at_origin (ℓ : ℝ) : symClock 1 ℓ 0 = 0 := by
  simp [symClock]

/-- **Clocks do not collide.**  Two face-`1` clocks at distinct primes share a zero only at the
origin: elsewhere a shared zero forces `log p / log q ∈ ℚ`, contradicting
`prime_clocks_incommensurable`. -/
theorem clocks_no_collision {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hne : p ≠ q) {z : ℂ}
    (hzp : symClock 1 (Real.log p) z = 0) (hzq : symClock 1 (Real.log q) z = 0) :
    z = 0 := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hq1 : (1 : ℝ) < q := by exact_mod_cast hq.one_lt
  have hlp : 0 < Real.log p := Real.log_pos hp1
  have hlq : 0 < Real.log q := Real.log_pos hq1
  obtain ⟨k, hk⟩ := (symClock_one_zero_iff _ _).mp hzp
  obtain ⟨m, hm⟩ := (symClock_one_zero_iff _ _).mp hzq
  by_contra hz0
  have hmne : m ≠ 0 := by
    rintro rfl
    apply hz0
    have h : z * (Real.log q : ℂ) = 0 := by simpa using hm
    exact (mul_eq_zero.mp h).resolve_right (Complex.ofReal_ne_zero.mpr hlq.ne')
  -- eliminate `z`: cross-multiplying the two lattice conditions
  have hcross : (Real.log p : ℂ) * (m : ℂ) = (Real.log q : ℂ) * (k : ℂ) := by
    have h1 : z * (Real.log p : ℂ) * (m : ℂ) = 2 * (Real.pi : ℂ) * (k : ℂ) * (m : ℂ) := by
      rw [hk]
    have h2 : z * (Real.log q : ℂ) * (k : ℂ) = 2 * (Real.pi : ℂ) * (m : ℂ) * (k : ℂ) := by
      rw [hm]
    refine mul_left_cancel₀ hz0 ?_
    linear_combination h1 - h2
  have hcrossR : Real.log p * (m : ℝ) = Real.log q * (k : ℝ) := by exact_mod_cast hcross
  refine CriticalLinePhasor.UnitMidpoint.prime_clocks_incommensurable hp hq hne
    ⟨(k : ℚ) / (m : ℚ), ?_⟩
  have hmR : (m : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hmne
  push_cast
  rw [div_eq_div_iff hmR hlq.ne']
  linarith [hcrossR]

/-- A face `α ≠ 1` clock does not vanish at the origin. -/
theorem symClock_zero_ne_of_face_ne_one {α : ℂ} (hα : α ≠ 1) (ℓ : ℝ) :
    symClock α ℓ 0 ≠ 0 := by
  unfold symClock
  simp only [mul_zero, zero_mul, zero_div, Complex.exp_zero, neg_zero, mul_one]
  intro h
  exact hα (sub_eq_zero.mp h).symm


/-! ### The carrier's zeros are simple away from the origin -/

/-- At most one clock of a distinct-prime carrier vanishes at any `z ≠ 0`. -/
theorem carrier_unique_vanishing_clock {ι : Type*} {s : Finset ι} {p : ι → ℕ}
    (hp : ∀ i ∈ s, (p i).Prime) (hinj : ∀ i ∈ s, ∀ j ∈ s, p i = p j → i = j)
    {z : ℂ} (hz0 : z ≠ 0) {i j : ι} (hi : i ∈ s) (hj : j ∈ s)
    (hzi : symClock 1 (Real.log (p i)) z = 0) (hzj : symClock 1 (Real.log (p j)) z = 0) :
    i = j := by
  by_contra hij
  exact hz0 (clocks_no_collision (hp i hi) (hp j hj) (fun h => hij (hinj i hi j hj h)) hzi hzj)

theorem symClock_differentiable (α : ℂ) (ℓ : ℝ) : Differentiable ℂ (symClock α ℓ) :=
  fun w => (symClock_hasDerivAt α ℓ w).differentiableAt

/-- **The pure carrier's zeros are simple away from the origin.**  Unconditional: the only inputs are
unique factorization (through `prime_clocks_incommensurable`) and the clock's own closed form. -/
theorem carrier_deriv_ne_zero {ι : Type*} [DecidableEq ι] {s : Finset ι} {p : ι → ℕ}
    (hp : ∀ i ∈ s, (p i).Prime) (hinj : ∀ i ∈ s, ∀ j ∈ s, p i = p j → i = j)
    {z : ℂ} (hz0 : z ≠ 0)
    (hz : (∏ i ∈ s, symClock 1 (Real.log (p i)) z) = 0) :
    deriv (fun w => ∏ i ∈ s, symClock 1 (Real.log (p i)) w) z ≠ 0 := by
  obtain ⟨i₀, hi₀, hzi₀⟩ := Finset.prod_eq_zero_iff.mp hz
  have hother : ∀ j ∈ s.erase i₀, symClock 1 (Real.log (p j)) z ≠ 0 := by
    intro j hj hzj
    rw [Finset.mem_erase] at hj
    exact hj.1 (carrier_unique_vanishing_clock hp hinj hz0 hj.2 hi₀ hzj hzi₀)
  have hGz : (∏ j ∈ s.erase i₀, symClock 1 (Real.log (p j)) z) ≠ 0 := by
    intro h
    obtain ⟨j, hj, hj0⟩ := Finset.prod_eq_zero_iff.mp h
    exact hother j hj hj0
  have hfun : (fun w => ∏ i ∈ s, symClock 1 (Real.log (p i)) w)
      = fun w => (∏ j ∈ s.erase i₀, symClock 1 (Real.log (p j)) w)
          * symClock 1 (Real.log (p i₀)) w :=
    funext fun w =>
      (Finset.prod_erase_mul s (fun i => symClock 1 (Real.log (p i)) w) hi₀).symm
  have hGd : DifferentiableAt ℂ
      (fun w => ∏ j ∈ s.erase i₀, symClock 1 (Real.log (p j)) w) z :=
    DifferentiableAt.fun_finsetProd
      (fun j _ => (symClock_differentiable 1 (Real.log (p j))).differentiableAt)
  have hgd : DifferentiableAt ℂ (symClock 1 (Real.log (p i₀))) z :=
    (symClock_differentiable 1 (Real.log (p i₀))).differentiableAt
  have hd0 : deriv (symClock 1 (Real.log (p i₀))) z ≠ 0 :=
    symClock_deriv_ne_zero one_ne_zero
      (Real.log_pos (by exact_mod_cast (hp i₀ hi₀).one_lt)).ne' hzi₀
  have key : HasDerivAt
      (fun w => (∏ j ∈ s.erase i₀, symClock 1 (Real.log (p j)) w)
        * symClock 1 (Real.log (p i₀)) w)
      (deriv (fun w => ∏ j ∈ s.erase i₀, symClock 1 (Real.log (p j)) w) z
          * symClock 1 (Real.log (p i₀)) z
        + (∏ j ∈ s.erase i₀, symClock 1 (Real.log (p j)) z)
          * deriv (symClock 1 (Real.log (p i₀))) z) z :=
    hGd.hasDerivAt.mul hgd.hasDerivAt
  rw [hfun, key.deriv, hzi₀]
  simpa using mul_ne_zero hGz hd0

end CriticalLinePhasor.ChiralityHB

#print axioms CriticalLinePhasor.ChiralityHB.symClock_deriv_ne_zero
#print axioms CriticalLinePhasor.ChiralityHB.clocks_no_collision
#print axioms CriticalLinePhasor.ChiralityHB.symClock_one_zero_at_origin
#print axioms CriticalLinePhasor.ChiralityHB.carrier_deriv_ne_zero
