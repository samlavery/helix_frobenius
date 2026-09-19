import RequestProject.LogWeightOperator
import RequestProject.ThetaTransport
import RequestProject.FoliatedDeterminant

/-!
# The carrier Hamiltonian: ζ as the partition function of the log-weight operator

`RequestProject/LogWeightOperator.lean` established that the paper's log-weight operator `H`
— multiplication by `log (n+1)` on the `n`-th phasor of `ℓ²(ℕ, ℂ)` — is self-adjoint on its
maximal domain, with the phasors a total orthonormal eigenbasis.  This file supplies the
other half of the Hilbert–Pólya-style reading: **`H` is the carrier's Hamiltonian, and the
Riemann zeta function is its partition function.**  Every statement is unconditional.

* `heat s` is the heat semigroup `e^{−sH}`: on the `n`-th phasor it acts by the Dirichlet
  factor `(n+1)^{−s}`, and `heat_eigenvalue_eq_exp` identifies that factor as
  `exp (−s · λ_n)` with `λ_n = log (n+1)` the eigenvalue of `H` (`H_phasor`).  This is the
  functional calculus of `H` read on its eigenbasis, and it is the sense in which `H`
  *generates* the warp: the paper's phrase "radial generator" is this theorem.
* `zeta_eq_heatTrace` : for `Re s > 1`, `Tr e^{−sH} = Σ_n ⟪e_n, e^{−sH} e_n⟫ = ζ(s)` —
  the fiber's readout is the trace of the Hamiltonian's semigroup.
* `vonMangoldt_heatTrace_eq` : the von Mangoldt–weighted trace of `e^{−sH}` is `−ζ'/ζ(s)`:
  **the prime side of the explicit formula is a trace of a function of `H`.**
* `logWeight_eq_sum_primeClocks`, `primeClock_isSelfAdjoint` : `H` is the sum of the
  commuting self-adjoint prime clocks `log p · N_p`, `N_p` the `p`-adic valuation at each
  site — the Euler product, read on the operator — and `heatTrace_eulerProduct` factorises
  the partition function accordingly.
* `riemannXi_eq_completed_heatTrace`, `spectralDet_eq_completed_heatTrace` : the entire
  readout `ξ`, and hence the spectral determinant of the zero operator `Θ`
  (`FoliatedDeterminant`), is the *completed* partition function of `H`.  Combined with
  `spectralDet_eq_zero_iff_spectralCoord`, the spectrum of `Θ` is exactly the zero set of the
  completed `H`-partition function.

What this makes precise.  The Hilbert–Pólya frame in this corpus has two operators, and they
must not be confused: `H` (this file, `LogWeightOperator`) is built from the carrier alone,
with no zero set in its definition, self-adjoint on a genuine Hilbert space, and *generates
the prime side*; `Θ` (`FoliatedPolarization`, `FoliatedDeterminant`) has the zeros as
spectrum and is self-adjoint for the functional-equation pairing (`blockOp_selfAdjoint`).  The
identity proved here — `spectralDet Θ = completed (Tr e^{−sH})` — is the bridge between them.
-/

open scoped BigOperators ComplexConjugate LinearPMap LSeries.notation
open CarrierReadout

noncomputable section

namespace CarrierReadout

/-! ### Complex-weight multiplication on the maximal domain -/

/-- The maximal domain of multiplication by a complex weight `w`. -/
def cweightDomain (w : ℕ → ℂ) : Submodule ℂ L2 where
  carrier := {v : L2 | Memℓp (fun n => w n * v n) 2}
  zero_mem' := by
    have : (fun n => w n * (0 : L2) n) = fun _ => (0 : ℂ) := by
      funext n; simp
    rw [Set.mem_ofPred_eq, this]
    exact zero_memℓp
  add_mem' := by
    intro u v hu hv
    have : (fun n => w n * (u + v) n)
        = (fun n => w n * u n) + (fun n => w n * v n) := by
      funext n; simp [mul_add]
    rw [Set.mem_ofPred_eq, this]
    exact Memℓp.add hu hv
  smul_mem' := by
    intro c v hv
    have : (fun n => w n * (c • v) n) = c • (fun n => w n * v n) := by
      funext n; simp [Pi.smul_apply, smul_eq_mul]; ring
    rw [Set.mem_ofPred_eq, this]
    exact Memℓp.const_smul hv c

theorem mem_cweightDomain_iff (w : ℕ → ℂ) (v : L2) :
    v ∈ cweightDomain w ↔ Memℓp (fun n => w n * v n) 2 := Iff.rfl

/-- Multiplication by a complex weight `w` on its maximal domain. -/
def cweightMul (w : ℕ → ℂ) : L2 →ₗ.[ℂ] L2 where
  domain := cweightDomain w
  toFun :=
    { toFun := fun v => ⟨fun n => w n * (v : L2) n, v.2⟩
      map_add' := by
        intro u v
        apply lp.ext
        funext n
        simp [mul_add]
        rfl
      map_smul' := by
        intro c v
        apply lp.ext
        funext n
        simp [smul_eq_mul]
        ring }

@[simp]
theorem cweightMul_apply_coe (w : ℕ → ℂ) (v : (cweightMul w).domain) (n : ℕ) :
    ((cweightMul w v : L2) : ℕ → ℂ) n = w n * ((v : L2) : ℕ → ℂ) n := rfl

@[simp]
theorem cweightMul_domain (w : ℕ → ℂ) : (cweightMul w).domain = cweightDomain w := rfl

theorem phasor_mem_cweightDomain (w : ℕ → ℂ) (n : ℕ) : phasor n ∈ cweightDomain w := by
  rw [mem_cweightDomain_iff]
  have h : (fun m => w m * (phasor n) m) = ⇑(lp.single 2 n (w n)) := by
    funext m
    by_cases hm : m = n
    · subst hm; simp [phasor]
    · simp [phasor, Pi.single_eq_of_ne hm]
  rw [h]
  exact lp.memℓp _

theorem cweightMul_phasor (w : ℕ → ℂ) (n : ℕ) :
    cweightMul w ⟨phasor n, phasor_mem_cweightDomain w n⟩ = w n • phasor n := by
  apply lp.ext
  funext m
  by_cases h : m = n
  · subst h; rfl
  · rw [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
    change w m * ((phasor n : L2) : ℕ → ℂ) m = _
    simp [phasor, lp.single_apply, h]

/-! ### The heat semigroup `e^{−sH}` -/

/-- The heat semigroup of the carrier Hamiltonian, `e^{−sH}`: on the `n`-th phasor
(site `n+1`) it acts by the Dirichlet factor `(n+1)^{−s}`. -/
def heat (s : ℂ) : L2 →ₗ.[ℂ] L2 := cweightMul (fun n => ((n : ℂ) + 1) ^ (-s))

theorem heat_phasor (s : ℂ) (n : ℕ) :
    heat s ⟨phasor n, phasor_mem_cweightDomain _ n⟩ = (((n : ℂ) + 1) ^ (-s)) • phasor n :=
  cweightMul_phasor _ n

/-- **`heat s` is `e^{−sH}` on the eigenbasis.**  The eigenvalue of `heat s` on the `n`-th
phasor is `exp (−s · λ_n)`, where `λ_n = log (n+1)` is the eigenvalue of `H` (`H_phasor`).
This is the functional calculus of the self-adjoint `H`, read on its total eigenbasis, and
it is the precise content of the paper's phrase "`H` is the radial generator". -/
theorem heat_eigenvalue_eq_exp (s : ℂ) (n : ℕ) :
    ((n : ℂ) + 1) ^ (-s) = Complex.exp (-s * (logWeight n : ℂ)) := by
  have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hne : ((n : ℂ) + 1) ≠ 0 := by exact_mod_cast hpos.ne'
  have hlog : Complex.log ((n : ℂ) + 1) = (Real.log ((n : ℝ) + 1) : ℂ) := by
    rw [Complex.ofReal_log hpos.le]; push_cast; rfl
  rw [Complex.cpow_def_of_ne_zero hne, hlog]
  simp only [logWeight]
  ring_nf

/-- The semigroup law on the eigenbasis: `e^{−sH} e^{−s'H} = e^{−(s+s')H}`. -/
theorem heat_eigenvalue_add (s s' : ℂ) (n : ℕ) :
    ((n : ℂ) + 1) ^ (-(s + s')) = ((n : ℂ) + 1) ^ (-s) * ((n : ℂ) + 1) ^ (-s') := by
  have hne : ((n : ℂ) + 1) ≠ 0 := by
    have : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    exact_mod_cast this.ne'
  rw [neg_add, Complex.cpow_add _ _ hne]

/-- The diagonal matrix element of the heat semigroup: `⟪e_n, e^{−sH} e_n⟫ = (n+1)^{−s}`. -/
theorem inner_phasor_heat (s : ℂ) (n : ℕ) :
    inner ℂ (phasor n) (heat s ⟨phasor n, phasor_mem_cweightDomain _ n⟩ : L2)
      = ((n : ℂ) + 1) ^ (-s) := by
  rw [heat_phasor, inner_smul_right]
  have h1 : inner ℂ (phasor n) (phasor n) = (1 : ℂ) := by
    rw [inner_self_eq_norm_sq_to_K, phasor_orthonormal.1 n]
    simp
  rw [h1, mul_one]

/-! ### ζ is the partition function of `H` -/

/-- **ζ is the partition function of the carrier Hamiltonian.**  For `Re s > 1`,
`Tr e^{−sH} = Σ_n ⟪e_n, e^{−sH} e_n⟫ = ζ(s)`: the fiber's readout is the trace of the heat
semigroup of the self-adjoint log-weight operator. -/
theorem zeta_eq_heatTrace {s : ℂ} (hs : 1 < s.re) :
    ∑' n, inner ℂ (phasor n) (heat s ⟨phasor n, phasor_mem_cweightDomain _ n⟩ : L2)
      = riemannZeta s := by
  simp_rw [inner_phasor_heat]
  rw [zeta_eq_tsum_one_div_nat_add_one_cpow hs]
  refine tsum_congr fun n => ?_
  rw [Complex.cpow_neg, one_div]

/-- **The prime side of the explicit formula is a trace.**  The von Mangoldt–weighted trace
of `e^{−sH}` over the phasor basis is `−ζ'/ζ(s)` for `Re s > 1`. -/
theorem vonMangoldt_heatTrace_eq {s : ℂ} (hs : 1 < s.re) :
    ∑' n, (ArithmeticFunction.vonMangoldt (n + 1) : ℂ) *
        inner ℂ (phasor n) (heat s ⟨phasor n, phasor_mem_cweightDomain _ n⟩ : L2)
      = - deriv riemannZeta s / riemannZeta s := by
  rw [← ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs]
  simp_rw [inner_phasor_heat]
  unfold LSeries
  rw [Summable.tsum_eq_zero_add (ArithmeticFunction.LSeriesSummable_vonMangoldt hs),
    LSeries.term_zero, zero_add]
  refine tsum_congr fun n => ?_
  rw [LSeries.term_of_ne_zero (Nat.succ_ne_zero n)]
  push_cast
  rw [Complex.cpow_neg, div_eq_mul_inv]

/-! ### The Euler product, read on the operator: `H = Σ_p log p · N_p` -/

/-- The `p`-th **prime clock**: the self-adjoint operator `log p · N_p`, where `N_p` reads the
power of `p` at each site.  On the `n`-th phasor (site `n+1`) its eigenvalue is
`log p · v_p(n+1)`. -/
def primeClock (p : ℕ) : L2 →ₗ.[ℂ] L2 :=
  weightMul (fun n => Real.log p * ((n + 1).factorization p : ℝ))

theorem primeClock_isSelfAdjoint (p : ℕ) : IsSelfAdjoint (primeClock p) :=
  weightMul_isSelfAdjoint _

theorem primeClock_phasor (p n : ℕ) :
    primeClock p ⟨phasor n, phasor_mem_weightDomain _ n⟩
      = ((Real.log p * ((n + 1).factorization p : ℝ) : ℝ) : ℂ) • phasor n :=
  weightMul_phasor _ n

/-- **The Euler product on the operator.**  The eigenvalue of `H` at site `n+1` is the sum of
the prime-clock eigenvalues: `log (n+1) = Σ_{p | n+1} log p · v_p(n+1)`.  `H` is the sum of
the commuting self-adjoint prime clocks — the multiplicative structure of the sites, which
is what the Euler product expresses, is carried by the operator itself. -/
theorem logWeight_eq_sum_primeClocks (n : ℕ) :
    logWeight n = ∑ p ∈ (n + 1).primeFactors, Real.log p * ((n + 1).factorization p : ℝ) := by
  have h := Real.log_nat_eq_sum_factorization (n + 1)
  rw [Finsupp.sum, Nat.support_factorization] at h
  unfold logWeight
  push_cast at h
  rw [h]
  refine Finset.sum_congr rfl fun p _ => ?_
  ring

/-- The partition function factorises over the prime clocks: `Tr e^{−sH} = ∏_p (1 − p^{−s})⁻¹`
for `Re s > 1`.  Each factor `(1 − p^{−s})⁻¹ = Σ_k e^{−s · k log p}` is the partition function
of the single clock `log p · N_p` (`primeClock_partition`). -/
theorem heatTrace_eulerProduct {s : ℂ} (hs : 1 < s.re) :
    ∑' n, inner ℂ (phasor n) (heat s ⟨phasor n, phasor_mem_cweightDomain _ n⟩ : L2)
      = ∏' p : Nat.Primes, (1 - (p : ℂ) ^ (-s))⁻¹ := by
  rw [zeta_eq_heatTrace hs, riemannZeta_eulerProduct_tprod hs]

/-- The partition function of a single prime clock is the geometric series in `p^{−s}`. -/
theorem primeClock_partition {s : ℂ} (hs : 1 < s.re) (p : Nat.Primes) :
    ∑' k : ℕ, ((p : ℂ) ^ (-s)) ^ k = (1 - (p : ℂ) ^ (-s))⁻¹ := by
  refine tsum_geometric_of_norm_lt_one ?_
  have hp : (1 : ℝ) < (p : ℕ) := by exact_mod_cast p.2.one_lt
  rw [Complex.norm_natCast_cpow_of_pos p.2.pos, Complex.neg_re]
  exact Real.rpow_lt_one_of_one_lt_of_neg hp (by linarith)

/-! ### The spectral determinant of `Θ` is the completed partition function of `H` -/

/-- **The entire readout is the completed partition function of `H`.**  For `Re s > 1`,
`ξ(s) = (s(s−1)/2) · Γ_ℝ(s) · Tr e^{−sH}`. -/
theorem riemannXi_eq_completed_heatTrace {s : ℂ} (hs : 1 < s.re) :
    ZD.riemannXi s = (s * (s - 1) / 2) * Complex.Gammaℝ s *
      ∑' n, inner ℂ (phasor n) (heat s ⟨phasor n, phasor_mem_cweightDomain _ n⟩ : L2) := by
  have hs0 : s ≠ 0 := by rintro rfl; norm_num at hs
  have hs1 : s ≠ 1 := by rintro rfl; norm_num at hs
  have hG : Complex.Gammaℝ s ≠ 0 := Complex.Gammaℝ_ne_zero_of_re_pos (by linarith)
  rw [zeta_eq_heatTrace hs, ZD.riemannXi_eq_classical_of_ne_zero_of_ne_one s hs0 hs1,
    riemannZeta_def_of_ne_zero hs0]
  field_simp

/-- **The spectral determinant of the zero operator `Θ` is the completed partition function of
the carrier Hamiltonian `H`.**  With `s = ½ + iw` and `Im w < −½`,
`spectralDet w = (s(s−1)/2) · Γ_ℝ(s) · Tr e^{−sH}`.  Together with
`spectralDet_eq_zero_iff_spectralCoord`, the spectrum of `Θ` is the zero set of the analytic
continuation of the completed `H`-partition function. -/
theorem spectralDet_eq_completed_heatTrace {w : ℂ} (hw : w.im < -1 / 2) :
    CriticalLinePhasor.FoliatedDeterminant.spectralDet w
      = ((1 / 2 + Complex.I * w) * ((1 / 2 + Complex.I * w) - 1) / 2)
          * Complex.Gammaℝ (1 / 2 + Complex.I * w) *
        ∑' n, inner ℂ (phasor n)
          (heat (1 / 2 + Complex.I * w) ⟨phasor n, phasor_mem_cweightDomain _ n⟩ : L2) := by
  have hs : 1 < (1 / 2 + Complex.I * w).re := by
    simp [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im]
    linarith
  unfold CriticalLinePhasor.FoliatedDeterminant.spectralDet
  exact riemannXi_eq_completed_heatTrace hs

end CarrierReadout
