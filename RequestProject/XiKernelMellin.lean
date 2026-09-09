import Mathlib

/-!
# T1a, steps 1–2: the completed zeta as an integral of the theta kernel (ledger 667)

Mathlib defines `completedRiemannZeta s = Λ(s/2)/2` for the Hurwitz even FE-pair at `a = 0`, whose
`f` is the theta kernel `θ(t) = Σ_{n∈ℤ} e^{−πn²t}` (`evenKernel 0`) with `f₀ = 1`.  `WeakFEPair.hasMellin`
gives, for `Re s > 1`,
  `Λ(s) = ½ ∫_0^∞ t^{s/2−1} (θ(t) − 1) dt`                              (step 1)
and the substitution `t = e^{2u}` gives
  `Λ(s) = 2 ∫_ℝ e^{su} Ψ(u) du`,  `Ψ(u) = (θ(e^{2u}) − 1)/2 = ψ(e^{2u})`.   (step 2)
Steps 3–5 (two integrations by parts turning `½ s(s−1)` into `Ψ″ + Ψ′`, evenness of the kernel from the
theta functional equation, analytic continuation) are the rest of T1a.
-/

open Complex HurwitzZeta MeasureTheory Set

namespace CriticalLinePhasor.XiKernel

/-- **Step 1.** For `Re s > 1`, `Λ(s) = ½ · mellin (θ − 1) (s/2)`. -/
theorem completedRiemannZeta_eq_mellin_theta {s : ℂ} (hs : 1 < s.re) :
    completedRiemannZeta s
      = (1 / 2 : ℂ) * mellin (fun t : ℝ => ((evenKernel 0 t : ℝ) : ℂ) - 1) (s / 2) := by
  have hk : (hurwitzEvenFEPair 0).k < (s / 2).re := by
    simp only [hurwitzEvenFEPair, Complex.div_ofNat_re]
    linarith
  have h := (hurwitzEvenFEPair 0).hasMellin hk
  have hΛ : (hurwitzEvenFEPair 0).Λ (s / 2)
      = mellin (fun t : ℝ => ((evenKernel 0 t : ℝ) : ℂ) - 1) (s / 2) := by
    rw [← h.2]
    congr 1
    funext t
    simp [hurwitzEvenFEPair]
  show completedHurwitzZetaEven 0 s = _
  unfold completedHurwitzZetaEven
  rw [hΛ]
  ring

/-- `Ψ(u) = ψ(e^{2u}) = (θ(e^{2u}) − 1)/2`. -/
noncomputable def Psi (u : ℝ) : ℝ := (evenKernel 0 (Real.exp (2 * u)) - 1) / 2

theorem image_exp_two_mul_univ : (fun u : ℝ => Real.exp (2 * u)) '' univ = Ioi 0 := by
  ext y
  constructor
  · rintro ⟨u, -, rfl⟩; exact Real.exp_pos _
  · intro hy
    refine ⟨Real.log y / 2, mem_univ _, ?_⟩
    show Real.exp (2 * (Real.log y / 2)) = y
    rw [show 2 * (Real.log y / 2) = Real.log y by ring, Real.exp_log hy]

/-- The complex power of a real exponential: `(e^{2u})^{w} = e^{2uw}`. -/
theorem ofReal_exp_cpow (u : ℝ) (w : ℂ) :
    ((Real.exp (2 * u) : ℝ) : ℂ) ^ w = Complex.exp (((2 * u : ℝ) : ℂ) * w) := by
  rw [Complex.ofReal_exp, Complex.cpow_def_of_ne_zero (Complex.exp_ne_zero _),
    Complex.log_exp (by simp; linarith [Real.pi_pos]) (by simp; linarith [Real.pi_pos])]

/-- **Step 2.** For `Re s > 1`, `Λ(s) = 2 ∫_ℝ e^{su} Ψ(u) du`. -/
theorem completedRiemannZeta_eq_integral_Psi {s : ℂ} (hs : 1 < s.re) :
    completedRiemannZeta s = 2 * ∫ u : ℝ, Complex.exp (s * (u : ℂ)) * (Psi u : ℂ) := by
  have hderiv : ∀ u ∈ (univ : Set ℝ),
      HasDerivWithinAt (fun u : ℝ => Real.exp (2 * u)) (2 * Real.exp (2 * u)) univ u := by
    intro u _
    have h1 : HasDerivAt (fun u : ℝ => 2 * u) 2 u := by
      simpa using (hasDerivAt_id u).const_mul (2 : ℝ)
    exact (h1.exp.congr_deriv (by ring)).hasDerivWithinAt
  have hinj : InjOn (fun u : ℝ => Real.exp (2 * u)) univ := by
    intro a _ b _ h
    have := Real.exp_injective h
    linarith
  rw [completedRiemannZeta_eq_mellin_theta hs, mellin, ← image_exp_two_mul_univ,
    integral_image_eq_integral_abs_deriv_smul MeasurableSet.univ hderiv hinj,
    Measure.restrict_univ, ← integral_const_mul]
  conv_rhs => rw [← integral_const_mul]
  congr 1
  funext u
  rw [ofReal_exp_cpow]
  simp only [Psi, abs_of_pos (by positivity : (0:ℝ) < 2 * Real.exp (2 * u)),
    real_smul, smul_eq_mul, Complex.ofReal_mul, Complex.ofReal_ofNat, Complex.ofReal_exp,
    Complex.ofReal_div, Complex.ofReal_sub, Complex.ofReal_one]
  have hexp : Complex.exp (s * u) = Complex.exp (2 * u) * Complex.exp (2 * u * (s / 2 - 1)) := by
    rw [← Complex.exp_add]; congr 1; ring
  rw [hexp]
  ring

end CriticalLinePhasor.XiKernel

#print axioms CriticalLinePhasor.XiKernel.completedRiemannZeta_eq_mellin_theta
#print axioms CriticalLinePhasor.XiKernel.completedRiemannZeta_eq_integral_Psi
