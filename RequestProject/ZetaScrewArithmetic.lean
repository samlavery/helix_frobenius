import RequestProject.ZetaScrewFourier
import RequestProject.SeatMassEtaForm

/-!
# The helix profile's transform, fully arithmetic; and the ends' profile (Track E)

* `logDeriv_riemannXi_arith` — on `Re s > 1` the completed log-derivative is
  `1/s + 1/(s−1) − ½ log π + ½ Γ′/Γ(s/2) − Σ_n Λ(n) n^{−s}` (compiled splice + Mathlib's
  `LSeries_vonMangoldt_eq_deriv_riemannZeta_div`): the two ENDS, the Archimedean clock, and the
  WINDING as the von Mangoldt Dirichlet series.
* `zetaScrew_fourier_arith` — **for `Im z > ½` and `s = ½ − iz`,**
  `∫₀^∞ Ψ(t) e^{izt} dt = −z⁻²[1/s + 1/(s−1) − ½ log π + ½ Γ′/Γ(s/2) − Σ Λ(n) n^{−s}]`:
  the zero-side helix profile's transform written in prime data alone — the transform side of
  the explicit formula in profile form.
* `endsProfile`, `endsProfile_laplace` — the ends' time-domain profile `4(e^{t/2} + e^{−t/2} − 2)`
  (Suzuki (1.1), first term) has transform `−z⁻²(1/s + 1/(s−1))`: the pole block of the
  arithmetic side is exactly the ends' contribution to Ψ.  First of the three fields of
  Suzuki's Thm 1.1(2).

No `sorry`, no `axiom`.
-/

open Complex Filter Topology MeasureTheory ArithmeticFunction

noncomputable section

namespace CriticalLinePhasor.HilbertPolya

open CriticalLinePhasor.StBridge CriticalLinePhasor.SeatingLedger

/-- **The completed log-derivative on `Re s > 1` is arithmetic**: ends + Archimedean clock −
von Mangoldt Dirichlet series. -/
theorem logDeriv_riemannXi_arith {s : ℂ} (hs : 1 < s.re) :
    logDeriv ZD.riemannXi s
      = 1 / s + 1 / (s - 1) - ((Real.log Real.pi : ℝ) : ℂ) / 2
        + logDeriv Complex.Gamma (s / 2) / 2
        - LSeries (fun n => ((Λ n : ℝ) : ℂ)) s := by
  have hs0 : 0 < s.re := by linarith
  have hs1 : s ≠ 1 := by
    intro h
    rw [h] at hs
    simp at hs
  have hz : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_one_le_re hs.le
  rw [logDeriv_riemannXi_splice hs0 hs1 hz, LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs]
  simp only [logDeriv_apply]
  ring

/-- `Re(½ − iz) = ½ + Im z`. -/
theorem half_sub_I_mul_re (z : ℂ) : ((1 / 2 : ℂ) - Complex.I * z).re = 1 / 2 + z.im := by
  simp [Complex.sub_re, Complex.mul_re]

/-- **The helix profile's transform in prime data** (`Im z > ½`, `s = ½ − iz`). -/
theorem zetaScrew_fourier_arith {z : ℂ} (hz : 1 / 2 < z.im) :
    ∫ t in Set.Ioi (0 : ℝ), zetaScrew t * Complex.exp (Complex.I * z * t)
      = -(1 / z ^ 2) * (1 / (1 / 2 - Complex.I * z) + 1 / ((1 / 2 - Complex.I * z) - 1)
          - ((Real.log Real.pi : ℝ) : ℂ) / 2
          + logDeriv Complex.Gamma ((1 / 2 - Complex.I * z) / 2) / 2
          - LSeries (fun n => ((Λ n : ℝ) : ℂ)) (1 / 2 - Complex.I * z)) := by
  have hre : 1 < ((1 / 2 : ℂ) - Complex.I * z).re := by
    rw [half_sub_I_mul_re]
    linarith
  rw [zetaScrew_fourier hz, logDeriv_riemannXi_arith hre]

/-! ## The ends' profile -/

/-- The ends' time-domain profile: `4(e^{t/2} + e^{−t/2} − 2)` (Suzuki (1.1), first term). -/
def endsProfile (t : ℝ) : ℂ := 4 * (Complex.exp (t / 2) + Complex.exp (-(t / 2)) - 2)

/-- The ends' profile as three complex exponentials in `t`. -/
theorem endsProfile_mul_exp_eq (z : ℂ) (t : ℝ) :
    endsProfile t * Complex.exp (Complex.I * z * t)
      = 4 * (Complex.exp ((Complex.I * z + 1 / 2) * t)
          + Complex.exp ((Complex.I * z - 1 / 2) * t)
          - 2 * Complex.exp ((Complex.I * z) * t)) := by
  unfold endsProfile
  have h1 : Complex.exp ((t : ℂ) / 2) * Complex.exp (Complex.I * z * t)
      = Complex.exp ((Complex.I * z + 1 / 2) * t) := by
    rw [← Complex.exp_add]; congr 1; ring
  have h2 : Complex.exp (-((t : ℂ) / 2)) * Complex.exp (Complex.I * z * t)
      = Complex.exp ((Complex.I * z - 1 / 2) * t) := by
    rw [← Complex.exp_add]; congr 1; ring
  rw [← h1, ← h2]
  ring

/-- **The ends' profile has transform `−z⁻²(1/s + 1/(s−1))`, `s = ½ − iz`** (`Im z > ½`): the pole
block of the arithmetic side is exactly the ends' contribution to `Ψ`. -/
theorem endsProfile_laplace {z : ℂ} (hz : 1 / 2 < z.im) :
    ∫ t in Set.Ioi (0 : ℝ), endsProfile t * Complex.exp (Complex.I * z * t)
      = -(1 / z ^ 2) * (1 / (1 / 2 - Complex.I * z) + 1 / ((1 / 2 - Complex.I * z) - 1)) := by
  have ha₁ : (Complex.I * z + 1 / 2).re < 0 := by
    rw [Complex.add_re, I_mul_re_neg]
    norm_num
    linarith
  have ha₂ : (Complex.I * z - 1 / 2).re < 0 := by
    rw [Complex.sub_re, I_mul_re_neg]
    norm_num
    linarith
  have ha₃ : (Complex.I * z).re < 0 := by
    rw [I_mul_re_neg]
    linarith
  have hfun : (fun t : ℝ => endsProfile t * Complex.exp (Complex.I * z * t))
      = fun t : ℝ => 4 * (Complex.exp ((Complex.I * z + 1 / 2) * t)
          + Complex.exp ((Complex.I * z - 1 / 2) * t)
          - 2 * Complex.exp ((Complex.I * z) * t)) := by
    funext t
    exact endsProfile_mul_exp_eq z t
  have hi₁ := integrableOn_exp_mul_complex_Ioi ha₁ 0
  have hi₂ := integrableOn_exp_mul_complex_Ioi ha₂ 0
  have hi₃ := integrableOn_exp_mul_complex_Ioi ha₃ 0
  have hi₁₂ : IntegrableOn (fun x : ℝ => Complex.exp ((Complex.I * z + 1 / 2) * x)
      + Complex.exp ((Complex.I * z - 1 / 2) * x)) (Set.Ioi 0) volume := hi₁.add hi₂
  have hi₃' : IntegrableOn (fun x : ℝ => 2 * Complex.exp ((Complex.I * z) * x))
      (Set.Ioi 0) volume := hi₃.const_mul 2
  rw [hfun, integral_const_mul, integral_sub hi₁₂ hi₃', integral_add hi₁ hi₂,
    integral_const_mul, integral_exp_mul_complex_Ioi ha₁ 0, integral_exp_mul_complex_Ioi ha₂ 0,
    integral_exp_mul_complex_Ioi ha₃ 0]
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero]
  -- substitute `w = iz`: everything is rational in `w`, with `z² = −w²`
  set w : ℂ := Complex.I * z with hw
  have hwre : w.re = -z.im := by rw [hw]; exact I_mul_re_neg z
  have hre_add : (w + 1 / 2).re = -z.im + 1 / 2 := by
    rw [Complex.add_re, hwre]; norm_num
  have hre_sub : (w - 1 / 2).re = -z.im - 1 / 2 := by
    rw [Complex.sub_re, hwre]; norm_num
  have hre_s : ((1 / 2 : ℂ) - w).re = 1 / 2 + z.im := by
    rw [Complex.sub_re, hwre]; norm_num
  have hre_s1 : ((1 / 2 : ℂ) - w - 1).re = z.im - 1 / 2 := by
    rw [Complex.sub_re, Complex.sub_re, hwre]; norm_num; ring
  have hw0 : w ≠ 0 := by
    intro h; have := congrArg Complex.re h; rw [hwre, Complex.zero_re] at this; linarith
  have hn₁ : w + 1 / 2 ≠ 0 := by
    intro h; have := congrArg Complex.re h; rw [hre_add, Complex.zero_re] at this; linarith
  have hn₂ : w - 1 / 2 ≠ 0 := by
    intro h; have := congrArg Complex.re h; rw [hre_sub, Complex.zero_re] at this; linarith
  have hs0 : (1 / 2 : ℂ) - w ≠ 0 := by
    intro h; have := congrArg Complex.re h; rw [hre_s, Complex.zero_re] at this; linarith
  have hs1 : (1 / 2 : ℂ) - w - 1 ≠ 0 := by
    intro h; have := congrArg Complex.re h; rw [hre_s1, Complex.zero_re] at this; linarith
  have hz2 : z ^ 2 = -(w ^ 2) := by
    rw [hw, mul_pow, Complex.I_sq]
    ring
  rw [hz2]
  -- clear the denominators by hand: both sides become `−2w²(w² − ¼)`
  rw [div_add_div _ _ hn₁ hn₂, div_add_div _ _ hs0 hs1, mul_div_assoc',
    div_sub_div _ _ (mul_ne_zero hn₁ hn₂) hw0, div_neg, neg_neg, div_mul_div_comm,
    mul_div_assoc',
    div_eq_div_iff (mul_ne_zero (mul_ne_zero hn₁ hn₂) hw0)
      (mul_ne_zero (pow_ne_zero 2 hw0) (mul_ne_zero hs0 hs1))]
  ring

end CriticalLinePhasor.HilbertPolya

#print axioms CriticalLinePhasor.HilbertPolya.logDeriv_riemannXi_arith
#print axioms CriticalLinePhasor.HilbertPolya.zetaScrew_fourier_arith
#print axioms CriticalLinePhasor.HilbertPolya.endsProfile_laplace
