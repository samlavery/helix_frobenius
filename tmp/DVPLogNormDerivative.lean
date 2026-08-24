import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import RequestProject.XiHadamardFactorization

open Complex InnerProductSpace

noncomputable section

namespace CriticalLinePhasor.DVP

/-- Half the logarithm of the squared xi modulus on a horizontal line. -/
def xiLogNormSqHorizontal (t sigma : ℝ) : ℝ :=
  Real.log (‖ZD.riemannXi ((sigma : ℂ) + Complex.I * (t : ℂ))‖ ^ 2) / 2

/-- The horizontal derivative of `log ‖xi‖` is the real logarithmic derivative. -/
theorem hasDerivAt_xiLogNormSqHorizontal {t sigma : ℝ}
    (hxi : ZD.riemannXi ((sigma : ℂ) + Complex.I * (t : ℂ)) ≠ 0) :
    HasDerivAt (xiLogNormSqHorizontal t)
      (logDeriv ZD.riemannXi ((sigma : ℂ) + Complex.I * (t : ℂ))).re sigma := by
  let s : ℂ := (sigma : ℂ) + Complex.I * (t : ℂ)
  have han : AnalyticAt ℂ ZD.riemannXi s :=
    ZD.ZeroCount.riemannXi_analyticOnNhd_univ s (Set.mem_univ _)
  have hd : HasDerivAt ZD.riemannXi (deriv ZD.riemannXi s) s :=
    han.differentiableAt.hasDerivAt
  have haff : HasDerivAt (fun z : ℂ => z + Complex.I * (t : ℂ)) 1 (sigma : ℂ) :=
    (hasDerivAt_id' (sigma : ℂ)).add_const _
  have hcomp : HasDerivAt
      (fun z : ℂ => ZD.riemannXi (z + Complex.I * (t : ℂ)))
      (deriv ZD.riemannXi s) (sigma : ℂ) := by
    simpa only [Function.comp_def, s, mul_one] using hd.comp (sigma : ℂ) haff
  have hreal : HasDerivAt
      (fun x : ℝ => ZD.riemannXi ((x : ℂ) + Complex.I * (t : ℂ)))
      (deriv ZD.riemannXi s) sigma := hcomp.comp_ofReal
  have hsq := hreal.norm_sq
  have hsqne : ‖ZD.riemannXi s‖ ^ 2 ≠ 0 := by positivity
  have hlog := hsq.log hsqne
  have hhalf := hlog.const_mul (1 / 2 : ℝ)
  have hquotient :
      (1 / 2 : ℝ) *
          (2 * ⟪ZD.riemannXi s, deriv ZD.riemannXi s⟫_ℝ /
            ‖ZD.riemannXi s‖ ^ 2) =
        (deriv ZD.riemannXi s / ZD.riemannXi s).re := by
    rw [Complex.inner, Complex.sq_norm, Complex.div_re]
    simp only [mul_re, conj_re, conj_im]
    ring
  have hfun : xiLogNormSqHorizontal t =
      fun y : ℝ => (1 / 2 : ℝ) *
        Real.log (‖ZD.riemannXi ((y : ℂ) + Complex.I * (t : ℂ))‖ ^ 2) := by
    funext y
    simp only [xiLogNormSqHorizontal]
    ring
  rw [hfun]
  apply hhalf.congr_deriv
  simpa only [s, one_div, logDeriv_apply] using hquotient

end CriticalLinePhasor.DVP

#print axioms CriticalLinePhasor.DVP.hasDerivAt_xiLogNormSqHorizontal
