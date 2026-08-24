import Mathlib.Analysis.InnerProductSpace.Harmonic.Constructions
import RequestProject.DVPSeatRealPart

open Complex ComplexConjugate InnerProductSpace

noncomputable section

namespace CriticalLinePhasor.DVP

/-- The real part of the xi logarithmic derivative is harmonic at every
point where xi does not vanish. -/
theorem xi_logDeriv_re_harmonicAt {s : ℂ} (hxi : ZD.riemannXi s ≠ 0) :
    HarmonicAt (fun z : ℂ => (logDeriv ZD.riemannXi z).re) s := by
  have han : AnalyticAt ℂ ZD.riemannXi s :=
    ZD.ZeroCount.riemannXi_analyticOnNhd_univ s (Set.mem_univ _)
  have hlog : AnalyticAt ℂ
      (fun z => deriv ZD.riemannXi z / ZD.riemannXi z) s :=
    han.deriv.div han hxi
  simpa only [logDeriv_apply] using hlog.harmonicAt_re

/-- Functional-equation antisymmetry makes the real logarithmic derivative
vanish at every nonzero point of the critical line. -/
theorem xi_logDeriv_re_eq_zero_on_line (t : ℝ)
    (hxi : ZD.riemannXi (1 / 2 + Complex.I * (t : ℂ)) ≠ 0) :
    (logDeriv ZD.riemannXi (1 / 2 + Complex.I * (t : ℂ))).re = 0 := by
  let s : ℂ := 1 / 2 + Complex.I * (t : ℂ)
  have hs : 1 - conj s = s := by
    apply Complex.ext <;> simp [s, Complex.mul_re, Complex.mul_im] <;> ring
  have href := xi_logDeriv_one_sub_conj s
  rw [hs] at href
  have hre := congrArg Complex.re href
  simp only [Complex.neg_re, Complex.conj_re] at hre
  rw [logDeriv_apply]
  change (deriv ZD.riemannXi s / ZD.riemannXi s).re = 0
  linarith

end CriticalLinePhasor.DVP

#print axioms CriticalLinePhasor.DVP.xi_logDeriv_re_harmonicAt
#print axioms CriticalLinePhasor.DVP.xi_logDeriv_re_eq_zero_on_line
