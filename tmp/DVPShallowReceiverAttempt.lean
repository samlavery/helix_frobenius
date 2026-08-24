import RequestProject.HilbertPolyaCapstone

open Complex Filter Topology

noncomputable section

namespace CriticalLinePhasor.HilbertPolya

/-- Direct receiver construction attempt. -/
theorem xiSpectralTrace_selfAdjointReceiver_attempt :
    HelixLimit.IsSelfAdjointReceiver xiSpectralTrace := by
  intro z hz
  have hxi : ZD.riemannXi (1 / 2 + Complex.I * z) ≠ 0 := by
    intro hzero
    apply hz
    exact congrArg Complex.re hzero
  have han : AnalyticAt ℂ ZD.riemannXi (1 / 2 + Complex.I * z) :=
    ZD.ZeroCount.riemannXi_analyticOnNhd_univ _ (Set.mem_univ _)
  have hcont : ContinuousAt (logDeriv ZD.riemannXi)
      (1 / 2 + Complex.I * z) :=
    han.deriv.continuousAt.div han.continuousAt hxi
  refine ⟨xiSpectralTrace z, ?_⟩
  have haff : ContinuousAt (fun w : ℂ => 1 / 2 + Complex.I * w) z := by
    fun_prop
  have htrace := (ContinuousAt.comp
    (g := logDeriv ZD.riemannXi)
    (f := fun w : ℂ => 1 / 2 + Complex.I * w)
    (x := z) hcont haff).neg
  exact htrace.tendsto.mono_left nhdsWithin_le_nhds

end CriticalLinePhasor.HilbertPolya
