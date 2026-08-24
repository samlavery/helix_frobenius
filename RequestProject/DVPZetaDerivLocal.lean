import RequestProject.DVPZetaLocalBound
import RequestProject.DVPZetaDerivBound

/-!
# The local ζ′ bound at heights 40–60: `‖ζ′‖ ≤ 140`

Radius-¼ Cauchy over the local instrument `zeta_local_bound` (`‖ζ‖ ≤ 35`
on `σ ≥ 1/4`, `40 ≤ |Im s| ≤ 60`): on `σ ≥ 1/2`,
`40.25 ≤ |Im s| ≤ 59.75`, `‖ζ′(s)‖ ≤ 140`.  This is the between-station
Lipschitz constant for the `t = 58` Backlund segment — 30× sharper than
the global `200·|t|^{3/4} ≈ 4211`, cutting the station count for the
`Re ζ > 0` sweep from ~7000 to ~235.  No upper bound on `σ`: the σ ≥ 2
sliver of the sphere is already inside `zeta_local_bound`.
-/

open Complex Metric

noncomputable section

namespace CriticalLinePhasor.DVP

/-- **The local ζ′ bound.**  Radius-¼ Cauchy over `zeta_local_bound`. -/
theorem zeta_deriv_local_bound {s : ℂ} (hσl : (1:ℝ)/2 ≤ s.re)
    (himl : (40.25:ℝ) ≤ |s.im|) (himu : |s.im| ≤ 59.75) :
    ‖deriv riemannZeta s‖ ≤ 140 := by
  -- ζ is differentiable on the closed ball (1 is far away: heights ≥ 40)
  have hball_ne_one : ∀ z ∈ closedBall s (1/4), z ≠ 1 := by
    intro z hz h1
    rw [mem_closedBall, dist_eq_norm] at hz
    have him' : |z.im - s.im| ≤ 1/4 := by
      calc |z.im - s.im| = |(z - s).im| := by rw [Complex.sub_im]
        _ ≤ ‖z - s‖ := Complex.abs_im_le_norm _
        _ ≤ 1/4 := hz
    rw [h1] at him'
    simp only [Complex.one_im, zero_sub, abs_neg] at him'
    linarith
  have hd : DiffContOnCl ℂ riemannZeta (ball s (1/4)) := by
    apply DifferentiableOn.diffContOnCl
    intro z hz
    have hz' : z ∈ closedBall s (1/4) := by
      rwa [closure_ball s (by norm_num : (1/4 : ℝ) ≠ 0)] at hz
    exact (differentiableAt_riemannZeta
      (hball_ne_one z hz')).differentiableWithinAt
  -- the sphere bound: every sphere point sits inside the local box
  have hC : ∀ z ∈ sphere s (1/4), ‖riemannZeta z‖ ≤ 35 := by
    intro z hz
    rw [mem_sphere_iff_norm] at hz
    have hre' : |z.re - s.re| ≤ 1/4 := by
      calc |z.re - s.re| = |(z - s).re| := by rw [Complex.sub_re]
        _ ≤ ‖z - s‖ := Complex.abs_re_le_norm _
        _ ≤ 1/4 := le_of_eq hz
    have him' : |z.im - s.im| ≤ 1/4 := by
      calc |z.im - s.im| = |(z - s).im| := by rw [Complex.sub_im]
        _ ≤ ‖z - s‖ := Complex.abs_im_le_norm _
        _ ≤ 1/4 := le_of_eq hz
    have hzre : (1:ℝ)/4 ≤ z.re := by
      rcases abs_le.mp hre' with ⟨h1, _⟩
      linarith
    have hzim_l : (40:ℝ) ≤ |z.im| := by
      have h1 : |s.im| - |z.im| ≤ |s.im - z.im| := abs_sub_abs_le_abs_sub _ _
      have h2 : |s.im - z.im| = |z.im - s.im| := abs_sub_comm _ _
      linarith
    have hzim_u : |z.im| ≤ 60 := by
      have h1 : |z.im| - |s.im| ≤ |z.im - s.im| := abs_sub_abs_le_abs_sub _ _
      linarith
    exact zeta_local_bound hzre hzim_l hzim_u
  -- Cauchy
  have hmain := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le
    (by norm_num : (0:ℝ) < 1/4) hd hC
  calc ‖deriv riemannZeta s‖ ≤ 35 / (1/4) := hmain
    _ = 140 := by norm_num

end CriticalLinePhasor.DVP

section AxiomAudit
#print axioms CriticalLinePhasor.DVP.zeta_deriv_local_bound
end AxiomAudit
