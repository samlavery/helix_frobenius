import RequestProject.FiberZeroMidpointRoute
import RequestProject.DVPLadder1269o2

/-!
# The route compiled unconditionally in the certified window

For `|y| ≤ 1269/2` the station ladder `DVP.online_below_1269o2` puts every nontrivial zero on
the line, so in that window the advocate's claim — a vanishing of the three-dimensional fiber at
`(σ, y)` in the strip has `σ = ½` — is a theorem, and `OneVanishingPerHeight3D` holds there.
-/

open CriticalLinePhasor

noncomputable section

namespace CarrierReadout

/-- **In the window `|y| ≤ 1269/2` the claim is a theorem**: a vanishing of the 3-D fiber at
`(σ, y)` in the strip has `σ = ½`, unconditionally. -/
theorem midpoint_of_fiber3D_zero_below {σ y : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1)
    (hy : |y| ≤ 1269 / 2) (h : laneChart3D σ y = 0) : σ = 1 / 2 := by
  have hmem := mem_nontrivialZeros_of_fiber3D_zero hσ0 hσ1 h
  have := DVP.online_below_1269o2 _ hmem (by rw [im_add_mul_I]; exact hy)
  rw [re_add_mul_I] at this
  exact this

/-- One vanishing per height holds unconditionally in the certified window. -/
theorem oneVanishingPerHeight3D_below {y : ℝ} (hy : |y| ≤ 1269 / 2) {σ₁ σ₂ : ℝ}
    (h10 : 0 < σ₁) (h11 : σ₁ < 1) (h20 : 0 < σ₂) (h21 : σ₂ < 1)
    (hz1 : laneChart3D σ₁ y = 0) (hz2 : laneChart3D σ₂ y = 0) : σ₁ = σ₂ := by
  rw [midpoint_of_fiber3D_zero_below h10 h11 hy hz1, midpoint_of_fiber3D_zero_below h20 h21 hy hz2]

/-- The six-step composite in the window, with no hypothesis at all. -/
theorem fiber_zero_descends_to_line_below {σ y : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1)
    (hy : |y| ≤ 1269 / 2) (h : laneChart3D σ y = 0) :
    σ = 1 / 2 ∧ midpointFocalZero y ∧ riemannZeta (descend y) = 0 ∧ (descend y).re = 1 / 2 := by
  have hσ := midpoint_of_fiber3D_zero_below hσ0 hσ1 hy h
  subst hσ
  exact ⟨rfl, h, (midpoint_zero_descends y).mp h, descend_re y⟩

end CarrierReadout
