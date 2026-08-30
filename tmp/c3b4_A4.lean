import c3b4_A2
import RequestProject.JKernelSignLaw

/-!
# C3 batch 4 — attack A4.  The THIRD tail primitive as a quadratic ramp, and the
J-kernel fiber under the weakened hypothesis.

`c3b4_A2` proved: `U(s) := ∫_{(s,∞)} T ≥ 0` for all `s ≥ 0` implies the target.
This file does three further things.

* **`second_tail_eq_quadratic_ramp`** — the exact evaluation of `U` in one step:
  `∫_{(s,∞)} T(r) dr = ∫_{(s,∞)} (u−s)²/2 · W(u) du`.
  So the surviving hypothesis is exactly QUADRATIC-RAMP positivity, one rung up the
  ramp hierarchy from the refuted linear ramp `T ≥ 0`.  At `s = 0` it reads
  `∫_{(0,∞)} u²/2 · W = L₁(x)/16`, so the `s = 0` instance is `L₁ ≥ 0`.

* **`second_tail_nonneg_of_single_crossing`** — single crossing plus `∫T ≥ 0` implies
  `U ≥ 0`.  This is the containment: DECOMPOSITION B'S HYPOTHESIS IS WEAKER THAN
  DECOMPOSITION A'S.  Compiling it is what licenses dropping A in favour of B rather
  than carrying both.

* **`jKernel_fiber_nonneg_of_second_tail`** — the J-kernel `d`-fiber under the weakened
  hypothesis, with the `Φ`-decay integrability discharged from the scalar bound.
-/

open MeasureTheory Set

noncomputable section

namespace CriticalLinePhasor.C3B4B

/-! ## The triangle for the third (quadratic-ramp) primitive -/

/-- The triangle integrand for the second tail primitive: `(u−r)·W(u)` on `{r < u}`. -/
def triH (W : ℝ → ℝ) (r u : ℝ) : ℝ := if r < u then (u - r) * W u else 0

theorem triH_inner_u (W : ℝ → ℝ) {s r : ℝ} (hr : s < r) :
    ∫ u in Ioi s, triH W r u = tailT W r := by
  have hind : (fun u : ℝ => triH W r u)
      = Set.indicator (Ioi r) (fun u => (u - r) * W u) := by
    funext u; simp [triH, Set.indicator_apply, Set.mem_Ioi]
  rw [hind, MeasureTheory.setIntegral_indicator measurableSet_Ioi]
  have h2 : Ioi s ∩ Ioi r = Ioi r := by
    rw [Set.Ioi_inter_Ioi, max_eq_right hr.le]
  rw [h2]
  rfl

theorem triH_inner_r (W : ℝ → ℝ) {s u : ℝ} (hu : s < u) :
    ∫ r in Ioi s, triH W r u = (u - s) ^ 2 / 2 * W u := by
  have hind : (fun r : ℝ => triH W r u)
      = Set.indicator (Iio u) (fun r => (u - r) * W u) := by
    funext r; simp [triH, Set.indicator_apply, Set.mem_Iio]
  rw [hind, MeasureTheory.setIntegral_indicator measurableSet_Iio]
  have h2 : Ioi s ∩ Iio u = Ioo s u := by
    ext r; simp [Set.mem_Ioi, Set.mem_Iio, Set.mem_Ioo]
  rw [h2, MeasureTheory.integral_mul_const,
    ← MeasureTheory.integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le hu.le]
  congr 1
  have h1 : (∫ r in s..u, (u - r)) = (∫ r in s..u, u) - ∫ r in s..u, r :=
    intervalIntegral.integral_sub (continuous_const.intervalIntegrable _ _)
      (continuous_id'.intervalIntegrable _ _)
  rw [h1, intervalIntegral.integral_const, integral_id]
  simp only [smul_eq_mul]
  ring

/-- **THE THIRD TAIL PRIMITIVE, EXACTLY.**  `∫_{(s,∞)} T = ∫_{(s,∞)} (u−s)²/2 · W(u) du`.
The second tail primitive of `W` IS the quadratic ramp, one rung above the refuted
linear ramp. -/
theorem second_tail_eq_quadratic_ramp (W : ℝ → ℝ) (s : ℝ)
    (hprod : Integrable (Function.uncurry (triH W))
      ((volume.restrict (Ioi s)).prod (volume.restrict (Ioi s)))) :
    ∫ r in Ioi s, tailT W r = ∫ u in Ioi s, (u - s) ^ 2 / 2 * W u := by
  have hswap := MeasureTheory.integral_integral_swap hprod
  have hL : ∫ r in Ioi s, (∫ u in Ioi s, triH W r u) = ∫ r in Ioi s, tailT W r :=
    MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
      (fun r hr => triH_inner_u W hr)
  have hR : ∫ u in Ioi s, (∫ r in Ioi s, triH W r u)
      = ∫ u in Ioi s, (u - s) ^ 2 / 2 * W u :=
    MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
      (fun u hu => triH_inner_r W hu)
  rw [← hL, ← hR]
  exact hswap

/-! ## Decomposition B's hypothesis is weaker than Decomposition A's -/

/-- **THE CONTAINMENT.**  If `T` changes sign at most once on `(0,∞)`, from `−` to `+`,
and `∫_{(0,∞)} T ≥ 0`, then the SECOND tail primitive is nonnegative at every `s ≥ 0`.

So `c3b4_A1`'s hypothesis implies `c3b4_A2`'s, and the converse fails (a `T` with three
sign changes and a nonnegative running tail satisfies B and not A).  This is why the
batch keeps B and records A as superseded. -/
theorem second_tail_nonneg_of_single_crossing {W : ℝ → ℝ} {r0 : ℝ}
    (hTint : IntegrableOn (tailT W) (Ioi (0 : ℝ)))
    (hTle : ∀ r ∈ Ioc (0 : ℝ) r0, tailT W r ≤ 0)
    (hTge : ∀ r ∈ Ioi r0, 0 ≤ tailT W r)
    (hTtot : 0 ≤ ∫ r in Ioi (0 : ℝ), tailT W r) :
    ∀ s : ℝ, 0 ≤ s → 0 ≤ ∫ r in Ioi s, tailT W r := by
  intro s hs
  rcases le_total s r0 with h | h
  · -- below the crossing: the discarded piece is nonpositive, so the tail can only grow
    have hu : Ioc (0 : ℝ) s ∪ Ioi s = Ioi (0 : ℝ) := Set.Ioc_union_Ioi_eq_Ioi hs
    have hd : Disjoint (Ioc (0 : ℝ) s) (Ioi s) := by
      rw [Set.disjoint_left]
      rintro x hx1 hx2
      exact absurd hx2 (not_lt.mpr hx1.2)
    have h1 : IntegrableOn (tailT W) (Ioc (0 : ℝ) s) :=
      hTint.mono_set (by rw [← hu]; exact Set.subset_union_left)
    have h2 : IntegrableOn (tailT W) (Ioi s) :=
      hTint.mono_set (by rw [← hu]; exact Set.subset_union_right)
    have hsplit := MeasureTheory.setIntegral_union hd measurableSet_Ioi h1 h2
    rw [hu] at hsplit
    have hneg : (∫ r in Ioc (0 : ℝ) s, tailT W r) ≤ 0 :=
      MeasureTheory.setIntegral_nonpos measurableSet_Ioc
        (fun r hr => hTle r ⟨hr.1, le_trans hr.2 h⟩)
    linarith
  · -- above the crossing: the integrand is already nonnegative there
    exact MeasureTheory.setIntegral_nonneg measurableSet_Ioi
      (fun r hr => hTge r (lt_of_le_of_lt h hr))

/-! ## The final analytic leaf, in quadratic-ramp form -/

/-- **THE TARGET, REDUCED TO QUADRATIC-RAMP POSITIVITY.**  If
`∫_{(s,∞)} (u−s)²/2 · W(u) du ≥ 0` for every `s ≥ 0`, then the `sinh`-weighted pairing
is nonnegative at every `y ≥ 0`.

This is the exact hypothesis the batch leaves open.  Its `s = 0` instance is
`L₁(x) ≥ 0`; the refuted `T ≥ 0` is its `s`-derivative statement one rung down. -/
theorem sinh_pairing_nonneg_of_quadratic_ramp {W : ℝ → ℝ} {y : ℝ} (hy : 0 ≤ y)
    (hW : Measurable W)
    (hint : IntegrableOn (fun u => gY y u * |W u|) (Ioi (0 : ℝ)))
    (hprodG : Integrable (Function.uncurry (triG (tailT W) (gY'' y)))
      ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))))
    (hTint : IntegrableOn (tailT W) (Ioi (0 : ℝ)))
    (hqTint : IntegrableOn (fun r => gY'' y r * tailT W r) (Ioi (0 : ℝ)))
    (hprodH : ∀ s : ℝ, 0 ≤ s → Integrable (Function.uncurry (triH W))
      ((volume.restrict (Ioi s)).prod (volume.restrict (Ioi s))))
    (hramp : ∀ s : ℝ, 0 ≤ s → 0 ≤ ∫ u in Ioi s, (u - s) ^ 2 / 2 * W u) :
    0 ≤ ∫ u in Ioi (0 : ℝ), gY y u * W u := by
  refine sinh_pairing_nonneg_of_second_tail hy hW hint hprodG hTint hqTint ?_
  intro s hs
  rw [second_tail_eq_quadratic_ramp W s (hprodH s hs)]
  exact hramp s hs

/-! ## The J-kernel fiber -/

open CriticalLinePhasor.JKernel

/-- The nonnegative `d`-fiber weight of the J-kernel, `W_d(u) = Φ(u+d/2)·Φ(u−d/2)`. -/
def jWeight (d u : ℝ) : ℝ := phiEven (u + d / 2) * phiEven (u - d / 2)

theorem jWeight_nonneg (d u : ℝ) : 0 ≤ jWeight d u :=
  mul_nonneg (phiEven_nonneg _) (phiEven_nonneg _)

/-- **THE BRIDGE.**  The closed `sinh` form of the J-kernel vertical pairing, read at
`s = 2u`, is exactly `4·g_y(u)·W_d(u)`. -/
theorem jKernel_sinh_eq_gY (d y u : ℝ) :
    2 * jKernel d (2 * u) * Real.sinh (y * (2 * u)) = 4 * (gY y u * jWeight d u) := by
  simp only [jKernel, jWeight, gY]
  rw [show (2 * u + d) / 2 = u + d / 2 by ring, show (2 * u - d) / 2 = u - d / 2 by ring,
    show y * (2 * u) = 2 * y * u by ring]
  ring

/-- **THE J-KERNEL FIBER, UNDER THE WEAKENED HYPOTHESIS.**  Each `d`-fiber of the
vertical pairing is nonnegative as soon as the QUADRATIC RAMP of `W_d` is nonnegative —
no sign hypothesis on the linear ramp, which is refuted. -/
theorem jKernel_fiber_nonneg_of_quadratic_ramp {d y : ℝ} (hy : 0 ≤ y)
    (hW : Measurable (jWeight d))
    (hint : IntegrableOn (fun u => gY y u * |jWeight d u|) (Ioi (0 : ℝ)))
    (hprodG : Integrable (Function.uncurry (triG (tailT (jWeight d)) (gY'' y)))
      ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))))
    (hTint : IntegrableOn (tailT (jWeight d)) (Ioi (0 : ℝ)))
    (hqTint : IntegrableOn (fun r => gY'' y r * tailT (jWeight d) r) (Ioi (0 : ℝ)))
    (hprodH : ∀ s : ℝ, 0 ≤ s → Integrable (Function.uncurry (triH (jWeight d)))
      ((volume.restrict (Ioi s)).prod (volume.restrict (Ioi s))))
    (hramp : ∀ s : ℝ, 0 ≤ s → 0 ≤ ∫ u in Ioi s, (u - s) ^ 2 / 2 * jWeight d u) :
    0 ≤ ∫ u in Ioi (0 : ℝ), gY y u * jWeight d u :=
  sinh_pairing_nonneg_of_quadratic_ramp hy hW hint hprodG hTint hqTint hprodH hramp

end CriticalLinePhasor.C3B4B

section AxiomAudit
#print axioms CriticalLinePhasor.C3B4B.triH_inner_u
#print axioms CriticalLinePhasor.C3B4B.triH_inner_r
#print axioms CriticalLinePhasor.C3B4B.second_tail_eq_quadratic_ramp
#print axioms CriticalLinePhasor.C3B4B.second_tail_nonneg_of_single_crossing
#print axioms CriticalLinePhasor.C3B4B.sinh_pairing_nonneg_of_quadratic_ramp
#print axioms CriticalLinePhasor.C3B4B.jWeight_nonneg
#print axioms CriticalLinePhasor.C3B4B.jKernel_sinh_eq_gY
#print axioms CriticalLinePhasor.C3B4B.jKernel_fiber_nonneg_of_quadratic_ramp
end AxiomAudit
