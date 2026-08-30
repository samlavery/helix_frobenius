import RequestProject.XiStructureFunction

/-!
# C3 batch 4 — attack A3.  THE CHART MAP, written out before it is used

**Geometric correction carried in (Sam, this session).**  Two things were being said
loosely in the batch-3 register and both are corrected here, by compiling the map rather
than asserting it.

1. **The native helix domain is `Re s > 0`.**  Phasors enter the bank at `Re s = 0` at
   zero magnitude and grow continuously; there is no convergence gate on the carrier.
   `Re s > 1` is the abscissa of the *projected* Dirichlet series and is a chart
   artifact, never an obstruction (ground rule 4).

2. **`|Re z| ≤ 634` is an ORDINATE BAND, not a strip.**  `XiStructureFunction` defines
   `E(z) = ξ(½ − iz) + ξ′(½ − iz)`, i.e. the chart is

   ```
   s = ½ − i·z        z = i·(s − ½)
   Re z = −Im s       (the ORDINATE / height t)
   Im z = Re s − ½    (the DEPTH off the critical line)
   ```

   so `|Re z| ≤ 634` is `|Im s| ≤ 634`: a band of heights `|t| ≤ 634`, which is exactly
   what a Hardy-ladder threshold controls.  It says nothing about `Re s`.  Calling it a
   "low strip" invites reading it as a strip in the native `s`-plane, which it is not —
   raising the ladder moves the height threshold and never the depth.

3. **`E` and `E*` are the conjugate double-helix / anti-helix pair.**  `E*(z) =
   conj(E(conj z))`, and in the chart `conj z` is exactly the functional-equation
   reflection `s ↦ 1 − s̄` (`conj_chart_is_fe_reflect`).  So the domination
   `‖E* z‖ ≤ ‖E z‖` on `Im z > 0` says: on the side `Re s > ½`, the helix dominates its
   anti-helix, the reading at the mirror point across the critical line.

Everything below is compiled; nothing here is an assertion about the map.
-/

open Complex

noncomputable section

namespace CriticalLinePhasor.C3B4Chart

/-- The chart: `z = i(s − ½)`. -/
def zOfS (s : ℂ) : ℂ := Complex.I * (s - 1 / 2)

/-- The inverse chart: `s = ½ − i z`, which is the argument `XiStructureFunction` uses. -/
def sOfZ (z : ℂ) : ℂ := 1 / 2 - Complex.I * z

theorem sOfZ_zOfS (s : ℂ) : sOfZ (zOfS s) = s := by
  have h : Complex.I * (Complex.I * (s - 1 / 2)) = -(s - 1 / 2) := by
    rw [← mul_assoc, Complex.I_mul_I]; ring
  simp only [sOfZ, zOfS, h]
  ring

theorem zOfS_sOfZ (z : ℂ) : zOfS (sOfZ z) = z := by
  have h : Complex.I * (Complex.I * z) = -z := by
    rw [← mul_assoc, Complex.I_mul_I]; ring
  simp only [sOfZ, zOfS]
  rw [show (1 : ℂ) / 2 - Complex.I * z - 1 / 2 = -(Complex.I * z) by ring]
  rw [mul_neg, h, neg_neg]

/-- **`Re z` is MINUS THE ORDINATE.**  `Re z = −Im s`. -/
theorem zOfS_re (s : ℂ) : (zOfS s).re = -s.im := by
  simp [zOfS, Complex.mul_re]

/-- **`Im z` is THE DEPTH.**  `Im z = Re s − ½`. -/
theorem zOfS_im (s : ℂ) : (zOfS s).im = s.re - 1 / 2 := by
  simp [zOfS, Complex.mul_im]

/-- **THE BAND CORRECTION.**  `|Re z| ≤ R` is a band of ORDINATES `|Im s| ≤ R`.  It
constrains the height only, and places no condition whatsoever on `Re s`. -/
theorem band_is_ordinate (s : ℂ) (R : ℝ) : |(zOfS s).re| ≤ R ↔ |s.im| ≤ R := by
  rw [zOfS_re, abs_neg]

/-- The upper half plane of the chart is the half plane to the RIGHT of the critical
line: `0 < Im z ↔ ½ < Re s`. -/
theorem upper_half_iff_right_of_critical (s : ℂ) : 0 < (zOfS s).im ↔ 1 / 2 < s.re := by
  rw [zOfS_im]; constructor <;> intro h <;> linarith

/-- **THE NATIVE HELIX DOMAIN.**  `Re s > 0` — where the phasors enter the bank — is the
chart half plane `Im z > −½`.  The domination criterion lives on `Im z > 0`, which is
the RIGHT HALF of the native domain, not all of it. -/
theorem native_domain_iff (s : ℂ) : 0 < s.re ↔ -(1 / 2) < (zOfS s).im := by
  rw [zOfS_im]; constructor <;> intro h <;> linarith

/-- The entry wall of the bank, `Re s = 0`, is the chart line `Im z = −½`. -/
theorem entry_wall_iff (s : ℂ) : s.re = 0 ↔ (zOfS s).im = -(1 / 2) := by
  rw [zOfS_im]; constructor <;> intro h <;> linarith

/-- **THE ANTI-HELIX.**  Chart conjugation is the functional-equation reflection
`s ↦ 1 − s̄`.  This is why `E*` is the anti-helix partner of `E`: it is the reading of
the same structure function at the mirror point across the critical line. -/
theorem conj_chart_is_fe_reflect (s : ℂ) :
    sOfZ ((starRingEnd ℂ) (zOfS s)) = 1 - (starRingEnd ℂ) s := by
  apply Complex.ext <;>
    simp [sOfZ, zOfS, Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im] <;>
    ring

/-- The reflection is an involution, as an anti-helix pair must be. -/
theorem fe_reflect_involutive (s : ℂ) :
    (1 : ℂ) - (starRingEnd ℂ) ((1 : ℂ) - (starRingEnd ℂ) s) = s := by
  apply Complex.ext <;> simp

/-- The critical line `Re s = ½` is exactly the fixed set of the reflection, i.e. the
chart's real axis `Im z = 0`. -/
theorem critical_line_iff (s : ℂ) : s.re = 1 / 2 ↔ (zOfS s).im = 0 := by
  rw [zOfS_im]; constructor <;> intro h <;> linarith

/-- The structure function is literally read at `sOfZ`. -/
theorem xiStructure_at (z : ℂ) :
    XiStructure.xiStructure z
      = ZD.riemannXi (sOfZ z) + deriv ZD.riemannXi (sOfZ z) := rfl

end CriticalLinePhasor.C3B4Chart

section AxiomAudit
#print axioms CriticalLinePhasor.C3B4Chart.sOfZ_zOfS
#print axioms CriticalLinePhasor.C3B4Chart.zOfS_sOfZ
#print axioms CriticalLinePhasor.C3B4Chart.zOfS_re
#print axioms CriticalLinePhasor.C3B4Chart.zOfS_im
#print axioms CriticalLinePhasor.C3B4Chart.band_is_ordinate
#print axioms CriticalLinePhasor.C3B4Chart.upper_half_iff_right_of_critical
#print axioms CriticalLinePhasor.C3B4Chart.native_domain_iff
#print axioms CriticalLinePhasor.C3B4Chart.entry_wall_iff
#print axioms CriticalLinePhasor.C3B4Chart.conj_chart_is_fe_reflect
#print axioms CriticalLinePhasor.C3B4Chart.critical_line_iff
#print axioms CriticalLinePhasor.C3B4Chart.xiStructure_at
end AxiomAudit
