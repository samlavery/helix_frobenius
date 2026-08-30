import RequestProject.XiStructureFunction

/-!
# The Xi chart of the native double helix

The native variable is `s`.  The Xi structure function uses the rotated chart

`z = i (s - 1/2)`, equivalently `s = 1/2 - i z`.

Thus `Re z = -Im s` is the ordinate and `Im z = Re s - 1/2` is depth from the
critical line.  The native helix domain `Re s > 0` begins at the entry wall `Re s = 0`;
it is not a convergence strip.  Conjugation in the Xi chart transports to the
functional-equation reflection `s ↦ 1 - conj s`, giving the double helix/anti-helix pair.

This local rotation is distinct from the carrier-scale registration chart.  There the
physical height is `Z`, the analytic ordinate is `t = log Z`, and the `S(t)` ledger is
the difference between the native harmonized `π/3` readout and the unit-`1` receiver.
-/

open Complex

noncomputable section

namespace CriticalLinePhasor.XiHelixChart

/-- The Xi chart: `z = i(s - 1/2)`. -/
def zOfS (s : ℂ) : ℂ := Complex.I * (s - 1 / 2)

/-- The inverse Xi chart: `s = 1/2 - i z`. -/
def sOfZ (z : ℂ) : ℂ := 1 / 2 - Complex.I * z

theorem sOfZ_zOfS (s : ℂ) : sOfZ (zOfS s) = s := by
  have h : Complex.I * (Complex.I * (s - 1 / 2)) = -(s - 1 / 2) := by
    rw [← mul_assoc, Complex.I_mul_I]
    ring
  simp only [sOfZ, zOfS, h]
  ring

theorem zOfS_sOfZ (z : ℂ) : zOfS (sOfZ z) = z := by
  have h : Complex.I * (Complex.I * z) = -z := by
    rw [← mul_assoc, Complex.I_mul_I]
    ring
  simp only [sOfZ, zOfS]
  rw [show (1 : ℂ) / 2 - Complex.I * z - 1 / 2 = -(Complex.I * z) by ring]
  rw [mul_neg, h, neg_neg]

/-- `Re z` is minus the native ordinate. -/
theorem zOfS_re (s : ℂ) : (zOfS s).re = -s.im := by
  simp [zOfS, Complex.mul_re]

/-- `Im z` is depth from the critical line. -/
theorem zOfS_im (s : ℂ) : (zOfS s).im = s.re - 1 / 2 := by
  simp [zOfS, Complex.mul_im]

/-- A bound on `|Re z|` is an ordinate band in the native plane. -/
theorem band_is_ordinate (s : ℂ) (R : ℝ) : |(zOfS s).re| ≤ R ↔ |s.im| ≤ R := by
  rw [zOfS_re, abs_neg]

/-- The Xi upper half-plane is the portion of the native domain right of the critical line. -/
theorem upper_half_iff_right_of_critical (s : ℂ) :
    0 < (zOfS s).im ↔ 1 / 2 < s.re := by
  rw [zOfS_im]
  constructor <;> intro h <;> linarith

/-- The native helix domain `Re s > 0` becomes `Im z > -1/2`. -/
theorem native_domain_iff (s : ℂ) : 0 < s.re ↔ -(1 / 2) < (zOfS s).im := by
  rw [zOfS_im]
  constructor <;> intro h <;> linarith

/-- Phasors enter at `Re s = 0`, the Xi-chart wall `Im z = -1/2`. -/
theorem entry_wall_iff (s : ℂ) : s.re = 0 ↔ (zOfS s).im = -(1 / 2) := by
  rw [zOfS_im]
  constructor <;> intro h <;> linarith

/-- Xi-chart conjugation is functional-equation reflection in the native plane. -/
theorem conj_chart_is_fe_reflect (s : ℂ) :
    sOfZ ((starRingEnd ℂ) (zOfS s)) = 1 - (starRingEnd ℂ) s := by
  apply Complex.ext <;>
    simp [sOfZ, zOfS, Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im] <;>
    ring

theorem fe_reflect_involutive (s : ℂ) :
    (1 : ℂ) - (starRingEnd ℂ) ((1 : ℂ) - (starRingEnd ℂ) s) = s := by
  apply Complex.ext <;> simp

/-- The critical line is the real axis of the Xi chart. -/
theorem critical_line_iff (s : ℂ) : s.re = 1 / 2 ↔ (zOfS s).im = 0 := by
  rw [zOfS_im]
  constructor <;> intro h <;> linarith

/-- The structure function is literally evaluated in the inverse Xi chart. -/
theorem xiStructure_at (z : ℂ) :
    XiStructure.xiStructure z
      = ZD.riemannXi (sOfZ z) + deriv ZD.riemannXi (sOfZ z) := rfl

end CriticalLinePhasor.XiHelixChart

section AxiomAudit
#print axioms CriticalLinePhasor.XiHelixChart.sOfZ_zOfS
#print axioms CriticalLinePhasor.XiHelixChart.zOfS_sOfZ
#print axioms CriticalLinePhasor.XiHelixChart.zOfS_re
#print axioms CriticalLinePhasor.XiHelixChart.zOfS_im
#print axioms CriticalLinePhasor.XiHelixChart.band_is_ordinate
#print axioms CriticalLinePhasor.XiHelixChart.upper_half_iff_right_of_critical
#print axioms CriticalLinePhasor.XiHelixChart.native_domain_iff
#print axioms CriticalLinePhasor.XiHelixChart.entry_wall_iff
#print axioms CriticalLinePhasor.XiHelixChart.conj_chart_is_fe_reflect
#print axioms CriticalLinePhasor.XiHelixChart.fe_reflect_involutive
#print axioms CriticalLinePhasor.XiHelixChart.critical_line_iff
#print axioms CriticalLinePhasor.XiHelixChart.xiStructure_at
end AxiomAudit
