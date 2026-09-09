import RequestProject.UnitaryClockToeplitz
import RequestProject.XiProductMultPartialFraction
import RequestProject.XiHadamardFactorization
import RequestProject.SeatingFloorOdd

/-!
# The Herglotz sweep: the transported measure's Herglotz function is `ξ′/ξ` at a moved anchor
(ledger 626)

At an anchor `s` off the line, `c = 1 − s̄`, `d = s − c = 2σ − 1`, the transported measure of the
nontrivial zeros is `μ_s = Σ_ρ m_ρ ω_ρ δ_{w_ρ}` with `ω_ρ = 1/((s−ρ)(ρ−c))`, `w_ρ = (ρ−c)/(s−ρ)`
(`transport`, ledger 622). Its Herglotz function `Φ_s(z) = Σ_ρ m_ρ ω_ρ (1 + w_ρ z)/(1 − w_ρ z)` is, per atom,
a partial fraction in `ρ` with poles at `s`, `c` and the **moved anchor** `s_z = (s + z c)/(1 + z)`
(`atomHerglotz_eq`), so summing over the zeros with the compiled Hadamard partial fractions gives

  `Φ_s(z) = (1/d) [ −L(s) − L(c) + 2 L(s_z) ] = (2/d) [ L(s_z) − i Im L(s) ]`,   `L = ξ′/ξ`

(`xiHerglotz_eq`, `xiHerglotz_eq'`), and `Re Φ_s(z) = 2 Re L(s_z)/(2σ − 1)` (`xiHerglotz_re`): the real
part of the Herglotz function at `z` is the seat mass at the moved anchor. The map `z ↦ s_z` sends the
unit disc onto the channel `Re < ½` and the unit circle onto the critical line
(`movedAnchor_re_lt_half_iff`), so the whole degree ladder at one anchor is the seat-mass sign condition
swept over the channel.
-/

open Complex Finset

namespace CriticalLinePhasor.SeatingLedger

/-- The moved anchor `s_z = (s + z c)/(1 + z)`, `c = 1 − s̄`. -/
noncomputable def movedAnchor (s z : ℂ) : ℂ := (s + z * (1 - (starRingEnd ℂ) s)) / (1 + z)

/-- The transported atom's weight `ω_ρ = 1/((s−ρ)(ρ−c))`. -/
noncomputable def atomWeight (s ρ : ℂ) : ℂ := ((s - ρ) * (ρ - (1 - (starRingEnd ℂ) s)))⁻¹

/-- The Herglotz kernel of the transported atom, `ω_ρ (1 + w_ρ z)/(1 − w_ρ z)`. -/
noncomputable def atomHerglotz (s ρ z : ℂ) : ℂ :=
  atomWeight s ρ * ((1 + transport s ρ * z) / (1 - transport s ρ * z))

theorem movedAnchor_sub (s z ρ : ℂ) (hz : 1 + z ≠ 0) :
    (s - ρ) - z * (ρ - (1 - (starRingEnd ℂ) s)) = (1 + z) * (movedAnchor s z - ρ) := by
  unfold movedAnchor
  field_simp
  ring

/-- The pure algebra of the per-atom identity. -/
theorem herglotz_atom_alg (A B z u : ℂ) (hA : A ≠ 0) (hB : B ≠ 0) (hz : 1 + z ≠ 0) (hu : u ≠ 0)
    (hd : A + B ≠ 0) (hrel : A - z * B = (1 + z) * u) :
    (A * B)⁻¹ * ((1 + B / A * z) / (1 - B / A * z))
      = (A + B)⁻¹ * (-(1 / A) + 1 / B + 2 / u) := by
  have hAzB : A - z * B ≠ 0 := by rw [hrel]; exact mul_ne_zero hz hu
  have hAzB' : A - B * z ≠ 0 := by rwa [mul_comm]
  have hu' : u = (A - z * B) / (1 + z) := by rw [hrel]; field_simp
  rw [hu']
  field_simp
  ring

/-- **Per atom**: `ω_ρ (1 + w_ρ z)/(1 − w_ρ z) = (1/d)[ −1/(s−ρ) + 1/(ρ−c) + 2/(s_z − ρ) ]`. -/
theorem atomHerglotz_eq (s ρ z : ℂ) (hA : s - ρ ≠ 0) (hB : ρ - (1 - (starRingEnd ℂ) s) ≠ 0)
    (hz : 1 + z ≠ 0) (hu : movedAnchor s z - ρ ≠ 0) (hd : s - (1 - (starRingEnd ℂ) s) ≠ 0) :
    atomHerglotz s ρ z = (s - (1 - (starRingEnd ℂ) s))⁻¹
      * (-(1 / (s - ρ)) + 1 / (ρ - (1 - (starRingEnd ℂ) s)) + 2 / (movedAnchor s z - ρ)) := by
  unfold atomHerglotz atomWeight transport
  rw [show s - (1 - (starRingEnd ℂ) s) = (s - ρ) + (ρ - (1 - (starRingEnd ℂ) s)) by ring]
  have hd' : (s - ρ) + (ρ - (1 - (starRingEnd ℂ) s)) ≠ 0 := by
    rw [show (s - ρ) + (ρ - (1 - (starRingEnd ℂ) s)) = s - (1 - (starRingEnd ℂ) s) by ring]; exact hd
  exact herglotz_atom_alg _ _ z _ hA hB hz hu hd' (movedAnchor_sub s z ρ hz)

/-- The Herglotz function of the transported measure of the nontrivial zeros. -/
noncomputable def xiHerglotz (s z : ℂ) : ℂ :=
  ∑' ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros}, (ZD.xiOrderNat ρ.val : ℂ) * atomHerglotz s ρ.val z

theorem sub_ne_zero_of_notMem {x ρ : ℂ} (hx : x ∉ ZD.NontrivialZeros) (hρ : ρ ∈ ZD.NontrivialZeros) :
    x - ρ ≠ 0 := by
  intro h
  apply hx
  rw [sub_eq_zero.mp h]
  exact hρ

/-- **The sweep identity**: `Φ_s(z) = (1/d)[ −L(s) − L(c) + 2 L(s_z) ]`, `L = ξ′/ξ`. -/
theorem xiHerglotz_eq {s z : ℂ} (hs : s ∉ ZD.NontrivialZeros)
    (hc : 1 - (starRingEnd ℂ) s ∉ ZD.NontrivialZeros) (hz : 1 + z ≠ 0)
    (hsz : movedAnchor s z ∉ ZD.NontrivialZeros) (hd : s.re ≠ 1 / 2) :
    xiHerglotz s z = (s - (1 - (starRingEnd ℂ) s))⁻¹
      * (-logDeriv ZD.riemannXi s - logDeriv ZD.riemannXi (1 - (starRingEnd ℂ) s)
          + 2 * logDeriv ZD.riemannXi (movedAnchor s z)) := by
  obtain ⟨A, hA⟩ := ZD.xi_logDeriv_sub_product_const_off_zeros
  have hd' : s - (1 - (starRingEnd ℂ) s) ≠ 0 := by
    rw [mirror_d]
    have : (2 * s.re - 1 : ℝ) ≠ 0 := by intro h; apply hd; linarith
    exact_mod_cast this
  have hterm : ∀ ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros},
      (ZD.xiOrderNat ρ.val : ℂ) * atomHerglotz s ρ.val z
        = (s - (1 - (starRingEnd ℂ) s))⁻¹
          * (-((ZD.xiOrderNat ρ.val : ℂ) * (1 / (s - ρ.val) + 1 / ρ.val))
             - ((ZD.xiOrderNat ρ.val : ℂ) * (1 / ((1 - (starRingEnd ℂ) s) - ρ.val) + 1 / ρ.val))
             + 2 * ((ZD.xiOrderNat ρ.val : ℂ) * (1 / (movedAnchor s z - ρ.val) + 1 / ρ.val))) := by
    intro ρ
    have hA' : s - ρ.val ≠ 0 := sub_ne_zero_of_notMem hs ρ.property
    have hB : ρ.val - (1 - (starRingEnd ℂ) s) ≠ 0 := by
      have := sub_ne_zero_of_notMem hc ρ.property
      intro h; apply this; linear_combination -h
    have hu : movedAnchor s z - ρ.val ≠ 0 := sub_ne_zero_of_notMem hsz ρ.property
    rw [atomHerglotz_eq s ρ.val z hA' hB hz hu hd']
    have hneg : (1 : ℂ) / (ρ.val - (1 - (starRingEnd ℂ) s))
        = -((1 : ℂ) / ((1 - (starRingEnd ℂ) s) - ρ.val)) := by
      rw [← neg_sub (1 - (starRingEnd ℂ) s) ρ.val, div_neg]
    rw [hneg]
    ring
  unfold xiHerglotz
  simp_rw [hterm]
  have h1 := (ZD.summable_weighted_partial_fraction hs).hasSum
  have h2 := (ZD.summable_weighted_partial_fraction hc).hasSum
  have h3 := (ZD.summable_weighted_partial_fraction hsz).hasSum
  rw [tsum_mul_left, ((h1.neg.sub h2).add (h3.mul_left 2)).tsum_eq,
    ← ZD.logDeriv_xiProductMult_partial_fraction hs, ← ZD.logDeriv_xiProductMult_partial_fraction hc,
    ← ZD.logDeriv_xiProductMult_partial_fraction hsz]
  have e1 := hA s hs
  have e2 := hA _ hc
  have e3 := hA _ hsz
  rw [← logDeriv_apply] at e1 e2 e3
  rw [show logDeriv ZD.xiProductMult s = logDeriv ZD.riemannXi s - A by linear_combination -e1,
    show logDeriv ZD.xiProductMult (1 - (starRingEnd ℂ) s)
      = logDeriv ZD.riemannXi (1 - (starRingEnd ℂ) s) - A by linear_combination -e2,
    show logDeriv ZD.xiProductMult (movedAnchor s z) = logDeriv ZD.riemannXi (movedAnchor s z) - A by
      linear_combination -e3]
  ring

/-- `L(c) = −conj L(s)` (functional equation and reality). -/
theorem xiLogDeriv_mirror (s : ℂ) :
    logDeriv ZD.riemannXi (1 - (starRingEnd ℂ) s) = -(starRingEnd ℂ) (logDeriv ZD.riemannXi s) := by
  rw [xiLogDeriv_odd, xiLogDeriv_conj]

/-- **The sweep identity, second form**: `Φ_s(z) = (2/d)[ L(s_z) − i Im L(s) ]`. -/
theorem xiHerglotz_eq' {s z : ℂ} (hs : s ∉ ZD.NontrivialZeros)
    (hc : 1 - (starRingEnd ℂ) s ∉ ZD.NontrivialZeros) (hz : 1 + z ≠ 0)
    (hsz : movedAnchor s z ∉ ZD.NontrivialZeros) (hd : s.re ≠ 1 / 2) :
    xiHerglotz s z = 2 / ((2 * s.re - 1 : ℝ) : ℂ)
      * (logDeriv ZD.riemannXi (movedAnchor s z) - I * ((logDeriv ZD.riemannXi s).im : ℂ)) := by
  rw [xiHerglotz_eq hs hc hz hsz hd, xiLogDeriv_mirror, mirror_d]
  have hsub := Complex.sub_conj (logDeriv ZD.riemannXi s)
  push_cast at hsub
  rw [show -logDeriv ZD.riemannXi s - -(starRingEnd ℂ) (logDeriv ZD.riemannXi s)
      + 2 * logDeriv ZD.riemannXi (movedAnchor s z)
      = 2 * (logDeriv ZD.riemannXi (movedAnchor s z) - I * ((logDeriv ZD.riemannXi s).im : ℂ)) by
    linear_combination (-1 : ℂ) * hsub]
  ring

/-- **The real part of the Herglotz function is the seat mass at the moved anchor, scaled by the depth
ratio**: `Re Φ_s(z) = 2 Re L(s_z)/(2σ_s − 1) = ((2 Re s_z − 1)/(2σ_s − 1)) · seatMass(s_z)`, and the depth
ratio is `(1 − |z|²)/|1 + z|²` (`movedAnchor_re`), positive on the disc; the exact scaled form is
`xiHerglotz_re_eq_scaled_seatMass` in `SeatHerglotzSweep.lean`. -/
theorem xiHerglotz_re {s z : ℂ} (hs : s ∉ ZD.NontrivialZeros)
    (hc : 1 - (starRingEnd ℂ) s ∉ ZD.NontrivialZeros) (hz : 1 + z ≠ 0)
    (hsz : movedAnchor s z ∉ ZD.NontrivialZeros) (hd : s.re ≠ 1 / 2) :
    (xiHerglotz s z).re = 2 * (logDeriv ZD.riemannXi (movedAnchor s z)).re / (2 * s.re - 1) := by
  rw [xiHerglotz_eq' hs hc hz hsz hd]
  have hd' : (2 * s.re - 1 : ℝ) ≠ 0 := by intro h; apply hd; linarith
  rw [show (2 : ℂ) / ((2 * s.re - 1 : ℝ) : ℂ) = ((2 / (2 * s.re - 1) : ℝ) : ℂ) by push_cast; ring,
    Complex.re_ofReal_mul, Complex.sub_re, Complex.mul_re, Complex.I_re, Complex.I_im,
    Complex.ofReal_re, Complex.ofReal_im]
  ring

/-- **The moved anchor lies in the channel iff `z` lies in the open unit disc** (for `Re s < ½`);
the unit circle is sent to the critical line. -/
theorem movedAnchor_re (s z : ℂ) (hz : 1 + z ≠ 0) :
    (movedAnchor s z).re = 1 / 2 + (s.re - 1 / 2) * (1 - Complex.normSq z) / Complex.normSq (1 + z) := by
  unfold movedAnchor
  have hn : Complex.normSq (1 + z) ≠ 0 := by rwa [Ne, Complex.normSq_eq_zero]
  rw [Complex.div_re, ← add_div, div_eq_iff hn, add_mul, div_mul_cancel₀ _ hn]
  simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.sub_re,
    Complex.sub_im, Complex.one_re, Complex.one_im, Complex.conj_re, Complex.conj_im,
    Complex.normSq_apply]
  ring

theorem movedAnchor_re_lt_half_iff {s z : ℂ} (hs : s.re < 1 / 2) (hz : 1 + z ≠ 0) :
    (movedAnchor s z).re < 1 / 2 ↔ Complex.normSq z < 1 := by
  rw [movedAnchor_re s z hz]
  have hn : 0 < Complex.normSq (1 + z) := by
    rw [Complex.normSq_pos]; exact hz
  have hneg : s.re - 1 / 2 < 0 := by linarith
  constructor
  · intro h
    by_contra hge
    have hge' : 1 ≤ Complex.normSq z := not_lt.mp hge
    have : 0 ≤ (s.re - 1 / 2) * (1 - Complex.normSq z) / Complex.normSq (1 + z) :=
      div_nonneg (mul_nonneg_of_nonpos_of_nonpos hneg.le (by linarith)) hn.le
    linarith
  · intro h
    have : (s.re - 1 / 2) * (1 - Complex.normSq z) / Complex.normSq (1 + z) < 0 :=
      div_neg_of_neg_of_pos (mul_neg_of_neg_of_pos hneg (by linarith)) hn
    linarith

end CriticalLinePhasor.SeatingLedger

#print axioms CriticalLinePhasor.SeatingLedger.atomHerglotz_eq
#print axioms CriticalLinePhasor.SeatingLedger.xiHerglotz_eq
#print axioms CriticalLinePhasor.SeatingLedger.xiHerglotz_re
#print axioms CriticalLinePhasor.SeatingLedger.movedAnchor_re_lt_half_iff
