import RequestProject.StExplicitBridge

/-!
# The Hilbert–Pólya resolvent trace identity

The trace formula at the resolvent level, unconditional and exact.  In the
spectral coordinate `t(ρ) = −i(ρ − ½)` — the carrier's eigenheight reading of
a zero — the multiplicity ledger's two-point resolvent sum *is* the completed
logarithmic derivative:

`Tr[(D − w)⁻¹ − (D − w₀)⁻¹]
  = −i·(ξ'/ξ(½ + iw) − ξ'/ξ(½ + iw₀))`,

the left side the absolutely convergent sum `Σ' m_ρ((t_ρ−w)⁻¹ − (t_ρ−w₀)⁻¹)`
over the actual zero multiset — wherever the zeros are — and the right side
an explicit arithmetic function.  Two-point differencing kills the Hadamard
constant and the `1/ρ` normalizers exactly, so no regularization convention
survives into the statement.

Derived from the compiled unconditional Hadamard partial fraction
(`ZD.xi_logDeriv_partial_fraction`) and the compiled counting majorant
(`ZD.summable_xiOrderNat_div_norm_sq_nontrivialZeros`).  The `HasSum` form is
the operator reading: the net of finite-rank diagonal truncations converges
unconditionally to the arithmetic value.  Consumers: the receiver
architecture of `HelixResolventCapture` (trace-identity hooks), the windowed
spectral-trace cluster (`ResidueJump`, `DifferencedResolvent`).  Reality of
the spectrum `{t_ρ}` is the house dichotomy (`SourceHolonomy`), untouched
here.  No `axiom`, no `sorry`.
-/

open Complex

namespace CriticalLinePhasor.HilbertPolya

open CriticalLinePhasor.StBridge

/-- Membership in the nontrivial-zero set forces a nonzero point. -/
theorem ne_zero_of_mem_nontrivialZeros {ρ : ℂ}
    (hρ : ρ ∈ ZD.NontrivialZeros) : ρ ≠ 0 := by
  intro h
  have h1 := hρ.1
  rw [h] at h1
  simp at h1

/-- Off the zero set, the difference to any zero is nonzero. -/
theorem sub_ne_zero_of_not_mem {s ρ : ℂ}
    (hs : s ∉ ZD.NontrivialZeros) (hρ : ρ ∈ ZD.NontrivialZeros) :
    s - ρ ≠ 0 := by
  intro h
  exact hs ((sub_eq_zero.mp h) ▸ hρ)

/-- **Summability of the Hadamard terms** at any point off the zero set,
from the compiled counting majorant. -/
theorem summable_hadamard_term {s : ℂ} (hs : s ∉ ZD.NontrivialZeros) :
    Summable (fun ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros} =>
      (ZD.xiOrderNat ρ.val : ℂ) * (1 / (s - ρ.val) + 1 / ρ.val)) := by
  have hg : Summable (fun ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros} =>
      (2 * ‖s‖) * ((ZD.xiOrderNat ρ.val : ℝ) / ‖ρ.val‖ ^ 2)) :=
    (ZD.summable_xiOrderNat_div_norm_sq_nontrivialZeros).mul_left _
  apply Summable.of_norm_bounded_eventually hg
  filter_upwards [eventually_cofinite_norm_ge (2 * ‖s‖ + 2)] with ρ hbig
  have hρ0 : ρ.val ≠ 0 := ne_zero_of_mem_nontrivialZeros ρ.2
  have hsρ : s - ρ.val ≠ 0 := sub_ne_zero_of_not_mem hs ρ.2
  have hid : 1 / (s - ρ.val) + 1 / ρ.val = s / ((s - ρ.val) * ρ.val) := by
    field_simp
    ring
  have hnorms : (0 : ℝ) ≤ ‖s‖ := norm_nonneg _
  have hnormρ : (0 : ℝ) < ‖ρ.val‖ := by
    have : (0 : ℝ) ≤ 2 * ‖s‖ := by positivity
    linarith
  have hlow : ‖ρ.val‖ / 2 ≤ ‖s - ρ.val‖ := by
    have h1 : ‖ρ.val‖ - ‖s‖ ≤ ‖s - ρ.val‖ := by
      calc ‖ρ.val‖ - ‖s‖ ≤ ‖ρ.val - s‖ := norm_sub_norm_le _ _
        _ = ‖s - ρ.val‖ := norm_sub_rev _ _
    linarith
  have hsub0 : (0 : ℝ) < ‖s - ρ.val‖ := by
    have : (0 : ℝ) < ‖ρ.val‖ / 2 := by linarith
    linarith
  calc ‖(ZD.xiOrderNat ρ.val : ℂ) * (1 / (s - ρ.val) + 1 / ρ.val)‖
      = (ZD.xiOrderNat ρ.val : ℝ) * (‖s‖ / (‖s - ρ.val‖ * ‖ρ.val‖)) := by
        rw [hid, norm_mul, norm_div, norm_mul, Complex.norm_natCast]
    _ ≤ (ZD.xiOrderNat ρ.val : ℝ) * (‖s‖ / (‖ρ.val‖ ^ 2 / 2)) := by
        have hXY : ‖ρ.val‖ ^ 2 / 2 ≤ ‖s - ρ.val‖ * ‖ρ.val‖ := by nlinarith
        gcongr
    _ = (2 * ‖s‖) * ((ZD.xiOrderNat ρ.val : ℝ) / ‖ρ.val‖ ^ 2) := by
        field_simp

/-- **The two-point Hadamard difference identity**: differencing the
completed logarithmic derivative at two points off the zero set kills the
constant and the normalizers exactly. -/
theorem xi_logDeriv_two_point {s₁ s₂ : ℂ}
    (hs₁ : s₁ ∉ ZD.NontrivialZeros) (hs₂ : s₂ ∉ ZD.NontrivialZeros) :
    deriv ZD.riemannXi s₁ / ZD.riemannXi s₁
      - deriv ZD.riemannXi s₂ / ZD.riemannXi s₂
      = ∑' ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros},
          (ZD.xiOrderNat ρ.val : ℂ) * ((s₁ - ρ.val)⁻¹ - (s₂ - ρ.val)⁻¹) := by
  obtain ⟨A, hA⟩ := ZD.xi_logDeriv_partial_fraction
  rw [hA s₁ hs₁, hA s₂ hs₂]
  have h1 := summable_hadamard_term hs₁
  have h2 := summable_hadamard_term hs₂
  rw [show ∀ T₁ T₂ : ℂ, A + T₁ - (A + T₂) = T₁ - T₂ from fun _ _ => by ring]
  rw [← h1.tsum_sub h2]
  exact tsum_congr fun ρ => by ring

/-- The spectral coordinate of a zero: `t(ρ) = −i(ρ − ½)`, the carrier's
eigenheight reading — real exactly when the zero is on the carrier. -/
noncomputable def spectralCoord (ρ : ℂ) : ℂ := -Complex.I * (ρ - 1 / 2)

/-- The resolvent factorizes through the chart rotation:
`t(ρ) − w = i·((½ + iw) − ρ)`. -/
theorem spectralCoord_sub (ρ w : ℂ) :
    spectralCoord ρ - w = Complex.I * ((1 / 2 + Complex.I * w) - ρ) := by
  unfold spectralCoord
  linear_combination (-w) * Complex.I_mul_I

/-- Resolvent inversion through the chart rotation. -/
theorem spectralCoord_sub_inv (ρ w : ℂ) :
    (spectralCoord ρ - w)⁻¹ = -Complex.I * ((1 / 2 + Complex.I * w) - ρ)⁻¹ := by
  rw [spectralCoord_sub, mul_inv, inv_I]

/-- **The Hilbert–Pólya resolvent trace identity.**  For any two resolvent
points whose chart images avoid the zero set, the multiplicity ledger's
two-point resolvent sum in spectral coordinates equals the explicit
arithmetic function `−i·Δ(ξ'/ξ)(½ + i·)`.  Unconditional; the sum runs over
the actual zero multiset with its analytic multiplicities. -/
theorem hilbertPolya_resolvent_trace {w w₀ : ℂ}
    (hw : (1 / 2 + Complex.I * w) ∉ ZD.NontrivialZeros)
    (hw₀ : (1 / 2 + Complex.I * w₀) ∉ ZD.NontrivialZeros) :
    ∑' ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros},
        (ZD.xiOrderNat ρ.val : ℂ) *
          ((spectralCoord ρ.val - w)⁻¹ - (spectralCoord ρ.val - w₀)⁻¹)
      = -Complex.I *
          (deriv ZD.riemannXi (1 / 2 + Complex.I * w)
              / ZD.riemannXi (1 / 2 + Complex.I * w)
            - deriv ZD.riemannXi (1 / 2 + Complex.I * w₀)
              / ZD.riemannXi (1 / 2 + Complex.I * w₀)) := by
  rw [xi_logDeriv_two_point hw hw₀, ← tsum_mul_left]
  exact tsum_congr fun ρ => by
    rw [spectralCoord_sub_inv, spectralCoord_sub_inv]
    ring

/-- Summability of the spectral resolvent differences. -/
theorem summable_spectral_diff {w w₀ : ℂ}
    (hw : (1 / 2 + Complex.I * w) ∉ ZD.NontrivialZeros)
    (hw₀ : (1 / 2 + Complex.I * w₀) ∉ ZD.NontrivialZeros) :
    Summable (fun ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros} =>
      (ZD.xiOrderNat ρ.val : ℂ) *
        ((spectralCoord ρ.val - w)⁻¹ - (spectralCoord ρ.val - w₀)⁻¹)) := by
  have h := ((summable_hadamard_term hw).sub (summable_hadamard_term hw₀)).mul_left
    (-Complex.I)
  apply h.congr
  intro ρ
  rw [spectralCoord_sub_inv, spectralCoord_sub_inv]
  ring

/-- **The trace as an unconditional net limit** — the operator reading: the
finite-rank diagonal truncations of the two-point resolvent difference
converge (as a net over finite subsets, hence over every window exhaustion)
to the arithmetic value. -/
theorem hilbertPolya_resolvent_trace_hasSum {w w₀ : ℂ}
    (hw : (1 / 2 + Complex.I * w) ∉ ZD.NontrivialZeros)
    (hw₀ : (1 / 2 + Complex.I * w₀) ∉ ZD.NontrivialZeros) :
    HasSum (fun ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros} =>
        (ZD.xiOrderNat ρ.val : ℂ) *
          ((spectralCoord ρ.val - w)⁻¹ - (spectralCoord ρ.val - w₀)⁻¹))
      (-Complex.I *
        (deriv ZD.riemannXi (1 / 2 + Complex.I * w)
            / ZD.riemannXi (1 / 2 + Complex.I * w)
          - deriv ZD.riemannXi (1 / 2 + Complex.I * w₀)
            / ZD.riemannXi (1 / 2 + Complex.I * w₀))) := by
  have h := (summable_spectral_diff hw hw₀).hasSum
  rwa [hilbertPolya_resolvent_trace hw hw₀] at h

end CriticalLinePhasor.HilbertPolya

#print axioms CriticalLinePhasor.HilbertPolya.summable_hadamard_term
#print axioms CriticalLinePhasor.HilbertPolya.xi_logDeriv_two_point
#print axioms CriticalLinePhasor.HilbertPolya.hilbertPolya_resolvent_trace
#print axioms CriticalLinePhasor.HilbertPolya.hilbertPolya_resolvent_trace_hasSum
