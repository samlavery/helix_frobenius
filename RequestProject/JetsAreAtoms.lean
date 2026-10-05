import RequestProject.LadderImpliesRH
import RequestProject.ExplicitAnchor

/-!
# The jet sequence is the atom sequence (ledger 631)

The Hadamard partial fractions of `ξ′/ξ` (`logDeriv_xiProductMult_partial_fraction`) differentiate
termwise on a zero-free ball (the method of 629), giving for `k ≥ 1`

  `∂^k (ξ′/ξ)(s) = (−1)^k k! Σ_ρ m_ρ (s−ρ)^{−(k+1)}`   (`iteratedDeriv_xiLogDeriv_series`),

so the jets `S_m = Σ_ρ m_ρ (s−ρ)^{−m}` (`m ≥ 2`) and, with 622's per-atom binomial identity
`transport_pow_identity` and the mirror relation `L(1−s̄) = −conj L(s)` for the zeroth coefficient,

  `toeplitzCoeff d (jets (ξ′/ξ) s) k = xiCoeff s k`   (`toeplitzCoeff_jets_eq_xiCoeff`).

Hence the ladder of the JET sequence at an anchor is the ladder of the ATOM sequence, and with 628
(the jets at an explicit anchor are the explicit prime-and-Γ jets) and 630:

  **`rh_of_explicit_ladder`: for `Re s₀ < 0`, if the Toeplitz forms of
  `toeplitzCoeff d (jets explicitLogDeriv s₀)` are all real and nonnegative, every nontrivial zero
  is on the line.**
-/

open Complex Finset Filter Topology

namespace CriticalLinePhasor.SeatingLedger

local notation "Zs" => {ρ : ℂ // ρ ∈ ZD.NontrivialZeros}

theorem isOpen_compl_zeros : IsOpen (ZD.NontrivialZeros)ᶜ := by
  have h : ZD.NontrivialZeros = {z : ℂ | ZD.riemannXi z = 0} := by
    ext z; exact (ZD.riemannXi_eq_zero_iff z).symm
  rw [h]
  exact (isClosed_eq ZD.ZeroCount.riemannXi_continuous continuous_const).isOpen_compl

theorem zero_ne_zero' (ρ : Zs) : ρ.val ≠ 0 := by
  intro h; have := ρ.property; rw [h] at this; obtain ⟨h1, -, -⟩ := this; simp at h1

/-- On a zero-free ball, uniform lower bounds `‖w − ρ‖ ≥ ‖s − ρ‖/2 ≥ (κ/2)‖ρ‖` and `‖w − ρ‖ ≥ δ/2`. -/
theorem ball_bounds {s : ℂ} (hs : s ∉ ZD.NontrivialZeros) :
    ∃ δ > 0, ∃ κ > 0, ∀ w ∈ Metric.ball s (δ / 2), ∀ ρ : Zs,
      δ / 2 ≤ ‖w - ρ.val‖ ∧ κ / 2 * ‖ρ.val‖ ≤ ‖w - ρ.val‖ := by
  obtain ⟨δ, hδ, hball⟩ := exists_zero_free_ball hs
  obtain ⟨κ, hκ, hκs⟩ := exists_kappa hs
  refine ⟨δ, hδ, κ, hκ, fun w hw ρ => ?_⟩
  have hws : ‖w - s‖ < δ / 2 := by rw [← dist_eq_norm]; exact Metric.mem_ball.mp hw
  have h1 : ‖s - ρ.val‖ ≤ ‖w - ρ.val‖ + ‖w - s‖ := by
    calc ‖s - ρ.val‖ = ‖(w - ρ.val) - (w - s)‖ := by ring_nf
      _ ≤ ‖w - ρ.val‖ + ‖w - s‖ := norm_sub_le _ _
  have hsρ := hball ρ.val ρ.property
  have hκρ := hκs ρ.val ρ.property
  constructor
  · linarith
  · linarith

/-- **Termwise derivative of the Hadamard series** at a point off the zeros. -/
theorem hasSum_deriv_hadamard {s : ℂ} (hs : s ∉ ZD.NontrivialZeros) :
    HasSum (fun ρ : Zs => (ZD.xiOrderNat ρ.val : ℂ) * (-(1 / (s - ρ.val) ^ 2)))
      (deriv (fun w : ℂ => ∑' ρ : Zs, (ZD.xiOrderNat ρ.val : ℂ) * (1 / (w - ρ.val) + 1 / ρ.val)) s) := by
  obtain ⟨δ, hδ, κ, hκ, hb⟩ := ball_bounds hs
  have hr0 : 0 < δ / 2 := by positivity
  set U := Metric.ball s (δ / 2) with hU
  have hzU : s ∈ U := Metric.mem_ball_self hr0
  have hwne : ∀ w ∈ U, ∀ ρ : Zs, w - ρ.val ≠ 0 := by
    intro w hw ρ h0
    have := (hb w hw ρ).1; rw [h0, norm_zero] at this; linarith
  set u : Zs → ℝ := fun ρ => 2 * (‖s‖ + δ / 2) / κ * ((ZD.xiOrderNat ρ.val : ℝ) / ‖ρ.val‖ ^ 2) with hu
  have hFle : ∀ (ρ : Zs) (w : ℂ), w ∈ U →
      ‖(ZD.xiOrderNat ρ.val : ℂ) * (1 / (w - ρ.val) + 1 / ρ.val)‖ ≤ u ρ := by
    intro ρ w hw
    have hρ0 := zero_ne_zero' ρ
    have hwρ := hwne w hw ρ
    have hid : (1 : ℂ) / (w - ρ.val) + 1 / ρ.val = w / (ρ.val * (w - ρ.val)) := by
      field_simp; ring
    rw [hid, norm_mul, norm_div, norm_mul, Complex.norm_natCast, hu]
    simp only
    have hwb : ‖w‖ ≤ ‖s‖ + δ / 2 := by
      have hws : ‖w - s‖ < δ / 2 := by rw [← dist_eq_norm]; exact Metric.mem_ball.mp hw
      calc ‖w‖ = ‖s + (w - s)‖ := by ring_nf
        _ ≤ ‖s‖ + ‖w - s‖ := norm_add_le _ _
        _ ≤ ‖s‖ + δ / 2 := by linarith
    have hlow := (hb w hw ρ).2
    have hρpos : 0 < ‖ρ.val‖ := norm_pos_iff.mpr hρ0
    have hden : κ / 2 * ‖ρ.val‖ * ‖ρ.val‖ ≤ ‖ρ.val‖ * ‖w - ρ.val‖ := by
      calc κ / 2 * ‖ρ.val‖ * ‖ρ.val‖ = ‖ρ.val‖ * (κ / 2 * ‖ρ.val‖) := by ring
        _ ≤ ‖ρ.val‖ * ‖w - ρ.val‖ := by gcongr
    have hdpos : 0 < κ / 2 * ‖ρ.val‖ * ‖ρ.val‖ := by positivity
    calc (ZD.xiOrderNat ρ.val : ℝ) * (‖w‖ / (‖ρ.val‖ * ‖w - ρ.val‖))
        ≤ (ZD.xiOrderNat ρ.val : ℝ) * ((‖s‖ + δ / 2) / (κ / 2 * ‖ρ.val‖ * ‖ρ.val‖)) := by
          gcongr
      _ = 2 * (‖s‖ + δ / 2) / κ * ((ZD.xiOrderNat ρ.val : ℝ) / ‖ρ.val‖ ^ 2) := by
          field_simp
  have husum : Summable u := ZD.summable_xiOrderNat_div_norm_sq_nontrivialZeros.mul_left _
  have hFdiff : ∀ ρ : Zs, DifferentiableOn ℂ
      (fun w : ℂ => (ZD.xiOrderNat ρ.val : ℂ) * (1 / (w - ρ.val) + 1 / ρ.val)) U := by
    intro ρ w hw
    apply DifferentiableAt.differentiableWithinAt
    have h1 : DifferentiableAt ℂ (fun w : ℂ => 1 / (w - ρ.val)) w :=
      (differentiableAt_const _).div (differentiableAt_id.sub_const _) (hwne w hw ρ)
    exact (h1.add_const _).const_mul _
  have hkey := hasSum_deriv_of_summable_norm husum hFdiff Metric.isOpen_ball hFle hzU
  have hderiv : ∀ ρ : Zs,
      deriv (fun w : ℂ => (ZD.xiOrderNat ρ.val : ℂ) * (1 / (w - ρ.val) + 1 / ρ.val)) s
        = (ZD.xiOrderNat ρ.val : ℂ) * (-(1 / (s - ρ.val) ^ 2)) := by
    intro ρ
    have h0 := hwne s hzU ρ
    have h1 : HasDerivAt (fun w : ℂ => (w - ρ.val)⁻¹) (-1 / (s - ρ.val) ^ 2) s :=
      ((hasDerivAt_id s).sub_const ρ.val).inv h0
    have h2 : HasDerivAt (fun w : ℂ => (ZD.xiOrderNat ρ.val : ℂ) * ((w - ρ.val)⁻¹ + 1 / ρ.val))
        ((ZD.xiOrderNat ρ.val : ℂ) * (-1 / (s - ρ.val) ^ 2)) s :=
      (h1.add_const _).const_mul _
    rw [show (fun w : ℂ => (ZD.xiOrderNat ρ.val : ℂ) * (1 / (w - ρ.val) + 1 / ρ.val))
        = fun w : ℂ => (ZD.xiOrderNat ρ.val : ℂ) * ((w - ρ.val)⁻¹ + 1 / ρ.val) by
      funext w; rw [one_div]]
    rw [h2.deriv]; ring
  simp only [hderiv] at hkey
  exact hkey

/-- **Termwise derivative of `Σ_ρ m_ρ (w−ρ)^{−k}`**, `k ≥ 2`, at a point off the zeros. -/
theorem hasSum_deriv_zeroPow {s : ℂ} (hs : s ∉ ZD.NontrivialZeros) {k : ℕ} (hk : 2 ≤ k) :
    HasSum (fun ρ : Zs => (ZD.xiOrderNat ρ.val : ℂ) * (-(k : ℂ) / (s - ρ.val) ^ (k + 1)))
      (deriv (fun w : ℂ => ∑' ρ : Zs, (ZD.xiOrderNat ρ.val : ℂ) * (1 / (w - ρ.val) ^ k)) s) := by
  obtain ⟨δ, hδ, κ, hκ, hb⟩ := ball_bounds hs
  have hr0 : 0 < δ / 2 := by positivity
  set U := Metric.ball s (δ / 2) with hU
  have hzU : s ∈ U := Metric.mem_ball_self hr0
  have hwne : ∀ w ∈ U, ∀ ρ : Zs, w - ρ.val ≠ 0 := by
    intro w hw ρ h0
    have := (hb w hw ρ).1; rw [h0, norm_zero] at this; linarith
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
  set u : Zs → ℝ := fun ρ =>
    (1 / ((κ / 2) ^ 2 * (δ / 2) ^ j)) * ((ZD.xiOrderNat ρ.val : ℝ) / ‖ρ.val‖ ^ 2) with hu
  have hFle : ∀ (ρ : Zs) (w : ℂ), w ∈ U →
      ‖(ZD.xiOrderNat ρ.val : ℂ) * (1 / (w - ρ.val) ^ (j + 2))‖ ≤ u ρ := by
    intro ρ w hw
    have hρ0 := zero_ne_zero' ρ
    have hρpos : 0 < ‖ρ.val‖ := norm_pos_iff.mpr hρ0
    obtain ⟨hδw, hκw⟩ := hb w hw ρ
    rw [norm_mul, norm_div, norm_one, norm_pow, Complex.norm_natCast, hu]
    simp only
    have hprod : (κ / 2 * ‖ρ.val‖) ^ 2 * (δ / 2) ^ j ≤ ‖w - ρ.val‖ ^ (j + 2) := by
      rw [pow_add, mul_comm]
      exact mul_le_mul (pow_le_pow_left₀ (by positivity) hδw j)
        (pow_le_pow_left₀ (by positivity) hκw 2) (by positivity) (by positivity)
    have hppos : 0 < (κ / 2 * ‖ρ.val‖) ^ 2 * (δ / 2) ^ j := by positivity
    calc (ZD.xiOrderNat ρ.val : ℝ) * (1 / ‖w - ρ.val‖ ^ (j + 2))
        ≤ (ZD.xiOrderNat ρ.val : ℝ) * (1 / ((κ / 2 * ‖ρ.val‖) ^ 2 * (δ / 2) ^ j)) := by
          gcongr
      _ = 1 / ((κ / 2) ^ 2 * (δ / 2) ^ j) * ((ZD.xiOrderNat ρ.val : ℝ) / ‖ρ.val‖ ^ 2) := by
          field_simp
  have husum : Summable u := ZD.summable_xiOrderNat_div_norm_sq_nontrivialZeros.mul_left _
  have hFdiff : ∀ ρ : Zs, DifferentiableOn ℂ
      (fun w : ℂ => (ZD.xiOrderNat ρ.val : ℂ) * (1 / (w - ρ.val) ^ (j + 2))) U := by
    intro ρ w hw
    apply DifferentiableAt.differentiableWithinAt
    have h1 : DifferentiableAt ℂ (fun w : ℂ => (w - ρ.val) ^ (j + 2)) w :=
      (differentiableAt_id.sub_const _).pow _
    exact ((differentiableAt_const _).div h1 (pow_ne_zero _ (hwne w hw ρ))).const_mul _
  have hkey := hasSum_deriv_of_summable_norm husum hFdiff Metric.isOpen_ball hFle hzU
  have hderiv : ∀ ρ : Zs,
      deriv (fun w : ℂ => (ZD.xiOrderNat ρ.val : ℂ) * (1 / (w - ρ.val) ^ (j + 2))) s
        = (ZD.xiOrderNat ρ.val : ℂ) * (-((j + 2 : ℕ) : ℂ) / (s - ρ.val) ^ (j + 2 + 1)) := by
    intro ρ
    have h0 := hwne s hzU ρ
    have h1 : HasDerivAt (fun w : ℂ => (w - ρ.val) ^ (j + 2))
        (((j + 2 : ℕ) : ℂ) * (s - ρ.val) ^ (j + 2 - 1) * 1) s :=
      ((hasDerivAt_id s).sub_const ρ.val).pow (j + 2)
    have h2 : HasDerivAt (fun w : ℂ => ((w - ρ.val) ^ (j + 2))⁻¹)
        (-(((j + 2 : ℕ) : ℂ) * (s - ρ.val) ^ (j + 2 - 1) * 1) / ((s - ρ.val) ^ (j + 2)) ^ 2) s :=
      h1.inv (pow_ne_zero _ h0)
    have h3 : HasDerivAt (fun w : ℂ => (ZD.xiOrderNat ρ.val : ℂ) * ((w - ρ.val) ^ (j + 2))⁻¹)
        ((ZD.xiOrderNat ρ.val : ℂ)
          * (-(((j + 2 : ℕ) : ℂ) * (s - ρ.val) ^ (j + 2 - 1) * 1) / ((s - ρ.val) ^ (j + 2)) ^ 2)) s :=
      h2.const_mul _
    rw [show (fun w : ℂ => (ZD.xiOrderNat ρ.val : ℂ) * (1 / (w - ρ.val) ^ (j + 2)))
        = fun w : ℂ => (ZD.xiOrderNat ρ.val : ℂ) * ((w - ρ.val) ^ (j + 2))⁻¹ by
      funext w; rw [one_div]]
    rw [h3.deriv, show j + 2 - 1 = j + 1 by omega]
    field_simp
    ring
  simp only [hderiv] at hkey
  exact hkey

/-- `ξ′/ξ` is the Hadamard series plus a constant near any point off the zeros. -/
theorem xiLogDeriv_eventuallyEq_hadamard {s : ℂ} (hs : s ∉ ZD.NontrivialZeros) :
    ∃ A : ℂ, logDeriv ZD.riemannXi =ᶠ[nhds s]
      fun w => A + ∑' ρ : Zs, (ZD.xiOrderNat ρ.val : ℂ) * (1 / (w - ρ.val) + 1 / ρ.val) := by
  obtain ⟨A, hA⟩ := ZD.xi_logDeriv_sub_product_const_off_zeros
  refine ⟨A, ?_⟩
  filter_upwards [isOpen_compl_zeros.mem_nhds hs] with w hw
  have h := hA w hw
  rw [← logDeriv_apply, ZD.logDeriv_xiProductMult_partial_fraction hw] at h
  linear_combination h

/-- **The jets of `ξ′/ξ` are the sums over the zeros**: for `k ≥ 1` and `s` off the zeros,
`∂^k (ξ′/ξ)(s) = (−1)^k k! Σ_ρ m_ρ (s−ρ)^{−(k+1)}`. -/
theorem iteratedDeriv_xiLogDeriv_series {s : ℂ} (hs : s ∉ ZD.NontrivialZeros) {k : ℕ} (hk : 1 ≤ k) :
    iteratedDeriv k (logDeriv ZD.riemannXi) s
      = (-1) ^ k * (k.factorial : ℂ) * ∑' ρ : Zs, (ZD.xiOrderNat ρ.val : ℂ) * (1 / (s - ρ.val) ^ (k + 1)) := by
  induction k generalizing s with
  | zero => omega
  | succ k ih =>
    rcases Nat.eq_zero_or_pos k with h0 | hpos
    · subst h0
      obtain ⟨A, hev⟩ := xiLogDeriv_eventuallyEq_hadamard hs
      rw [iteratedDeriv_one, hev.deriv_eq, deriv_const_add, ← (hasSum_deriv_hadamard hs).tsum_eq]
      rw [show (fun ρ : Zs => (ZD.xiOrderNat ρ.val : ℂ) * (-(1 / (s - ρ.val) ^ 2)))
          = fun ρ : Zs => (-1 : ℂ) * ((ZD.xiOrderNat ρ.val : ℂ) * (1 / (s - ρ.val) ^ 2)) from
        funext (fun ρ => by ring), tsum_mul_left]
      norm_num
    · rw [iteratedDeriv_succ]
      have hev : iteratedDeriv k (logDeriv ZD.riemannXi) =ᶠ[nhds s]
          fun w => (-1) ^ k * (k.factorial : ℂ)
            * ∑' ρ : Zs, (ZD.xiOrderNat ρ.val : ℂ) * (1 / (w - ρ.val) ^ (k + 1)) := by
        filter_upwards [isOpen_compl_zeros.mem_nhds hs] with w hw
        exact ih hw hpos
      rw [hev.deriv_eq, deriv_const_mul_field,
        ← (hasSum_deriv_zeroPow hs (k := k + 1) (by omega)).tsum_eq]
      rw [show (fun ρ : Zs => (ZD.xiOrderNat ρ.val : ℂ) * (-((k + 1 : ℕ) : ℂ) / (s - ρ.val) ^ (k + 1 + 1)))
          = fun ρ : Zs => (-((k + 1 : ℕ) : ℂ))
              * ((ZD.xiOrderNat ρ.val : ℂ) * (1 / (s - ρ.val) ^ (k + 1 + 1))) from
        funext (fun ρ => by ring), tsum_mul_left, Nat.factorial_succ]
      push_cast
      ring

/-- The jets `S_m = Σ_ρ m_ρ (s−ρ)^{−m}`, `m ≥ 2`. -/
theorem jets_xiLogDeriv_atoms {s : ℂ} (hs : s ∉ ZD.NontrivialZeros) (k : ℕ) :
    jets (logDeriv ZD.riemannXi) s (k + 2)
      = ∑' ρ : Zs, (ZD.xiOrderNat ρ.val : ℂ) * (1 / (s - ρ.val) ^ (k + 2)) := by
  simp only [jets]
  rw [iteratedDeriv_xiLogDeriv_series hs (k := k + 1) (by omega)]
  have hf : ((k + 1).factorial : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
  have hsq : ((-1 : ℂ) ^ (k + 1)) ^ 2 = 1 := by
    rw [← pow_mul]; exact Even.neg_one_pow ⟨k + 1, by ring⟩
  rw [show (-1 : ℂ) ^ (k + 1) / ((k + 1).factorial : ℂ) * ((-1) ^ (k + 1) * ((k + 1).factorial : ℂ)
        * ∑' ρ : Zs, (ZD.xiOrderNat ρ.val : ℂ) * (1 / (s - ρ.val) ^ (k + 1 + 1)))
      = ((-1 : ℂ) ^ (k + 1)) ^ 2 * (((k + 1).factorial : ℂ) / ((k + 1).factorial : ℂ))
        * ∑' ρ : Zs, (ZD.xiOrderNat ρ.val : ℂ) * (1 / (s - ρ.val) ^ (k + 1 + 1)) by ring,
    hsq, div_self hf, one_mul, one_mul]

theorem summable_zeroPow {s : ℂ} (hs : s ∉ ZD.NontrivialZeros) (k : ℕ) :
    Summable (fun ρ : Zs => (ZD.xiOrderNat ρ.val : ℂ) * (1 / (s - ρ.val) ^ (k + 2))) := by
  rcases Nat.eq_zero_or_pos k with h0 | hpos
  · subst h0
    have h := (hasSum_deriv_hadamard hs).summable
    refine (h.mul_left (-1)).congr (fun ρ => ?_)
    ring
  · have h := (hasSum_deriv_zeroPow hs (k := k + 1) (by omega)).summable
    have hk0 : (-((k + 1 : ℕ) : ℂ)) ≠ 0 := by
      have : ((k + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (by omega : k + 1 ≠ 0)
      exact neg_ne_zero.mpr this
    refine (h.mul_left (-((k + 1 : ℕ) : ℂ))⁻¹).congr (fun ρ => ?_)
    field_simp

/-- **The jet sequence is the atom sequence**: `toeplitzCoeff d (jets (ξ′/ξ) s) k = xiCoeff s k`. -/
theorem toeplitzCoeff_jets_eq_xiCoeff {s : ℂ} (hs : s ∉ ZD.NontrivialZeros) (hs' : s.re ≠ 1 / 2)
    (k : ℕ) :
    toeplitzCoeff ((2 * s.re - 1 : ℝ) : ℂ) (jets (logDeriv ZD.riemannXi) s) k = xiCoeff s k := by
  have hc : 1 - (starRingEnd ℂ) s ∉ ZD.NontrivialZeros := mirror_notMem_nontrivialZeros hs
  have hd : ((2 * s.re - 1 : ℝ) : ℂ) ≠ 0 := by
    have : (2 * s.re - 1 : ℝ) ≠ 0 := by intro h; apply hs'; linarith
    exact_mod_cast this
  have hA : ∀ ρ : Zs, s - ρ.val ≠ 0 := fun ρ => sub_ne_zero_of_notMem hs ρ.property
  have hB : ∀ ρ : Zs, ρ.val - (1 - (starRingEnd ℂ) s) ≠ 0 := by
    intro ρ h
    have := sub_ne_zero_of_notMem hc ρ.property
    apply this; linear_combination -h
  cases k with
  | zero =>
    -- `2 Re L(s)/d = Σ m_ρ ω_ρ`
    simp only [toeplitzCoeff, jets, pow_zero, Nat.factorial_zero, Nat.cast_one, div_one, one_mul,
      iteratedDeriv_zero]
    unfold xiCoeff
    simp only [pow_zero, mul_one]
    obtain ⟨A, hA'⟩ := ZD.xi_logDeriv_sub_product_const_off_zeros
    have hLs := hA' s hs
    have hLc := hA' _ hc
    rw [← logDeriv_apply, ZD.logDeriv_xiProductMult_partial_fraction hs] at hLs
    rw [← logDeriv_apply, ZD.logDeriv_xiProductMult_partial_fraction hc] at hLc
    have h1 := ZD.summable_weighted_partial_fraction hs
    have h2 := ZD.summable_weighted_partial_fraction hc
    have hterm : ∀ ρ : Zs, (ZD.xiOrderNat ρ.val : ℂ) * atomWeight s ρ.val
        = ((2 * s.re - 1 : ℝ) : ℂ)⁻¹
          * ((ZD.xiOrderNat ρ.val : ℂ) * (1 / (s - ρ.val) + 1 / ρ.val)
            - (ZD.xiOrderNat ρ.val : ℂ) * (1 / ((1 - (starRingEnd ℂ) s) - ρ.val) + 1 / ρ.val)) := by
      intro ρ
      have hρ0 := zero_ne_zero' ρ
      have hd' : s - (1 - (starRingEnd ℂ) s) ≠ 0 := by rw [mirror_d]; exact hd
      have hB' := hB ρ
      have hA'' := hA ρ
      unfold atomWeight
      rw [← mirror_d]
      have hcρ : (1 - (starRingEnd ℂ) s) - ρ.val ≠ 0 := by intro h; apply hB'; linear_combination -h
      field_simp
      ring
    simp_rw [hterm]
    rw [tsum_mul_left, (h1.hasSum.sub h2.hasSum).tsum_eq]
    have e1 : ∑' ρ : Zs, (ZD.xiOrderNat ρ.val : ℂ) * (1 / (s - ρ.val) + 1 / ρ.val)
        = logDeriv ZD.riemannXi s - A := by linear_combination -hLs
    have e2 : ∑' ρ : Zs, (ZD.xiOrderNat ρ.val : ℂ) * (1 / ((1 - (starRingEnd ℂ) s) - ρ.val) + 1 / ρ.val)
        = logDeriv ZD.riemannXi (1 - (starRingEnd ℂ) s) - A := by linear_combination -hLc
    rw [e1, e2, xiLogDeriv_mirror,
      show logDeriv ZD.riemannXi s - A - (-(starRingEnd ℂ) (logDeriv ZD.riemannXi s) - A)
        = logDeriv ZD.riemannXi s + (starRingEnd ℂ) (logDeriv ZD.riemannXi s) by ring,
      Complex.add_conj]
    push_cast
    ring
  | succ k =>
    simp only [toeplitzCoeff]
    have hjet : ∀ i ∈ range (k + 1), jets (logDeriv ZD.riemannXi) s (k + 2 - i)
        = ∑' ρ : Zs, (ZD.xiOrderNat ρ.val : ℂ) * (1 / (s - ρ.val) ^ (k + 2 - i)) := by
      intro i hi
      rw [mem_range] at hi
      have := jets_xiLogDeriv_atoms hs (k - i)
      rwa [show k - i + 2 = k + 2 - i by omega] at this
    have hsum : ∀ i ∈ range (k + 1), Summable (fun ρ : Zs =>
        (ZD.xiOrderNat ρ.val : ℂ) * (1 / (s - ρ.val) ^ (k + 2 - i))) := by
      intro i hi
      rw [mem_range] at hi
      have := summable_zeroPow hs (k - i)
      rwa [show k - i + 2 = k + 2 - i by omega] at this
    have hL : ∑ i ∈ range (k + 1), ((k.choose i : ℂ) * ((2 * s.re - 1 : ℝ) : ℂ) ^ (k - i) * (-1) ^ i
          * jets (logDeriv ZD.riemannXi) s (k + 2 - i))
        = ∑' ρ : Zs, ∑ i ∈ range (k + 1), ((k.choose i : ℂ) * ((2 * s.re - 1 : ℝ) : ℂ) ^ (k - i)
          * (-1) ^ i * ((ZD.xiOrderNat ρ.val : ℂ) * (1 / (s - ρ.val) ^ (k + 2 - i)))) := by
      rw [Summable.tsum_finsetSum (fun i hi => (hsum i hi).mul_left _)]
      exact Finset.sum_congr rfl (fun i hi => by rw [hjet i hi, tsum_mul_left])
    rw [hL]
    unfold xiCoeff
    apply tsum_congr
    intro ρ
    have hid := transport_pow_identity s ρ.val (hA ρ) k
    rw [mirror_d] at hid
    have hconv : ∀ i : ℕ, (1 : ℂ) / (s - ρ.val) ^ (k + 2 - i) = (s - ρ.val)⁻¹ ^ (k + 2 - i) :=
      fun i => by rw [one_div, inv_pow]
    simp_rw [hconv]
    rw [show (∑ i ∈ range (k + 1), ((k.choose i : ℂ) * ((2 * s.re - 1 : ℝ) : ℂ) ^ (k - i) * (-1) ^ i
          * ((ZD.xiOrderNat ρ.val : ℂ) * (s - ρ.val)⁻¹ ^ (k + 2 - i))))
        = (ZD.xiOrderNat ρ.val : ℂ) * ∑ i ∈ range (k + 1), ((k.choose i : ℂ)
          * ((2 * s.re - 1 : ℝ) : ℂ) ^ (k - i) * (-1) ^ i * (s - ρ.val)⁻¹ ^ (k + 2 - i)) by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun i _ => by ring), ← hid]
    have hB' := hB ρ
    rw [show (ρ.val - (1 - (starRingEnd ℂ) s)) ^ k
        = (ρ.val - (1 - (starRingEnd ℂ) s))⁻¹ * (ρ.val - (1 - (starRingEnd ℂ) s)) ^ (k + 1) by
      rw [pow_succ', inv_mul_cancel_left₀ hB']]
    unfold atomWeight transport
    rw [div_pow, mul_inv, div_eq_mul_inv, ← inv_pow]
    ring

/-- The ladder of the explicit prime-and-Γ sequence at an anchor. -/
def ExplicitLadder (s : ℂ) : Prop :=
  ∀ (N : ℕ) (c : Fin N → ℂ),
    (toeplitzForm (hermExt (toeplitzCoeff ((2 * s.re - 1 : ℝ) : ℂ)
      (jets explicitLogDeriv s))) c).im = 0 ∧
    0 ≤ (toeplitzForm (hermExt (toeplitzCoeff ((2 * s.re - 1 : ℝ) : ℂ)
      (jets explicitLogDeriv s))) c).re

/-- **The positivity of the explicit sequence at one anchor puts every zero on the line**: for
`Re s < 0`, if the Toeplitz forms of the coefficient sequence built from the explicit prime-and-Γ jets
are all real and nonnegative, every nontrivial zero has real part `½`. -/
theorem rh_of_explicit_ladder {s : ℂ} (hs : s.re < 0) (h : ExplicitLadder s) : RH := by
  have hs0 : s ∉ ZD.NontrivialZeros := notMem_nontrivialZeros_of_re_nonpos hs.le
  have hs' : s.re ≠ 1 / 2 := by intro h; linarith
  have hseq : toeplitzCoeff ((2 * s.re - 1 : ℝ) : ℂ) (jets explicitLogDeriv s) = xiCoeff s := by
    funext k
    rw [← jets_xiLogDeriv_eq_explicit hs, toeplitzCoeff_jets_eq_xiCoeff hs0 hs' k]
  have e : ExplicitLadder s = Ladder s := by
    unfold ExplicitLadder Ladder; rw [hseq]
  rw [e] at h
  exact rh_of_ladder hs0 (by linarith) h

end CriticalLinePhasor.SeatingLedger

#print axioms CriticalLinePhasor.SeatingLedger.iteratedDeriv_xiLogDeriv_series
#print axioms CriticalLinePhasor.SeatingLedger.toeplitzCoeff_jets_eq_xiCoeff
#print axioms CriticalLinePhasor.SeatingLedger.rh_of_explicit_ladder
