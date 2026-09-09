import RequestProject.GammaJetsSeries

/-!
# The explicit anchor's Archimedean jets as series (ledger 629, second half)

`archSide s = −weilArch(1 − s) = 1/s + 1/(s−1) + log π/2 − ½ ψ((1−s)/2)`. With the polygamma series
(`iteratedDeriv_digamma_half_one_sub_series`) and the jets of `1/(s−a)`, every jet of the Archimedean
side of the explicit anchor is a series over the Γ ticks: for `m ≥ 2`, `Re s < 0`, `Im s ≠ 0`,

  `jets archSide s m = 1/s^m + 1/(s−1)^m − Σ_{n≥0} 1/(s − 1 − 2n)^m`

(`jets_archSide_series`): the atoms of the Archimedean side are the end `0` (residue `+1`) and the Γ ticks
`1 + 2n` (`n ≥ 1`, residue `−1`), the `n = 0` tick cancelling the end `1`.
-/

open Complex Filter Topology
open CriticalLinePhasor.ContourArgument

namespace CriticalLinePhasor.SeatingLedger

/-- The jets of `1/(s − a)`: `∂^k (s−a)^{−1} = (−1)^k k! (s−a)^{−(k+1)}`. -/
theorem iteratedDeriv_one_div_sub (a : ℂ) (k : ℕ) {s : ℂ} (hs : s ≠ a) :
    iteratedDeriv k (fun s : ℂ => 1 / (s - a)) s
      = (-1) ^ k * (k.factorial : ℂ) / (s - a) ^ (k + 1) := by
  induction k generalizing s with
  | zero => simp
  | succ k ih =>
    rw [iteratedDeriv_succ]
    have hev : iteratedDeriv k (fun s : ℂ => 1 / (s - a)) =ᶠ[nhds s]
        fun s => (-1) ^ k * (k.factorial : ℂ) / (s - a) ^ (k + 1) := by
      filter_upwards [isOpen_ne.mem_nhds hs] with s' hs'
      exact ih hs'
    rw [hev.deriv_eq]
    have h0 : s - a ≠ 0 := sub_ne_zero.mpr hs
    have h1 : HasDerivAt (fun s : ℂ => (s - a) ^ (k + 1))
        (((k + 1 : ℕ) : ℂ) * (s - a) ^ (k + 1 - 1) * 1) s :=
      ((hasDerivAt_id s).sub_const a).pow (k + 1)
    have h2 : HasDerivAt (fun s : ℂ => ((s - a) ^ (k + 1))⁻¹)
        (-(((k + 1 : ℕ) : ℂ) * (s - a) ^ (k + 1 - 1) * 1) / ((s - a) ^ (k + 1)) ^ 2) s :=
      h1.inv (pow_ne_zero _ h0)
    have h3 : HasDerivAt (fun s : ℂ => (-1) ^ k * (k.factorial : ℂ) * ((s - a) ^ (k + 1))⁻¹)
        ((-1) ^ k * (k.factorial : ℂ)
          * (-(((k + 1 : ℕ) : ℂ) * (s - a) ^ (k + 1 - 1) * 1) / ((s - a) ^ (k + 1)) ^ 2)) s :=
      h2.const_mul _
    rw [show (fun s : ℂ => (-1) ^ k * (k.factorial : ℂ) / (s - a) ^ (k + 1))
        = fun s : ℂ => (-1) ^ k * (k.factorial : ℂ) * ((s - a) ^ (k + 1))⁻¹ by
      funext s; rw [div_eq_mul_inv]]
    rw [h3.deriv, Nat.add_sub_cancel, Nat.factorial_succ]
    push_cast
    field_simp
    ring

/-- `archSide` in rational-plus-digamma form. -/
theorem archSide_eq : archSide = fun s : ℂ =>
    1 / s + 1 / (s - 1) + ((Real.log Real.pi : ℝ) : ℂ) / 2
      - (1 / 2 : ℂ) * Complex.digamma ((1 - s) / 2) := by
  funext s
  unfold archSide weilArch
  rw [← Complex.digamma_def]
  have e1 : (1 : ℂ) / (1 - s) = -(1 / (s - 1)) := by rw [← neg_sub s 1, div_neg]
  have e2 : (1 : ℂ) / (1 - s - 1) = -(1 / s) := by rw [show (1 : ℂ) - s - 1 = -s by ring, div_neg]
  rw [e1, e2]
  ring

theorem isOpen_anchorDomain : IsOpen ({s : ℂ | s.re < 0} ∩ {s : ℂ | s.im ≠ 0}) :=
  isOpen_left.inter (isOpen_ne.preimage Complex.continuous_im)

/-- The pure algebra of the Archimedean jets. -/
theorem arch_alg (k : ℕ) (F A B T : ℂ) (hF : F ≠ 0) :
    (-1) ^ k / F * ((-1) ^ k * F * A + (-1) ^ k * F * B
      - 1 / 2 * ((-1 / 2) ^ k * ((-1) ^ (k + 1) * F * ((-2) ^ (k + 1) * T)))) = A + B - T := by
  have e1 : ((-1 : ℂ) ^ k) * (-1) ^ k = 1 := by rw [← mul_pow]; norm_num
  have e2 : ((-1 / 2 : ℂ)) ^ k * (-2) ^ k = 1 := by rw [← mul_pow]; norm_num
  rw [pow_succ (-1 : ℂ) k, pow_succ (-2 : ℂ) k, div_mul_eq_mul_div, div_eq_iff hF]
  linear_combination (F * A + F * B - (-1 / 2 : ℂ) ^ k * (-2) ^ k * F * T) * e1 - F * T * e2

/-- **The Archimedean jets of the explicit anchor are series over the Γ ticks.** -/
theorem jets_archSide_series {s : ℂ} (hs : s.re < 0) (hi : s.im ≠ 0) {m : ℕ} (hm : 2 ≤ m) :
    jets archSide s m
      = 1 / s ^ m + 1 / (s - 1) ^ m - ∑' n : ℕ, (1 : ℂ) / (s - 1 - 2 * n) ^ m := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  simp only [jets]
  have hVopen := isOpen_anchorDomain
  have hsV : s ∈ {s : ℂ | s.re < 0} ∩ {s : ℂ | s.im ≠ 0} := ⟨hs, hi⟩
  have hs0 : ∀ w ∈ {s : ℂ | s.re < 0} ∩ {s : ℂ | s.im ≠ 0}, w ≠ 0 := by
    intro w hw h; rw [h] at hw; simp at hw
  have hs1 : ∀ w ∈ {s : ℂ | s.re < 0} ∩ {s : ℂ | s.im ≠ 0}, w - 1 ≠ 0 := by
    intro w hw h
    have : w = 1 := by linear_combination h
    rw [this] at hw; simp at hw
  have hp0d : ContDiffOn ℂ ⊤ (fun s : ℂ => 1 / s) ({s : ℂ | s.re < 0} ∩ {s : ℂ | s.im ≠ 0}) := by
    refine DifferentiableOn.contDiffOn ?_ hVopen
    intro w hw
    have h : DifferentiableAt ℂ (fun s : ℂ => 1 / s) w :=
      (differentiableAt_const (1 : ℂ)).div differentiableAt_id (hs0 w hw)
    exact h.differentiableWithinAt
  have hp1d : ContDiffOn ℂ ⊤ (fun s : ℂ => 1 / (s - 1)) ({s : ℂ | s.re < 0} ∩ {s : ℂ | s.im ≠ 0}) := by
    refine DifferentiableOn.contDiffOn ?_ hVopen
    intro w hw
    have hd : DifferentiableAt ℂ (fun s : ℂ => s - 1) w := (differentiableAt_id (𝕜 := ℂ)).sub_const 1
    have h : DifferentiableAt ℂ (fun s : ℂ => 1 / (s - 1)) w :=
      (differentiableAt_const (1 : ℂ)).div hd (hs1 w hw)
    exact h.differentiableWithinAt
  have hqd : ContDiffOn ℂ ⊤ (fun s : ℂ => (1 / 2 : ℂ) * Complex.digamma ((1 - s) / 2))
      ({s : ℂ | s.re < 0} ∩ {s : ℂ | s.im ≠ 0}) := by
    refine DifferentiableOn.contDiffOn ?_ hVopen
    intro w hw
    have hmem := archDomain_of_im_ne_zero hw.2
    have h1 : DifferentiableAt ℂ (fun w : ℂ => (1 - w) / 2) w := by fun_prop
    have h : DifferentiableAt ℂ (fun s : ℂ => (1 / 2 : ℂ) * Complex.digamma ((1 - s) / 2)) w :=
      ((Zeta23.Stirling.differentiableAt_digamma hmem).comp w h1).const_mul _
    exact h.differentiableWithinAt
  have hU : UniqueDiffOn ℂ ({s : ℂ | s.re < 0} ∩ {s : ℂ | s.im ≠ 0}) := hVopen.uniqueDiffOn
  have harch : archSide = fun s => (((fun s : ℂ => 1 / s) + (fun s : ℂ => 1 / (s - 1)))
      - (fun s : ℂ => (1 / 2 : ℂ) * Complex.digamma ((1 - s) / 2))) s
        + ((Real.log Real.pi : ℝ) : ℂ) / 2 := by
    rw [archSide_eq]; funext s; simp only [Pi.sub_apply, Pi.add_apply]; ring
  have hconst : iteratedDeriv (j + 1) (fun s => (((fun s : ℂ => 1 / s) + (fun s : ℂ => 1 / (s - 1)))
      - (fun s : ℂ => (1 / 2 : ℂ) * Complex.digamma ((1 - s) / 2))) s
        + ((Real.log Real.pi : ℝ) : ℂ) / 2) s
      = iteratedDeriv (j + 1) (((fun s : ℂ => 1 / s) + (fun s : ℂ => 1 / (s - 1)))
        - (fun s : ℂ => (1 / 2 : ℂ) * Complex.digamma ((1 - s) / 2))) s := by
    rw [iteratedDeriv_succ', deriv_add_const', ← iteratedDeriv_succ']
  have hpq : ContDiffWithinAt ℂ (j + 1) ((fun s : ℂ => 1 / s) + (fun s : ℂ => 1 / (s - 1)))
      ({s : ℂ | s.re < 0} ∩ {s : ℂ | s.im ≠ 0}) s :=
    ((hp0d s hsV).add (hp1d s hsV)).of_le le_top
  have hsplit : iteratedDeriv (j + 1) (((fun s : ℂ => 1 / s) + (fun s : ℂ => 1 / (s - 1)))
      - (fun s : ℂ => (1 / 2 : ℂ) * Complex.digamma ((1 - s) / 2))) s
      = iteratedDeriv (j + 1) (fun s : ℂ => 1 / s) s
        + iteratedDeriv (j + 1) (fun s : ℂ => 1 / (s - 1)) s
        - iteratedDeriv (j + 1) (fun s : ℂ => (1 / 2 : ℂ) * Complex.digamma ((1 - s) / 2)) s := by
    rw [← iteratedDerivWithin_of_isOpen (f := ((fun s : ℂ => 1 / s) + (fun s : ℂ => 1 / (s - 1)))
        - (fun s : ℂ => (1 / 2 : ℂ) * Complex.digamma ((1 - s) / 2))) hVopen hsV,
      ← iteratedDerivWithin_of_isOpen (f := fun s : ℂ => 1 / s) hVopen hsV,
      ← iteratedDerivWithin_of_isOpen (f := fun s : ℂ => 1 / (s - 1)) hVopen hsV,
      ← iteratedDerivWithin_of_isOpen
        (f := fun s : ℂ => (1 / 2 : ℂ) * Complex.digamma ((1 - s) / 2)) hVopen hsV,
      iteratedDerivWithin_sub hsV hU hpq ((hqd s hsV).of_le le_top),
      iteratedDerivWithin_add hsV hU ((hp0d s hsV).of_le le_top) ((hp1d s hsV).of_le le_top)]
  rw [harch, hconst, hsplit]
  have e0 : iteratedDeriv (j + 1) (fun s : ℂ => 1 / s) s
      = (-1) ^ (j + 1) * ((j + 1).factorial : ℂ) / (s - 0) ^ (j + 1 + 1) := by
    rw [show (fun s : ℂ => 1 / s) = fun s : ℂ => 1 / (s - 0) by funext s; rw [sub_zero]]
    exact iteratedDeriv_one_div_sub 0 (j + 1) (hs0 s hsV)
  have e1 : iteratedDeriv (j + 1) (fun s : ℂ => 1 / (s - 1)) s
      = (-1) ^ (j + 1) * ((j + 1).factorial : ℂ) / (s - 1) ^ (j + 1 + 1) :=
    iteratedDeriv_one_div_sub 1 (j + 1) (sub_ne_zero.mp (hs1 s hsV))
  have eq : iteratedDeriv (j + 1) (fun s : ℂ => (1 / 2 : ℂ) * Complex.digamma ((1 - s) / 2)) s
      = (1 / 2 : ℂ) * ((-1 / 2 : ℂ) ^ (j + 1) * ((-1) ^ (j + 1 + 1) * ((j + 1).factorial : ℂ)
          * ∑' n : ℕ, (1 : ℂ) / ((1 - s) / 2 + n) ^ (j + 1 + 1))) := by
    have h := iteratedDeriv_const_mul_field (1 / 2 : ℂ)
      (fun s : ℂ => Complex.digamma ((1 - s) / 2)) (x := s) (n := j + 1)
    beta_reduce at h
    rw [h, iteratedDeriv_digamma_half_one_sub_series (by omega) hi]
  have htick : ∑' n : ℕ, (1 : ℂ) / ((1 - s) / 2 + n) ^ (j + 1 + 1)
      = (-2) ^ (j + 1 + 1) * ∑' n : ℕ, (1 : ℂ) / (s - 1 - 2 * n) ^ (j + 1 + 1) := by
    rw [← tsum_mul_left]
    apply tsum_congr
    intro n
    rw [show (1 - s) / 2 + (n : ℂ) = (s - 1 - 2 * n) / (-2) by ring, div_pow, one_div_div]
    ring
  rw [e0, e1, eq, htick, sub_zero]
  have hF : ((j + 1).factorial : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
  have key := arch_alg (j + 1) ((j + 1).factorial : ℂ) (1 / s ^ (j + 1 + 1))
    (1 / (s - 1) ^ (j + 1 + 1)) (∑' n : ℕ, (1 : ℂ) / (s - 1 - 2 * n) ^ (j + 1 + 1)) hF
  rw [← key]
  congr 1
  ring

/-- **Every jet of `ξ′/ξ` at an explicit anchor is a series**: for `m ≥ 2`, `Re s < 0`, `Im s ≠ 0`,
`jets (ξ′/ξ) s m = 1/s^m + 1/(s−1)^m − Σ_{n≥0} (s−1−2n)^{−m}
  + (−1)^{m−1}/(m−1)! · Σ_n Λ(n) (log n)^{m−1} n^{s−1}`. -/
theorem jets_xiLogDeriv_series {s : ℂ} (hs : s.re < 0) (hi : s.im ≠ 0) (m : ℕ) :
    jets (logDeriv ZD.riemannXi) s (m + 2)
      = 1 / s ^ (m + 2) + 1 / (s - 1) ^ (m + 2) - ∑' n : ℕ, (1 : ℂ) / (s - 1 - 2 * n) ^ (m + 2)
        + (-1) ^ (m + 1) / ((m + 1).factorial : ℂ)
          * LSeries (LSeries.logMul^[m + 1] CriticalLinePhasor.ContourArgument.vonMangoldtC) (1 - s) := by
  rw [show m + 2 = (m + 1) + 1 by omega, jets_xiLogDeriv_explicit hs (m + 1),
    jets_archSide_series hs hi (by omega : 2 ≤ m + 1 + 1)]

end CriticalLinePhasor.SeatingLedger

#print axioms CriticalLinePhasor.SeatingLedger.iteratedDeriv_one_div_sub
#print axioms CriticalLinePhasor.SeatingLedger.jets_archSide_series
#print axioms CriticalLinePhasor.SeatingLedger.jets_xiLogDeriv_series
