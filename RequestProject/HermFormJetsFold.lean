import Mathlib
import RequestProject.HermFormJets

/-!
# Folding the mirror-point jets into jets at `s` (ledger 595)

`hermForm_eq_jets` (594) writes the seat form as a finite functional of the jets of `ξ′/ξ` at `s = ½ + iw`
and at the mirror `c = 1 − s̄`. Two function-level facts fold the mirror jets away:

* `ξ′/ξ` is odd under `z ↦ 1 − z` (`xiLogDeriv_odd`), so by Mathlib's `iteratedDeriv_comp_const_sub`
  the `n`-th jet at `1 − t` is `−(−1)^n` times the jet at `t` (`jet_reflect`);
* `ξ′/ξ` commutes with conjugation (`logDeriv_xi_conj`, from `riemannXi_conj`), and a function commuting
  with conjugation has all its derivatives commuting with conjugation (`iteratedDeriv_conj_comm`, proved
  from the slope characterisation with no differentiability hypothesis: at a point of
  non-differentiability both sides are `0`).

Result: **`rh_iff_jets_s_nonneg`** — RH ⟺ a sign condition on a finite functional of the jets of `ξ′/ξ`
at the single point `s = σ₀ + iγ`, `1 < σ₀ < 3/2`, quantified over `γ`, `σ₀`, and test polynomials.
-/

open Complex Finset Filter Topology
open CriticalLinePhasor.SeatPrimeAnchorHermitian

noncomputable section

namespace CriticalLinePhasor.ContourArgument

/-! ## 1. Derivatives commute with conjugation -/

/-- If `f` commutes with conjugation, a derivative at `z` conjugates to a derivative at `z̄`. -/
theorem hasDerivAt_conj_of_conj_comm {f : ℂ → ℂ}
    (hf : ∀ z, f ((starRingEnd ℂ) z) = (starRingEnd ℂ) (f z))
    {z f' : ℂ} (h : HasDerivAt f f' z) :
    HasDerivAt f ((starRingEnd ℂ) f') ((starRingEnd ℂ) z) := by
  rw [hasDerivAt_iff_tendsto_slope_zero] at h ⊢
  have hc : Tendsto (starRingEnd ℂ) (𝓝[≠] (0 : ℂ)) (𝓝[≠] (0 : ℂ)) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · have := Complex.continuous_conj.tendsto (0 : ℂ)
      rw [map_zero] at this
      exact this.mono_left nhdsWithin_le_nhds
    · exact eventually_nhdsWithin_of_forall (fun t ht => by simpa using ht)
  have h2 := (Complex.continuous_conj.tendsto f').comp (h.comp hc)
  refine h2.congr (fun t => ?_)
  simp only [Function.comp_apply, smul_eq_mul, map_mul, map_sub, map_inv₀, Complex.conj_conj]
  rw [← hf, ← hf, map_add, Complex.conj_conj]

theorem deriv_conj_comm {f : ℂ → ℂ}
    (hf : ∀ z, f ((starRingEnd ℂ) z) = (starRingEnd ℂ) (f z)) (z : ℂ) :
    deriv f ((starRingEnd ℂ) z) = (starRingEnd ℂ) (deriv f z) := by
  by_cases hd : DifferentiableAt ℂ f z
  · exact (hasDerivAt_conj_of_conj_comm hf hd.hasDerivAt).deriv
  · have hd' : ¬ DifferentiableAt ℂ f ((starRingEnd ℂ) z) := by
      intro h
      have := hasDerivAt_conj_of_conj_comm hf h.hasDerivAt
      rw [Complex.conj_conj] at this
      exact hd this.differentiableAt
    rw [deriv_zero_of_not_differentiableAt hd, deriv_zero_of_not_differentiableAt hd', map_zero]

theorem iteratedDeriv_conj_comm {f : ℂ → ℂ}
    (hf : ∀ z, f ((starRingEnd ℂ) z) = (starRingEnd ℂ) (f z)) (n : ℕ) (z : ℂ) :
    iteratedDeriv n f ((starRingEnd ℂ) z) = (starRingEnd ℂ) (iteratedDeriv n f z) := by
  induction n generalizing z with
  | zero => simp [iteratedDeriv_zero, hf]
  | succ n ih =>
    rw [iteratedDeriv_succ]
    exact deriv_conj_comm (fun w => ih w) z

/-- `ξ′/ξ` commutes with conjugation (at zeros both sides are `0`). -/
theorem logDeriv_xi_conj (s : ℂ) :
    logDeriv ZD.riemannXi ((starRingEnd ℂ) s) = (starRingEnd ℂ) (logDeriv ZD.riemannXi s) := by
  rw [logDeriv_apply, logDeriv_apply, riemannXi_conj, map_div₀]
  congr 1
  exact deriv_conj_comm riemannXi_conj s

/-! ## 2. The jets under `z ↦ 1 − z` -/

/-- `(ξ′/ξ)^{(n)}(1 − t) = −(−1)^n (ξ′/ξ)^{(n)}(t)`, every `n`, every `t`. -/
theorem jet_reflect (n : ℕ) (t : ℂ) :
    iteratedDeriv n (logDeriv ZD.riemannXi) (1 - t)
      = -((-1 : ℂ) ^ n * iteratedDeriv n (logDeriv ZD.riemannXi) t) := by
  have hfun : (fun z => logDeriv ZD.riemannXi (1 - z)) = fun z => -(logDeriv ZD.riemannXi z) := by
    funext z
    exact CriticalLinePhasor.SeatingLedger.xiLogDeriv_odd z
  have h1 := congrFun (iteratedDeriv_comp_const_sub (f := logDeriv ZD.riemannXi) (n := n) (s := 1)) t
  rw [hfun, iteratedDeriv_fun_neg, smul_eq_mul] at h1
  have hpow : ((-1 : ℂ) ^ n) * ((-1 : ℂ) ^ n) = 1 := by
    rw [← mul_pow]
    simp
  linear_combination (-(-1 : ℂ) ^ n) * h1 - iteratedDeriv n (logDeriv ZD.riemannXi) (1 - t) * hpow

/-- The jets at the mirror `1 − s̄` are signed conjugates of the jets at `s`. -/
theorem jet_mirror (n : ℕ) (s : ℂ) :
    iteratedDeriv n (logDeriv ZD.riemannXi) (1 - (starRingEnd ℂ) s)
      = -((-1 : ℂ) ^ n * (starRingEnd ℂ) (iteratedDeriv n (logDeriv ZD.riemannXi) s)) := by
  rw [jet_reflect, iteratedDeriv_conj_comm logDeriv_xi_conj]

/-! ## 3. The jet functional at one point -/

/-- The jet functional of one monomial pair `(j, k)` with all jets at `s` (`d = s − c` the real
anchor gap): `a₁·2Re(ξ′/ξ)(s) + Σ_i a_{i+2} (ξ′/ξ)^{(i+1)}(s)/((−1)^{i+1}(i+1)!)
+ Σ_l b_{l+2} (−1)^{l+1} conj((ξ′/ξ)^{(l+1)}(s))/(l+1)!`. -/
def jetValueS (s d : ℂ) (M : ℕ) (j k : ℕ) : ℂ :=
  (pf d j k).1 1 * (2 * ((logDeriv ZD.riemannXi s).re : ℂ))
    + ∑ i ∈ range (M - 1), (pf d j k).1 (i + 2)
        * (iteratedDeriv (i + 1) (logDeriv ZD.riemannXi) s / ((-1) ^ (i + 1) * ((i + 1).factorial : ℂ)))
    + ∑ l ∈ range (M - 1), (pf d j k).2 (l + 2)
        * ((-1) ^ (l + 1) * (starRingEnd ℂ) (iteratedDeriv (l + 1) (logDeriv ZD.riemannXi) s)
            / ((l + 1).factorial : ℂ))

theorem jetValue_eq_jetValueS (s : ℂ) (M j k : ℕ) :
    jetValue s (1 - (starRingEnd ℂ) s) M j k = jetValueS s (s - (1 - (starRingEnd ℂ) s)) M j k := by
  unfold jetValue jetValueS
  congr 1
  refine Finset.sum_congr rfl (fun l _ => ?_)
  rw [jet_mirror]
  have hF : ((-1 : ℂ) ^ (l + 1) * ((l + 1).factorial : ℂ)) ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ (by norm_num)) (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _))
  have hF' : ((l + 1).factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  congr 1
  field_simp
  ring

/-- **The seat form as a jet functional at the single point `s = ½ + iw`.** -/
theorem hermForm_eq_jets_s (w : ℂ) (R : Polynomial ℂ) (hR : R.coeff 0 = 0)
    (hs : (1 / 2 : ℂ) + I * w ∉ ZD.NontrivialZeros)
    (hc : (1 / 2 : ℂ) + I * (starRingEnd ℂ) w ∉ ZD.NontrivialZeros)
    (hd : (1 / 2 : ℂ) + I * w - ((1 / 2 : ℂ) + I * (starRingEnd ℂ) w) ≠ 0) :
    hermForm w R
      = ∑ j ∈ range (R.natDegree + 1), ∑ k ∈ range (R.natDegree + 1),
          ((starRingEnd ℂ) (R.coeff j) * R.coeff k)
            * jetValueS ((1 / 2 : ℂ) + I * w)
                ((1 / 2 : ℂ) + I * w - ((1 / 2 : ℂ) + I * (starRingEnd ℂ) w))
                (2 * R.natDegree + 2) j k := by
  rw [hermForm_eq_jets w R hR hs hc hd]
  refine Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun k _ => ?_))
  congr 1
  have hm := mirror_anchor w
  rw [hm, jetValue_eq_jetValueS]

/-- At the door's anchor the gap is `d = 2σ₀ − 1`. -/
theorem anchor_gap (γ σ₀ : ℝ) :
    (σ₀ : ℂ) + (γ : ℂ) * I - (((1 - σ₀ : ℝ) : ℂ) + (γ : ℂ) * I) = ((2 * σ₀ - 1 : ℝ) : ℂ) := by
  push_cast
  ring

/-- **The seat form at the door's anchor, jets at one point.** -/
theorem hermForm_anchor_eq_jets_s (γ σ₀ : ℝ) (h : 1 < σ₀) (R : Polynomial ℂ) (hR : R.coeff 0 = 0) :
    hermForm (CriticalLinePhasor.SeatPrimeAnchor.anchor γ σ₀) R
      = ∑ j ∈ range (R.natDegree + 1), ∑ k ∈ range (R.natDegree + 1),
          ((starRingEnd ℂ) (R.coeff j) * R.coeff k)
            * jetValueS ((σ₀ : ℂ) + (γ : ℂ) * I) ((2 * σ₀ - 1 : ℝ) : ℂ) (2 * R.natDegree + 2) j k := by
  have hs := anchor_s γ σ₀
  have hc := anchor_c γ σ₀
  have hd : (σ₀ : ℂ) + (γ : ℂ) * I - (((1 - σ₀ : ℝ) : ℂ) + (γ : ℂ) * I) ≠ 0 := by
    rw [anchor_gap]
    intro h0
    have := congrArg Complex.re h0
    simp at this
    linarith
  rw [hermForm_eq_jets_s _ R hR (hs ▸ anchor_s_not_zero h) (hc ▸ anchor_c_not_zero h)
    (by rw [hs, hc]; exact hd), hs, hc, anchor_gap]

/-- **The door with jets at one prime-chart point.** RH ⟺ for all `γ`, all `1 < σ₀ < 3/2`, all `R` with
`R(0) = 0`: `Re Σ_{j,k} conj(r_j) r_k · jetValueS(σ₀+iγ, 2σ₀−1) j k ≥ 0`. The hypothesis side mentions
only `2Re(ξ′/ξ)(s)`, the jets `(ξ′/ξ)^{(m)}(s)` and their conjugates, at `s = σ₀ + iγ`, `Re s > 1`. -/
theorem rh_iff_jets_s_nonneg :
    (∀ ρ ∈ ZD.NontrivialZeros, ρ.re = 1 / 2) ↔
    (∀ γ σ₀ : ℝ, 1 < σ₀ → σ₀ < 3 / 2 → ∀ R : Polynomial ℂ, R.coeff 0 = 0 →
      0 ≤ (∑ j ∈ range (R.natDegree + 1), ∑ k ∈ range (R.natDegree + 1),
          ((starRingEnd ℂ) (R.coeff j) * R.coeff k)
            * jetValueS ((σ₀ : ℂ) + (γ : ℂ) * I) ((2 * σ₀ - 1 : ℝ) : ℂ)
                (2 * R.natDegree + 2) j k).re) := by
  rw [rh_iff_hermForm_nonneg]
  constructor
  · intro H γ σ₀ h1 h2 R hR
    rw [← hermForm_anchor_eq_jets_s γ σ₀ h1 R hR]
    exact H γ σ₀ h1 h2 R hR
  · intro H γ σ₀ h1 h2 R hR
    rw [hermForm_anchor_eq_jets_s γ σ₀ h1 R hR]
    exact H γ σ₀ h1 h2 R hR

#print axioms iteratedDeriv_conj_comm
#print axioms jet_mirror
#print axioms rh_iff_jets_s_nonneg

end CriticalLinePhasor.ContourArgument
