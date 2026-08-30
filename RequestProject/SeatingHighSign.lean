import RequestProject.SeatingShellReceiver

/-!
# The high sign condition: the seat's valley floor, localized

The compiled seat form of RH is a sign condition — `Re[ξ′/ξ] ≤ 0` left of
the critical line.  This file localizes it by the ladder and the shell: the
sign is needed only in the HIGH LEFT CHANNEL

  `1269/2 < |Im s|`,  `A/log⁹|Im s| < Re s < 1/2`

(above the compiled ladder, right of the classical zero-free margin).

Mechanism: an off-line zero `ρ'` (mirrored left of the line) carries a
positive integer residue `m = xiOrderNat ρ' ≥ 1`; approaching the pole from
the right along the real direction, `(s−ρ')·ξ′/ξ(s) → m`, so at some point
of the channel `Re[ξ′/ξ] > 0` — one point of positivity refutes the
hypothesis.  DC first: the residue is computed exactly; no estimate
appears.

No `sorry`, no `axiom`.
-/

open Complex ComplexConjugate Filter Topology

noncomputable section

namespace CriticalLinePhasor.SeatingLedger

open CriticalLinePhasor

/-- **RH from the high sign condition**: there is a compiled `A > 0` such
that `Re[ξ′/ξ] ≤ 0` on the high left channel alone forces every nontrivial
zero onto the critical line. -/
theorem rh_of_high_sign :
    ∃ A : ℝ, 0 < A ∧
      ((∀ s : ℂ, 1269/2 < |s.im| →
          A / (Real.log |s.im|)^9 < s.re → s.re < 1/2 →
          (logDeriv ZD.riemannXi s).re ≤ 0) →
        ∀ ρ ∈ ZD.NontrivialZeros, ρ.re = 1/2) := by
  obtain ⟨A, hA0, _hAle, hdepth⟩ := offline_depth_bound
  refine ⟨A, hA0, fun hsign => ?_⟩
  intro ρ hρ
  by_contra hre
  -- the ladder pushes the ordinate high
  have hladder : 1269/2 < |ρ.im| := by
    by_contra hle
    push_neg at hle
    exact hre (CriticalLinePhasor.DVP.online_below_1269o2 ρ hρ hle)
  -- reflect to the left of the line if needed
  obtain ⟨ρ', hρ', hβlt, him_eq⟩ :
      ∃ ρ', ρ' ∈ ZD.NontrivialZeros ∧ ρ'.re < 1/2 ∧ |ρ'.im| = |ρ.im| := by
    rcases lt_or_gt_of_ne hre with h | h
    · exact ⟨ρ, hρ, h, rfl⟩
    · refine ⟨1 - conj ρ, mirror_mem hρ, ?_, ?_⟩
      · rw [mirror_re]
        linarith
      · rw [mirror_im]
  -- the shell floor: the left zero sits right of the classical margin
  have hd := hdepth ρ' hρ' (by rw [him_eq]; linarith)
  have hβpos : A / (Real.log |ρ'.im|)^9 < ρ'.re := by
    rw [abs_of_nonpos (by linarith)] at hd
    linarith
  -- the residue at the pole is the multiplicity, a positive integer
  have han : AnalyticAt ℂ ZD.riemannXi ρ' :=
    ZD.ZeroCount.riemannXi_analyticOnNhd_univ ρ' (Set.mem_univ _)
  have hne := ZD.riemannXi_analyticOrderAt_ne_top_everywhere ρ'
  have hm : analyticOrderAt ZD.riemannXi ρ' = (ZD.xiOrderNat ρ' : ℕ∞) := by
    rw [ZD.xiOrderNat, analyticOrderNatAt]
    exact (ENat.coe_toNat hne).symm
  have hres := CriticalLinePhasor.ResidueJump.logDeriv_residue_eq_order han hm
  have hpos := ZD.xiOrderNat_pos_of_mem_NontrivialZeros hρ'
  have hm0R : (0:ℝ) < (ZD.xiOrderNat ρ' : ℝ) := by exact_mod_cast hpos
  -- approach the pole from the right along the real direction
  have hpath : Tendsto (fun h : ℝ => ρ' + (h:ℂ))
      (nhdsWithin (0:ℝ) (Set.Ioi 0)) (nhdsWithin ρ' {ρ'}ᶜ) := by
    rw [tendsto_nhdsWithin_iff]
    constructor
    · have hc : Continuous (fun h : ℝ => ρ' + (h:ℂ)) :=
        continuous_const.add Complex.continuous_ofReal
      have := hc.tendsto 0
      simp only [Complex.ofReal_zero, add_zero] at this
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with h hh
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      intro hEq
      have hc0 : (h:ℂ) = 0 := by linear_combination hEq
      have hr0 : h = 0 := by exact_mod_cast hc0
      rw [hr0] at hh
      exact lt_irrefl 0 (Set.mem_Ioi.mp hh)
  have h2 : Tendsto (fun h : ℝ => (h:ℂ) * logDeriv ZD.riemannXi (ρ' + h))
      (nhdsWithin (0:ℝ) (Set.Ioi 0)) (nhds (ZD.xiOrderNat ρ' : ℂ)) := by
    have hcomp := hres.comp hpath
    have heq : ((fun s => (s - ρ') * logDeriv ZD.riemannXi s)
        ∘ fun h : ℝ => ρ' + (h:ℂ))
        = fun h : ℝ => (h:ℂ) * logDeriv ZD.riemannXi (ρ' + h) := by
      funext h
      simp only [Function.comp_apply]
      congr 1
      ring
    rwa [heq] at hcomp
  -- eventual: the product is within m/2 of m, and h is small
  have hev1 : ∀ᶠ h : ℝ in nhdsWithin (0:ℝ) (Set.Ioi 0),
      dist ((h:ℂ) * logDeriv ZD.riemannXi (ρ' + h))
        (ZD.xiOrderNat ρ' : ℂ) < (ZD.xiOrderNat ρ' : ℝ)/2 :=
    Metric.tendsto_nhds.mp h2 _ (half_pos hm0R)
  have hev2 : ∀ᶠ h : ℝ in nhdsWithin (0:ℝ) (Set.Ioi 0),
      h < 1/2 - ρ'.re := by
    have hlt : (0:ℝ) < 1/2 - ρ'.re := by linarith
    have hid : Tendsto (fun h : ℝ => h)
        (nhdsWithin (0:ℝ) (Set.Ioi 0)) (nhds 0) :=
      tendsto_id.mono_left nhdsWithin_le_nhds
    exact hid.eventually (eventually_lt_nhds hlt)
  obtain ⟨h, ⟨hd1, hd2⟩, hh0⟩ :=
    ((hev1.and hev2).and self_mem_nhdsWithin).exists
  have hh0' : (0:ℝ) < h := hh0
  -- one point of positivity
  have hre_big : 0 < (logDeriv ZD.riemannXi (ρ' + h)).re := by
    rw [dist_eq_norm] at hd1
    have habs := Complex.abs_re_le_norm
      ((h:ℂ) * logDeriv ZD.riemannXi (ρ' + h) - (ZD.xiOrderNat ρ' : ℂ))
    have hre1 : ((h:ℂ) * logDeriv ZD.riemannXi (ρ' + h)
        - (ZD.xiOrderNat ρ' : ℂ)).re
        = h * (logDeriv ZD.riemannXi (ρ' + h)).re - (ZD.xiOrderNat ρ' : ℝ) := by
      simp [Complex.sub_re, Complex.re_ofReal_mul]
    have hband : |h * (logDeriv ZD.riemannXi (ρ' + h)).re
        - (ZD.xiOrderNat ρ' : ℝ)| < (ZD.xiOrderNat ρ' : ℝ)/2 := by
      rw [← hre1]
      exact lt_of_le_of_lt habs hd1
    have hmul : 0 < h * (logDeriv ZD.riemannXi (ρ' + h)).re := by
      have := abs_lt.mp hband
      linarith [this.1]
    rcases mul_pos_iff.mp hmul with ⟨_, hx⟩ | ⟨hneg, _⟩
    · exact hx
    · linarith
  -- the point is in the channel: contradiction with the sign hypothesis
  have hregion := hsign (ρ' + (h:ℂ)) ?_ ?_ ?_
  · linarith [hregion, hre_big]
  · simp only [Complex.add_im, Complex.ofReal_im, add_zero]
    rw [him_eq]
    exact hladder
  · simp only [Complex.add_re, Complex.ofReal_re, Complex.add_im,
      Complex.ofReal_im, add_zero]
    linarith
  · simp only [Complex.add_re, Complex.ofReal_re]
    linarith

end CriticalLinePhasor.SeatingLedger

#print axioms CriticalLinePhasor.SeatingLedger.rh_of_high_sign
