import RequestProject.ResidueJump
import RequestProject.XiHadamardFactorization
import RequestProject.ZetaContourArgument

open Complex ComplexConjugate Filter Set Topology

noncomputable section

set_option maxHeartbeats 50000

namespace CriticalLinePhasor.DVP

/-- A zero strictly left of the critical line creates a nonzero point to its right,
still left of the line, where `Re (ξ'/ξ)` is strictly positive. -/
theorem exists_logDeriv_re_pos_right_of_left_zero {rho : ℂ}
    (hrho : rho ∈ ZD.NontrivialZeros) (hleft : rho.re < 1 / 2) :
    ∃ eps : ℝ, 0 < eps ∧ rho.re + eps < 1 / 2 ∧
      ZD.riemannXi (rho + eps) ≠ 0 ∧
      0 < (logDeriv ZD.riemannXi (rho + eps)).re := by
  have han : AnalyticAt ℂ ZD.riemannXi rho :=
    ZD.ZeroCount.riemannXi_analyticOnNhd_univ rho (Set.mem_univ _)
  have hne := ZD.riemannXi_analyticOrderAt_ne_top_everywhere rho
  have hm : analyticOrderAt ZD.riemannXi rho = (ZD.xiOrderNat rho : ℕ∞) := by
    rw [ZD.xiOrderNat, analyticOrderNatAt]
    exact (ENat.coe_toNat hne).symm
  have hres := CriticalLinePhasor.ResidueJump.logDeriv_residue_eq_order han hm
  have happ : Tendsto (fun eps : ℝ => rho + (eps : ℂ))
      (nhdsWithin 0 (Set.Ioi 0)) (nhdsWithin rho {rho}ᶜ) := by
    rw [tendsto_nhdsWithin_iff]
    constructor
    · have hc : Continuous (fun eps : ℝ => rho + (eps : ℂ)) :=
        continuous_const.add Complex.continuous_ofReal
      simpa using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with eps heps
      simp only [mem_Ioi] at heps
      simp [heps.ne']
  have hprod := hres.comp happ
  have hre : Tendsto
      (fun eps : ℝ => (((rho + (eps : ℂ) - rho) *
        logDeriv ZD.riemannXi (rho + eps))).re)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (ZD.xiOrderNat rho : ℝ)) := by
    simpa [Function.comp_def, Complex.mul_re] using
      (Complex.continuous_re.tendsto (ZD.xiOrderNat rho : ℂ)).comp hprod
  have hmpos : (0 : ℝ) < ZD.xiOrderNat rho := by
    exact_mod_cast ZD.xiOrderNat_pos_of_mem_NontrivialZeros hrho
  have hpositive : ∀ᶠ eps : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)),
      0 < (((rho + (eps : ℂ) - rho) *
        logDeriv ZD.riemannXi (rho + eps))).re :=
    (tendsto_order.1 hre).1 (0 : ℝ) hmpos
  have hgap : 0 < (1 / 2 - rho.re) := by linarith
  have hsmall : ∀ᶠ eps in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      eps < 1 / 2 - rho.re := by
    exact Filter.Eventually.filter_mono nhdsWithin_le_nhds (Iio_mem_nhds hgap)
  have hself : ∀ᶠ eps : ℝ in nhdsWithin 0 (Set.Ioi 0), eps ∈ Set.Ioi 0 :=
    self_mem_nhdsWithin
  obtain ⟨eps, heps, hpos, hsmall'⟩ :=
    (hself.and (hpositive.and hsmall)).exists
  simp only [mem_Ioi] at heps
  have hmul : 0 < eps * (logDeriv ZD.riemannXi (rho + eps)).re := by
    simpa [Complex.mul_re] using hpos
  have hlogpos : 0 < (logDeriv ZD.riemannXi (rho + eps)).re :=
    pos_of_mul_pos_right hmul heps.le
  have hxine : ZD.riemannXi (rho + eps) ≠ 0 := by
    intro hzero
    rw [logDeriv_apply, hzero, div_zero] at hlogpos
    exact (lt_self_iff_false 0).mp hlogpos
  exact ⟨eps, heps, by linarith, hxine, hlogpos⟩

/-- At a zero strictly left of the critical line, the real logarithmic
derivative is unbounded above along the rightward punctured ray. -/
theorem exists_logDeriv_re_gt_right_of_left_zero {rho : ℂ}
    (hrho : rho ∈ ZD.NontrivialZeros) (hleft : rho.re < 1 / 2) (M : ℝ) :
    ∃ eps : ℝ, 0 < eps ∧ rho.re + eps < 1 / 2 ∧
      ZD.riemannXi (rho + eps) ≠ 0 ∧
      M < (logDeriv ZD.riemannXi (rho + eps)).re := by
  have han : AnalyticAt ℂ ZD.riemannXi rho :=
    ZD.ZeroCount.riemannXi_analyticOnNhd_univ rho (Set.mem_univ _)
  have hne := ZD.riemannXi_analyticOrderAt_ne_top_everywhere rho
  have hm : analyticOrderAt ZD.riemannXi rho = (ZD.xiOrderNat rho : ℕ∞) := by
    rw [ZD.xiOrderNat, analyticOrderNatAt]
    exact (ENat.coe_toNat hne).symm
  have hres := CriticalLinePhasor.ResidueJump.logDeriv_residue_eq_order han hm
  have happ : Tendsto (fun eps : ℝ => rho + (eps : ℂ))
      (nhdsWithin 0 (Set.Ioi 0)) (nhdsWithin rho {rho}ᶜ) := by
    rw [tendsto_nhdsWithin_iff]
    constructor
    · have hc : Continuous (fun eps : ℝ => rho + (eps : ℂ)) :=
        continuous_const.add Complex.continuous_ofReal
      simpa using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with eps heps
      simp only [mem_Ioi] at heps
      simp [heps.ne']
  have hprod := hres.comp happ
  have hre : Tendsto
      (fun eps : ℝ => eps * (logDeriv ZD.riemannXi (rho + eps)).re)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (ZD.xiOrderNat rho : ℝ)) := by
    simpa [Function.comp_def, Complex.mul_re] using
      (Complex.continuous_re.tendsto (ZD.xiOrderNat rho : ℂ)).comp hprod
  have hmpos : (0 : ℝ) < ZD.xiOrderNat rho := by
    exact_mod_cast ZD.xiOrderNat_pos_of_mem_NontrivialZeros hrho
  have hlarge : ∀ᶠ eps : ℝ in nhdsWithin 0 (Set.Ioi 0),
      (ZD.xiOrderNat rho : ℝ) / 2 <
        eps * (logDeriv ZD.riemannXi (rho + eps)).re :=
    (tendsto_order.1 hre).1 _ (by linarith)
  let C : ℝ := max M 0 + 1
  have hCpos : 0 < C := by
    dsimp [C]
    linarith [le_max_right M 0]
  have hMC : M < C := by
    dsimp [C]
    linarith [le_max_left M 0]
  have hgap : 0 < 1 / 2 - rho.re := by linarith
  have hbound : 0 < (ZD.xiOrderNat rho : ℝ) / (2 * C) := by positivity
  have hsmall : ∀ᶠ eps : ℝ in nhdsWithin 0 (Set.Ioi 0),
      eps < min (1 / 2 - rho.re) ((ZD.xiOrderNat rho : ℝ) / (2 * C)) :=
    Filter.Eventually.filter_mono nhdsWithin_le_nhds
      (Iio_mem_nhds (lt_min hgap hbound))
  have hself : ∀ᶠ eps : ℝ in nhdsWithin 0 (Set.Ioi 0), eps ∈ Set.Ioi 0 :=
    self_mem_nhdsWithin
  obtain ⟨eps, heps, hlarge', hsmall'⟩ :=
    (hself.and (hlarge.and hsmall)).exists
  simp only [mem_Ioi] at heps
  have hepsGap : eps < 1 / 2 - rho.re :=
    lt_of_lt_of_le hsmall' (min_le_left _ _)
  have hepsBound : eps < (ZD.xiOrderNat rho : ℝ) / (2 * C) :=
    lt_of_lt_of_le hsmall' (min_le_right _ _)
  have hmulBound : eps * C < (ZD.xiOrderNat rho : ℝ) / 2 := by
    calc
      eps * C < ((ZD.xiOrderNat rho : ℝ) / (2 * C)) * C :=
        mul_lt_mul_of_pos_right hepsBound hCpos
      _ = (ZD.xiOrderNat rho : ℝ) / 2 := by
        field_simp
  have hCu : C < (logDeriv ZD.riemannXi (rho + eps)).re :=
    lt_of_mul_lt_mul_left (hmulBound.trans hlarge') heps.le
  have hlogpos : 0 < (logDeriv ZD.riemannXi (rho + eps)).re :=
    hCpos.trans hCu
  have hxine : ZD.riemannXi (rho + eps) ≠ 0 := by
    intro hzero
    rw [logDeriv_apply, hzero, div_zero] at hlogpos
    exact (lt_self_iff_false 0).mp hlogpos
  exact ⟨eps, heps, by linarith, hxine, hMC.trans hCu⟩

/-- The requested left-half-plane sign rule excludes every zero strictly left
of the critical line. -/
theorem no_left_zero_of_logDeriv_re_nonpos
    (hsign : ∀ s : ℂ, s.re < 1 / 2 → ZD.riemannXi s ≠ 0 →
      (logDeriv ZD.riemannXi s).re ≤ 0) :
    ∀ rho ∈ ZD.NontrivialZeros, ¬ rho.re < 1 / 2 := by
  intro rho hrho hleft
  obtain ⟨eps, heps, hstill, hxi, hpos⟩ :=
    exists_logDeriv_re_pos_right_of_left_zero hrho hleft
  exact (not_lt_of_ge (hsign (rho + eps) (by simpa using hstill) hxi)) hpos

/-- The requested sign rule places every nontrivial zero on the critical line:
left zeros are excluded by the residue lemma, and right zeros by FE reflection. -/
theorem zeros_online_of_logDeriv_re_nonpos
    (hsign : ∀ s : ℂ, s.re < 1 / 2 → ZD.riemannXi s ≠ 0 →
      (logDeriv ZD.riemannXi s).re ≤ 0) :
    ∀ rho ∈ ZD.NontrivialZeros, rho.re = 1 / 2 := by
  have hnleft := no_left_zero_of_logDeriv_re_nonpos hsign
  intro rho hrho
  have hge : 1 / 2 ≤ rho.re := le_of_not_gt (hnleft rho hrho)
  have hle : rho.re ≤ 1 / 2 := by
    by_contra hnot
    have hright : 1 / 2 < rho.re := lt_of_not_ge hnot
    let rhoStar : ℂ := 1 - conj rho
    have hstar : rhoStar ∈ ZD.NontrivialZeros := by
      apply (ZD.riemannXi_eq_zero_iff rhoStar).mp
      simp only [rhoStar]
      rw [CriticalLinePhasor.ContourArgument.riemannXi_one_sub_conj,
        (ZD.riemannXi_eq_zero_iff rho).mpr hrho, map_zero]
    have hstarleft : rhoStar.re < 1 / 2 := by
      simp only [rhoStar, map_sub, map_one, Complex.conj_re, Complex.one_re,
        Complex.sub_re]
      linarith
    exact hnleft rhoStar hstar hstarleft
  exact le_antisymm hle hge

end CriticalLinePhasor.DVP

#print axioms CriticalLinePhasor.DVP.exists_logDeriv_re_pos_right_of_left_zero
#print axioms CriticalLinePhasor.DVP.exists_logDeriv_re_gt_right_of_left_zero
#print axioms CriticalLinePhasor.DVP.no_left_zero_of_logDeriv_re_nonpos
#print axioms CriticalLinePhasor.DVP.zeros_online_of_logDeriv_re_nonpos
