import RequestProject.DVPWeightedCount
import RequestProject.DVPRegionFixed
import RequestProject.SeatScalarCriterion
import RequestProject.DVPThetaIncrement

/-!
# R6: the interior positivity rung at exponent 1

`seat_interior_rung` (DVPZeroFreeRegion) proved seat-energy nonnegativity
at depth `½ − c/log⁹(height)`.  The compiled exponent-1 zero-free region
(`zero_free_region_exponent_one`) widens the empty deep-window argument to
depth `½ − c/log(height)` — the proven positivity frontier now approaches
the critical line at the classical de la Vallée Poussin rate.
-/

open Complex Filter Topology
open CriticalLinePhasor.SeatScalar
open CriticalLinePhasor.HilbertPolya

noncomputable section

namespace CriticalLinePhasor.DVP

/-- **R6: THE INTERIOR POSITIVITY RUNG, EXPONENT 1.**  There is `c > 0`
such that the seat energy is nonnegative at every admissible anchor of
height `|Re w| ≥ e³² + 2` and depth `|Im w| ≥ ½ − c/log(|Re w| + ½)`.
Mechanism: the exponent-1 region caps the depth of every zero in the
anchor's unit window strictly below the anchor's depth (the FE partner
giving the two-sided bound), so the deep-window of the local-resonance law
is empty and every term of the seat energy is nonnegative. -/
theorem seat_interior_rung_one : ∃ c : ℝ, 0 < c ∧ ∀ w : ℂ,
    Real.exp 32 + 2 ≤ |w.re| →
    1/2 - c / Real.log (|w.re| + 1/2) ≤ |w.im| →
    ((1/2 + Complex.I * w) ∉ ZD.NontrivialZeros) →
    ((1/2 + Complex.I * (starRingEnd ℂ) w) ∉ ZD.NontrivialZeros) →
    (w - (starRingEnd ℂ) w ≠ 0) →
    0 ≤ (∑' ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros},
        (ZD.xiOrderNat ρ.val : ℂ) *
          ((CriticalLinePhasor.HilbertPolya.spectralCoord ρ.val - w)⁻¹ *
            (CriticalLinePhasor.HilbertPolya.spectralCoord ρ.val
              - (starRingEnd ℂ) w)⁻¹)).re := by
  obtain ⟨c, hcpos, hregion⟩ := zero_free_region_exponent_one
  refine ⟨c, hcpos, fun w hre him hw hw' hwim => ?_⟩
  have hwindow := seat_energy_ge_window hw hw' hwim
  -- the deep-window is empty
  have hempty : IsEmpty {ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros} //
      |ρ.val.im - w.re| < 1 / 2 ∧ |w.im| < |ρ.val.re - 1 / 2|} := by
    constructor
    rintro ⟨⟨ρ, hρ⟩, hnear, hdeep⟩
    simp only at hnear hdeep
    set β : ℝ := ρ.re with hβdef
    set γ : ℝ := ρ.im with hγdef
    have hβ0 : 0 < β := hρ.1
    have hβ1' : β < 1 := hρ.2.1
    -- the ordinate is high
    have hγlb : |w.re| - 1/2 ≤ |γ| := by
      have h1 := abs_sub_abs_le_abs_sub w.re γ
      rw [abs_sub_comm γ w.re] at hnear
      linarith [hnear, h1]
    have hγ32 : Real.exp 32 ≤ |γ| := by linarith
    have hγub : |γ| ≤ |w.re| + 1/2 := by
      have h1 := abs_sub_abs_le_abs_sub γ w.re
      linarith [hnear, h1]
    set L : ℝ := Real.log |γ| with hLdef
    have hγpos : (0:ℝ) < |γ| := by linarith [Real.exp_pos 32]
    have hL32 : (32:ℝ) ≤ L := by
      rw [hLdef]
      have := Real.log_le_log (Real.exp_pos 32) hγ32
      rwa [Real.log_exp] at this
    have hLpos : (0:ℝ) < L := by linarith
    -- region: upper bound on β
    have hβup : β ≤ 1 - c / L := by
      have h := hregion ρ hρ.2.2 (by rw [← hγdef]; exact hγ32)
      rw [← hγdef, ← hLdef] at h
      rw [hβdef]
      exact h
    -- region at the FE partner: lower bound on β
    have hβlow : c / L ≤ β := by
      have hmem' :=
        CriticalLinePhasor.FoliatedGlobalPolarization.feReflect_mem hρ
      have hpt' : ((1 - β : ℝ) : ℂ) + I * γ
          = CriticalLinePhasor.FoliatedPolarization.feReflect ρ := by
        rw [CriticalLinePhasor.FoliatedPolarization.feReflect, hβdef, hγdef]
        apply Complex.ext <;> simp
      have hζ' : riemannZeta (((1 - β : ℝ) : ℂ) + I * γ) = 0 := by
        rw [hpt']
        exact hmem'.2.2
      have hpim : (((1 - β : ℝ) : ℂ) + I * γ).im = γ := by
        simp
      have hpre : (((1 - β : ℝ) : ℂ) + I * γ).re = 1 - β := by
        simp
      have h := hregion (((1 - β : ℝ) : ℂ) + I * γ) hζ'
        (by rw [hpim]; exact hγ32)
      rw [hpre, hpim, ← hLdef] at h
      linarith
    -- depth cap
    have hdepth_cap : |β - 1/2| ≤ 1/2 - c / L := by
      rw [abs_le]
      constructor <;> linarith
    -- the anchor is at least that deep
    have hΛ : L ≤ Real.log (|w.re| + 1/2) := by
      rw [hLdef]
      apply Real.log_le_log hγpos
      exact hγub
    have hmono : c / Real.log (|w.re| + 1/2) ≤ c / L :=
      div_le_div_of_nonneg_left (le_of_lt hcpos) hLpos hΛ
    have hanchor : |β - 1/2| ≤ |w.im| := by
      calc |β - 1/2| ≤ 1/2 - c / L := hdepth_cap
        _ ≤ 1/2 - c / Real.log (|w.re| + 1/2) := by linarith
        _ ≤ |w.im| := him
    rw [hβdef] at hanchor
    linarith [hdeep, hanchor]
  -- empty window ⟹ zero window sum ⟹ nonneg energy
  have hzero : (∑' x : {ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros} //
      |ρ.val.im - w.re| < 1 / 2 ∧ |w.im| < |ρ.val.re - 1 / 2|},
      (ZD.xiOrderNat x.val.val : ℂ) *
        ((CriticalLinePhasor.HilbertPolya.spectralCoord x.val.val - w)⁻¹ *
          (CriticalLinePhasor.HilbertPolya.spectralCoord x.val.val
            - (starRingEnd ℂ) w)⁻¹)) = 0 := by
    exact tsum_empty
  rw [hzero] at hwindow
  simpa using hwindow

set_option maxHeartbeats 3200000 in
/-- **R7c-1: the unit-window count in ledger multiplicities.**  For
`T ≥ e⁴`, the zeros in the height-window `|γ − T| ≤ ½` (a finite set) carry
total `xiOrderNat` at most `48·log T`: those right of the line sit in the
counted ball `B̄(2+iT, 8/5)`, those left of it enter through their FE
partners with multiplicity preserved. -/
theorem window_xiOrderNat_count {T : ℝ} (hT : Real.exp 4 ≤ T) :
    ∃ W : Finset ℂ,
      (∀ ρ : ℂ, ρ ∈ W ↔ ρ ∈ ZD.NontrivialZeros ∧ |ρ.im - T| ≤ 1/2) ∧
      (∑ ρ ∈ W, (ZD.xiOrderNat ρ : ℝ)) ≤ 48 * Real.log T := by
  have hTpos : (0:ℝ) < T := lt_of_lt_of_le (Real.exp_pos 4) hT
  have hT50 : (50:ℝ) ≤ T := by
    have he2 : (7.38:ℝ) ≤ Real.exp 1 * Real.exp 1 := by
      nlinarith [Real.exp_one_gt_d9]
    have h4 : Real.exp 4 = Real.exp 1 * Real.exp 1
        * (Real.exp 1 * Real.exp 1) := by
      rw [← Real.exp_add, ← Real.exp_add]
      norm_num
    nlinarith [he2, Real.exp_pos 1]
  -- the window is finite
  have hfin : {ρ : ℂ | ρ ∈ ZD.NontrivialZeros ∧ |ρ.im - T| ≤ 1/2}.Finite := by
    apply Set.Finite.subset
      (ZD.ZeroCount.NontrivialZeros_inter_closedBall_finite (T + 2))
    rintro ρ ⟨hρ, hwin⟩
    refine ⟨hρ, ?_⟩
    rw [Metric.mem_closedBall, dist_zero_right]
    have him : |ρ.im| ≤ T + 1/2 := by
      have h1 := abs_sub_abs_le_abs_sub ρ.im T
      rw [abs_of_pos hTpos] at h1
      linarith
    calc ‖ρ‖ ≤ |ρ.re| + |ρ.im| := Complex.norm_le_abs_re_add_abs_im ρ
      _ ≤ 1 + (T + 1/2) := by
          apply add_le_add _ him
          rw [abs_of_pos hρ.1]
          exact le_of_lt hρ.2.1
      _ ≤ T + 2 := by linarith
  refine ⟨hfin.toFinset, fun ρ => by rw [Set.Finite.mem_toFinset]; rfl, ?_⟩
  -- the counting ball
  set c : ℂ := (2:ℂ) + T * Complex.I with hcdef
  have hcre : c.re = 2 := by rw [hcdef]; simp
  have hcim : c.im = T := by rw [hcdef]; simp
  set CB := Metric.closedBall c (8/5) with hCBdef
  -- ball membership for window zeros right of the line
  have hball_mem : ∀ ρ : ℂ, ρ ∈ ZD.NontrivialZeros → |ρ.im - T| ≤ 1/2 →
      1/2 ≤ ρ.re → ρ ∈ CB := by
    intro ρ hρ hwin hre
    rw [hCBdef, Metric.mem_closedBall, dist_eq_norm]
    have hsq : ‖ρ - c‖^2 = (ρ.re - 2)^2 + (ρ.im - T)^2 := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
      rw [Complex.sub_re, Complex.sub_im, hcre, hcim]
      ring
    have h1 : (ρ.re - 2)^2 ≤ (3/2)^2 := by
      have hρ1 := hρ.2.1
      nlinarith
    have h2 : (ρ.im - T)^2 ≤ (1/2)^2 := by
      nlinarith [sq_abs (ρ.im - T), abs_nonneg (ρ.im - T)]
    have hsq_le : ‖ρ - c‖^2 ≤ (8/5)^2 := by
      rw [hsq]
      nlinarith
    nlinarith [norm_nonneg (ρ - c), sq_nonneg (‖ρ - c‖ - 8/5),
      sq_nonneg (‖ρ - c‖ + 8/5)]
  -- analyticity of ζ on the ball
  have hanal : AnalyticOnNhd ℂ riemannZeta CB := by
    rw [hCBdef]
    apply AnalyticOnNhd.mono
      (DifferentiableOn.analyticOnNhd
        (f := riemannZeta) (s := {z : ℂ | z ≠ 1})
        (fun z hz => (differentiableAt_riemannZeta hz).differentiableWithinAt)
        isOpen_ne)
    intro z hz
    simp only [Metric.mem_closedBall] at hz
    intro h1
    rw [h1, dist_eq_norm] at hz
    have him : |((1:ℂ) - c).im| ≤ ‖(1:ℂ) - c‖ := Complex.abs_im_le_norm _
    have heq : ((1:ℂ) - c).im = -T := by
      simp [Complex.sub_im, hcim]
    rw [heq, abs_neg, abs_of_pos hTpos] at him
    linarith
  have hζc : riemannZeta c ≠ 0 :=
    riemannZeta_ne_zero_of_one_lt_re (by rw [hcre]; norm_num)
  -- ball zeros have divisor ≥ 1, and equal to xiOrderNat
  have hdiv_ge : ∀ u ∈ CB, riemannZeta u = 0 →
      1 ≤ MeromorphicOn.divisor riemannZeta CB u := by
    intro u hu hζu
    have hordne : analyticOrderAt riemannZeta u ≠ 0 := by
      rw [analyticOrderAt_ne_zero]
      exact ⟨hanal u hu, hζu⟩
    have hordtop : analyticOrderAt riemannZeta u ≠ ⊤ := by
      have hpre : IsPreconnected CB := by
        rw [hCBdef]
        exact (convex_closedBall c (8/5)).isPreconnected
      have hcmem : c ∈ CB := by
        rw [hCBdef]
        exact Metric.mem_closedBall_self (by norm_num)
      exact CriticalLinePhasor.DVP.analyticOrderAt_ne_top_of_ne_zero
        hpre hanal hcmem hζc hu
    obtain ⟨m, hm⟩ : ∃ m : ℕ, (m : ℕ∞) = analyticOrderAt riemannZeta u :=
      ENat.ne_top_iff_exists.mp hordtop
    have hm_ne : m ≠ 0 := fun h => hordne (by rw [← hm, h]; rfl)
    have hm1 : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr hm_ne
    rw [MeromorphicOn.divisor_apply hanal.meromorphicOn hu,
      (hanal u hu).meromorphicOrderAt_eq, ← hm]
    simp
    exact hm1
  have hxi_div : ∀ u ∈ CB, u.im ≠ 0 →
      (ZD.xiOrderNat u : ℤ)
        = MeromorphicOn.divisor riemannZeta CB u := by
    intro u hu him
    rw [CriticalLinePhasor.DVP.xiOrderNat_eq_zeta_orderNat him,
      MeromorphicOn.AnalyticOnNhd.divisor_apply hanal hu]
  have him_CB : ∀ u ∈ CB, u.im ≠ 0 := by
    intro u hu
    rw [hCBdef, Metric.mem_closedBall, dist_eq_norm] at hu
    have him := Complex.abs_im_le_norm (u - c)
    rw [Complex.sub_im, hcim] at him
    intro h0
    rw [h0, zero_sub, abs_neg, abs_of_pos hTpos] at him
    linarith
  -- the ball count
  have hcount := CriticalLinePhasor.DVP.zeta_ball_count_two hT
  have hsupp : (MeromorphicOn.divisor riemannZeta CB).support.Finite := by
    rw [hCBdef]
    exact (MeromorphicOn.divisor riemannZeta _).finiteSupport
      (isCompact_closedBall c (8/5))
  have hfinsum : (∑ᶠ u, MeromorphicOn.divisor riemannZeta CB u)
      = ∑ u ∈ hsupp.toFinset, MeromorphicOn.divisor riemannZeta CB u :=
    finsum_eq_sum _ hsupp
  have hdiv_nonneg : ∀ u : ℂ,
      0 ≤ MeromorphicOn.divisor riemannZeta CB u := fun u =>
    MeromorphicOn.AnalyticOnNhd.divisor_nonneg hanal u
  -- the generic half-count: any Finset of ball zeros carries ≤ 24 log T
  have hhalf : ∀ V : Finset ℂ, (∀ u ∈ V, u ∈ CB ∧ riemannZeta u = 0) →
      (∑ u ∈ V, (ZD.xiOrderNat u : ℝ)) ≤ 24 * Real.log T := by
    intro V hV
    have hVsub : V ⊆ hsupp.toFinset := by
      intro u hu
      rw [Set.Finite.mem_toFinset, Function.mem_support]
      intro h0
      have := hdiv_ge u (hV u hu).1 (hV u hu).2
      omega
    calc (∑ u ∈ V, (ZD.xiOrderNat u : ℝ))
        = ∑ u ∈ V, ((MeromorphicOn.divisor riemannZeta CB u : ℤ) : ℝ) := by
          apply Finset.sum_congr rfl
          intro u hu
          have := hxi_div u (hV u hu).1 (him_CB u (hV u hu).1)
          exact_mod_cast congrArg (fun x : ℤ => (x : ℝ)) this
      _ ≤ ∑ u ∈ hsupp.toFinset,
            ((MeromorphicOn.divisor riemannZeta CB u : ℤ) : ℝ) := by
          apply Finset.sum_le_sum_of_subset_of_nonneg hVsub
          intro u _ _
          exact_mod_cast hdiv_nonneg u
      _ = ((∑ᶠ u, MeromorphicOn.divisor riemannZeta CB u : ℤ) : ℝ) := by
          rw [hfinsum]
          push_cast
          rfl
      _ ≤ 24 * Real.log T := by
          rw [hCBdef, hcdef] at *
          exact hcount
  -- split the window at the critical line
  set W := hfin.toFinset with hW
  have hWmem : ∀ ρ ∈ W, ρ ∈ ZD.NontrivialZeros ∧ |ρ.im - T| ≤ 1/2 := by
    intro ρ hρ
    rwa [hW, Set.Finite.mem_toFinset] at hρ
  rw [← Finset.sum_filter_add_sum_filter_not W (fun ρ => 1/2 ≤ ρ.re)]
  have hplus : (∑ ρ ∈ W.filter (fun ρ => 1/2 ≤ ρ.re),
      (ZD.xiOrderNat ρ : ℝ)) ≤ 24 * Real.log T := by
    apply hhalf
    intro u hu
    rw [Finset.mem_filter] at hu
    obtain ⟨hρ, hwin⟩ := hWmem u hu.1
    exact ⟨hball_mem u hρ hwin hu.2, hρ.2.2⟩
  have hminus : (∑ ρ ∈ W.filter (fun ρ => ¬ 1/2 ≤ ρ.re),
      (ZD.xiOrderNat ρ : ℝ)) ≤ 24 * Real.log T := by
    have hrefl : (∑ ρ ∈ W.filter (fun ρ => ¬ 1/2 ≤ ρ.re),
        (ZD.xiOrderNat ρ : ℝ))
        = ∑ u ∈ (W.filter (fun ρ => ¬ 1/2 ≤ ρ.re)).image
            CriticalLinePhasor.FoliatedPolarization.feReflect,
          (ZD.xiOrderNat u : ℝ) := by
      rw [Finset.sum_image]
      · apply Finset.sum_congr rfl
        intro ρ _
        rw [CriticalLinePhasor.FoliatedGlobalPolarization.xiOrderNat_feReflect]
      · intro a _ b _ h
        have h' : (1:ℂ) - (starRingEnd ℂ) a = 1 - (starRingEnd ℂ) b := h
        have h2 := congrArg (starRingEnd ℂ) (sub_right_injective h')
        simpa [Complex.conj_conj] using h2
    rw [hrefl]
    apply hhalf
    intro u hu
    rw [Finset.mem_image] at hu
    obtain ⟨ρ, hρW, rfl⟩ := hu
    rw [Finset.mem_filter] at hρW
    obtain ⟨hρ, hwin⟩ := hWmem ρ hρW.1
    have hmem' := CriticalLinePhasor.FoliatedGlobalPolarization.feReflect_mem hρ
    have hre' : (CriticalLinePhasor.FoliatedPolarization.feReflect ρ).re
        = 1 - ρ.re := by
      simp [CriticalLinePhasor.FoliatedPolarization.feReflect]
    have him' : (CriticalLinePhasor.FoliatedPolarization.feReflect ρ).im
        = ρ.im := by
      simp [CriticalLinePhasor.FoliatedPolarization.feReflect]
    refine ⟨hball_mem _ hmem' (by rw [him']; exact hwin) ?_, hmem'.2.2⟩
    rw [hre']
    push_neg at hρW
    linarith [hρW.2]
  linarith

/-- Conjugation preserves the nontrivial-zero set. -/
theorem conj_mem_NontrivialZeros {ρ : ℂ} (hρ : ρ ∈ ZD.NontrivialZeros) :
    (starRingEnd ℂ) ρ ∈ ZD.NontrivialZeros := by
  refine ⟨by simpa using hρ.1, by simpa using hρ.2.1, ?_⟩
  rw [riemannZeta_conj, hρ.2.2, map_zero]

set_option maxHeartbeats 1600000 in
/-- **R7c-2(i): the two-sided window count.**  For `T ≥ e⁴`, the zeros with
`||γ| − T| ≤ ½` (both signs of the ordinate) carry total `xiOrderNat` at
most `96·log T`. -/
theorem abs_window_xiOrderNat_count {T : ℝ} (hT : Real.exp 4 ≤ T) :
    ∃ W : Finset ℂ,
      (∀ ρ : ℂ, ρ ∈ W ↔ ρ ∈ ZD.NontrivialZeros ∧ |(|ρ.im| - T)| ≤ 1/2) ∧
      (∑ ρ ∈ W, (ZD.xiOrderNat ρ : ℝ)) ≤ 96 * Real.log T := by
  have hTpos : (0:ℝ) < T := lt_of_lt_of_le (Real.exp_pos 4) hT
  obtain ⟨W₀, hW₀mem, hW₀⟩ := window_xiOrderNat_count hT
  have hfin : {ρ : ℂ | ρ ∈ ZD.NontrivialZeros ∧ |(|ρ.im| - T)| ≤ 1/2}.Finite := by
    apply Set.Finite.subset
      (ZD.ZeroCount.NontrivialZeros_inter_closedBall_finite (T + 2))
    rintro ρ ⟨hρ, hwin⟩
    refine ⟨hρ, ?_⟩
    rw [Metric.mem_closedBall, dist_zero_right]
    have him : |ρ.im| ≤ T + 1/2 := by
      rw [abs_le] at hwin
      linarith [hwin.2]
    calc ‖ρ‖ ≤ |ρ.re| + |ρ.im| := Complex.norm_le_abs_re_add_abs_im ρ
      _ ≤ 1 + (T + 1/2) := by
          apply add_le_add _ him
          rw [abs_of_pos hρ.1]
          exact le_of_lt hρ.2.1
      _ ≤ T + 2 := by linarith
  refine ⟨hfin.toFinset, fun ρ => by rw [Set.Finite.mem_toFinset]; rfl, ?_⟩
  set W := hfin.toFinset with hWdef
  have hWmem : ∀ ρ ∈ W, ρ ∈ ZD.NontrivialZeros ∧ |(|ρ.im| - T)| ≤ 1/2 := by
    intro ρ hρ
    rwa [hWdef, Set.Finite.mem_toFinset] at hρ
  have hnn : ∀ ρ : ℂ, (0:ℝ) ≤ (ZD.xiOrderNat ρ : ℝ) :=
    fun ρ => Nat.cast_nonneg _
  rw [← Finset.sum_filter_add_sum_filter_not W (fun ρ => 0 ≤ ρ.im)]
  -- positive ordinates sit in the one-sided window
  have hplus : (∑ ρ ∈ W.filter (fun ρ => 0 ≤ ρ.im),
      (ZD.xiOrderNat ρ : ℝ)) ≤ 48 * Real.log T := by
    calc (∑ ρ ∈ W.filter (fun ρ => 0 ≤ ρ.im), (ZD.xiOrderNat ρ : ℝ))
        ≤ ∑ ρ ∈ W₀, (ZD.xiOrderNat ρ : ℝ) := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro ρ hρ
            rw [Finset.mem_filter] at hρ
            obtain ⟨hρm, hwin⟩ := hWmem ρ hρ.1
            rw [hW₀mem]
            refine ⟨hρm, ?_⟩
            rwa [abs_of_nonneg hρ.2] at hwin
          · intro ρ _ _
            exact hnn ρ
      _ ≤ 48 * Real.log T := hW₀
  -- negative ordinates map in by conjugation
  have hminus : (∑ ρ ∈ W.filter (fun ρ => ¬ 0 ≤ ρ.im),
      (ZD.xiOrderNat ρ : ℝ)) ≤ 48 * Real.log T := by
    have hrefl : (∑ ρ ∈ W.filter (fun ρ => ¬ 0 ≤ ρ.im),
        (ZD.xiOrderNat ρ : ℝ))
        = ∑ u ∈ (W.filter (fun ρ => ¬ 0 ≤ ρ.im)).image (starRingEnd ℂ),
          (ZD.xiOrderNat u : ℝ) := by
      rw [Finset.sum_image]
      · apply Finset.sum_congr rfl
        intro ρ _
        rw [CriticalLinePhasor.FoliatedGlobalPolarization.xiOrderNat_conj]
      · intro a _ b _ h
        have h2 := congrArg (starRingEnd ℂ) h
        simpa [Complex.conj_conj] using h2
    calc (∑ ρ ∈ W.filter (fun ρ => ¬ 0 ≤ ρ.im), (ZD.xiOrderNat ρ : ℝ))
        = ∑ u ∈ (W.filter (fun ρ => ¬ 0 ≤ ρ.im)).image (starRingEnd ℂ),
            (ZD.xiOrderNat u : ℝ) := hrefl
      _ ≤ ∑ ρ ∈ W₀, (ZD.xiOrderNat ρ : ℝ) := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro u hu
            rw [Finset.mem_image] at hu
            obtain ⟨ρ, hρW, rfl⟩ := hu
            rw [Finset.mem_filter] at hρW
            obtain ⟨hρm, hwin⟩ := hWmem ρ hρW.1
            rw [hW₀mem]
            refine ⟨conj_mem_NontrivialZeros hρm, ?_⟩
            have him : ((starRingEnd ℂ) ρ).im = -ρ.im := Complex.conj_im ρ
            rw [him]
            push_neg at hρW
            rwa [abs_of_neg hρW.2] at hwin
          · intro ρ _ _
            exact hnn ρ
      _ ≤ 48 * Real.log T := hW₀
  linarith

set_option maxHeartbeats 3200000 in
/-- **R7c-2(ii): the explicit tail decay.**  For `H ≥ e⁴ + 1`, the counting
tail of the band floor obeys
`τ(H) = Σ'_{|γ|>H} xiOrderNat/‖ρ‖² ≤ 400·(log H + 1)/H`.
Fiberwise partition by `⌊|γ|−H⌋₊`, the two-sided window count per fiber,
and the `σ = 2` log-telescope. -/
theorem tail_tau_bound {H : ℝ} (hH : Real.exp 4 + 1 ≤ H) :
    (∑' x : {ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros} // H < |ρ.val.im|},
        (ZD.xiOrderNat x.val.val : ℝ) / ‖x.val.val‖ ^ 2)
      ≤ 400 * (Real.log H + 1) / H := by
  have hE4 : (50:ℝ) ≤ Real.exp 4 := by
    have he2 : (7.38:ℝ) ≤ Real.exp 1 * Real.exp 1 := by
      nlinarith [Real.exp_one_gt_d9]
    have h4 : Real.exp 4 = Real.exp 1 * Real.exp 1
        * (Real.exp 1 * Real.exp 1) := by
      rw [← Real.exp_add, ← Real.exp_add]
      norm_num
    nlinarith [he2, Real.exp_pos 1]
  have hHpos : (0:ℝ) < H := by linarith
  have hH51 : (51:ℝ) ≤ H := by linarith
  have hlogH : (0:ℝ) ≤ Real.log H :=
    Real.log_nonneg (by linarith)
  -- the Φ-potential at σ = 2
  set Φ : ℝ → ℝ := fun x =>
    -(x ^ ((1:ℝ)-2) * (((2:ℝ)-1) * Real.log x + 1)) / ((2:ℝ)-1)^2
    with hΦdef
  have hΦ_nonpos : ∀ x : ℝ, 1 ≤ x → Φ x ≤ 0 := by
    intro x hx
    rw [hΦdef]
    dsimp only
    apply div_nonpos_of_nonpos_of_nonneg _ (by norm_num)
    simp only [neg_nonpos]
    have h1 := Real.log_nonneg hx
    have h2 : (0:ℝ) ≤ x ^ ((1:ℝ)-2) := Real.rpow_nonneg (by linarith) _
    nlinarith
  have hΦ_floor : -Φ (H-1) ≤ 2 * (Real.log H + 1) / H := by
    rw [hΦdef]
    dsimp only
    rw [neg_div, neg_neg]
    have hH1pos : (0:ℝ) < H - 1 := by linarith
    have hrp : (H-1) ^ ((1:ℝ)-2) = (H-1)⁻¹ := by
      rw [show ((1:ℝ)-2) = -1 by norm_num, Real.rpow_neg_one]
    rw [hrp]
    have hlog1 : Real.log (H-1) ≤ Real.log H :=
      Real.log_le_log hH1pos (by linarith)
    have hinv : (H-1)⁻¹ ≤ 2/H := by
      rw [inv_le_iff_one_le_mul₀ hH1pos]
      rw [div_mul_eq_mul_div, le_div_iff₀ hHpos]
      nlinarith
    calc (H-1)⁻¹ * (((2:ℝ)-1) * Real.log (H-1) + 1) / ((2:ℝ)-1)^2
        = (H-1)⁻¹ * (Real.log (H-1) + 1) := by norm_num
      _ ≤ (2/H) * (Real.log H + 1) := by
          apply mul_le_mul hinv (by linarith)
            (by
              have := Real.log_nonneg (show (1:ℝ) ≤ H - 1 by linarith)
              linarith)
            (by positivity)
      _ = 2 * (Real.log H + 1) / H := by ring
  -- the telescoped partial sums
  have htel : ∀ K : ℕ, (∑ k ∈ Finset.range K,
      ((H + k) ^ (-(2:ℝ)) * Real.log (H + k + 1)))
      ≤ 2 * (2 * (Real.log H + 1) / H) := by
    intro K
    -- log(H+k+1) ≤ 2·log(H+k)
    have hdouble : ∀ k : ℕ, Real.log (H + k + 1) ≤ 2 * Real.log (H + k) := by
      intro k
      have hk0 : (0:ℝ) ≤ (k:ℝ) := Nat.cast_nonneg k
      have h1 : H + k + 1 ≤ (H + k)^2 := by nlinarith
      calc Real.log (H + k + 1) ≤ Real.log ((H + k)^2) :=
          Real.log_le_log (by linarith) h1
        _ = 2 * Real.log (H + k) := by
            rw [show ((H:ℝ) + k)^2 = (H+k)^(2:ℕ) by norm_num, Real.log_pow]
            push_cast
            ring
    -- strengthened telescoping invariant
    have hkey : ∀ K : ℕ, (∑ k ∈ Finset.range K,
        ((H + k) ^ (-(2:ℝ)) * Real.log (H + k)))
        ≤ Φ (H + K - 1) - Φ (H - 1) := by
      intro K
      induction K with
      | zero =>
        simp
      | succ M ih =>
        rw [Finset.sum_range_succ]
        have hstep : (H + M) ^ (-(2:ℝ)) * Real.log (H + M)
            ≤ Φ (H + M) - Φ (H + M - 1) := by
          have := log_rpow_unit_telescope_le
            (a := H + (M:ℝ) - 1) (σ := 2)
            (by
              have : (0:ℝ) ≤ (M:ℝ) := Nat.cast_nonneg M
              linarith)
            (by norm_num)
          have hrw : H + (M:ℝ) - 1 + 1 = H + M := by ring
          rw [hrw] at this
          rw [hΦdef]
          dsimp only
          exact this
        have hcast : H + ((M:ℕ) + 1 : ℕ) - 1 = H + M := by
          push_cast
          ring
        rw [hcast]
        have hcast2 : Φ (H + (M:ℝ)) = Φ (H + M) := rfl
        linarith [ih, hstep]
    calc (∑ k ∈ Finset.range K,
        ((H + k) ^ (-(2:ℝ)) * Real.log (H + k + 1)))
        ≤ ∑ k ∈ Finset.range K,
            (2 * ((H + k) ^ (-(2:ℝ)) * Real.log (H + k))) := by
          apply Finset.sum_le_sum
          intro k _
          have hk0 : (0:ℝ) ≤ (k:ℝ) := Nat.cast_nonneg k
          have hrpnn : (0:ℝ) ≤ (H + k) ^ (-(2:ℝ)) :=
            Real.rpow_nonneg (by linarith) _
          calc (H + k) ^ (-(2:ℝ)) * Real.log (H + k + 1)
              ≤ (H + k) ^ (-(2:ℝ)) * (2 * Real.log (H + k)) :=
                mul_le_mul_of_nonneg_left (hdouble k) hrpnn
            _ = 2 * ((H + k) ^ (-(2:ℝ)) * Real.log (H + k)) := by ring
      _ = 2 * ∑ k ∈ Finset.range K,
            ((H + k) ^ (-(2:ℝ)) * Real.log (H + k)) := by
          rw [Finset.mul_sum]
      _ ≤ 2 * (Φ (H + K - 1) - Φ (H - 1)) := by
          have := hkey K
          linarith
      _ ≤ 2 * (2 * (Real.log H + 1) / H) := by
          have h1 : Φ (H + K - 1) ≤ 0 := by
            apply hΦ_nonpos
            have : (0:ℝ) ≤ (K:ℝ) := Nat.cast_nonneg K
            linarith
          linarith [hΦ_floor]
  -- every finite partial sum obeys the bound
  apply Real.tsum_le_of_sum_le (fun x => by positivity)
  intro F
  -- fiber index
  set κ : {ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros} // H < |ρ.val.im|} → ℕ :=
    fun x => ⌊|x.val.val.im| - H⌋₊ with hκdef
  have hfib := Finset.sum_fiberwise_of_maps_to
    (g := κ) (t := F.image κ)
    (fun x hx => Finset.mem_image_of_mem κ hx)
    (fun x => (ZD.xiOrderNat x.val.val : ℝ) / ‖x.val.val‖ ^ 2)
  rw [← hfib]
  -- the per-fiber bound
  have hfiber : ∀ k ∈ F.image κ,
      (∑ x ∈ F.filter (fun x => κ x = k),
        (ZD.xiOrderNat x.val.val : ℝ) / ‖x.val.val‖ ^ 2)
      ≤ (H + k) ^ (-(2:ℝ)) * (96 * Real.log (H + k + 1)) := by
    intro k _
    have hk0 : (0:ℝ) ≤ (k:ℝ) := Nat.cast_nonneg k
    have hHk : (0:ℝ) < H + k := by linarith
    -- each fiber member has |γ| ≥ H + k and |γ| ∈ the T_k window
    have hmem_facts : ∀ x ∈ F.filter (fun x => κ x = k),
        H + k ≤ |x.val.val.im| ∧ |x.val.val.im| < H + k + 1 := by
      intro x hx
      rw [Finset.mem_filter] at hx
      have hfloor := hx.2
      rw [hκdef] at hfloor
      have hpos : (0:ℝ) ≤ |x.val.val.im| - H := by
        have := x.property
        linarith [le_of_lt this]
      have hfl : ⌊|x.val.val.im| - H⌋₊ = k := hfloor
      constructor
      · have h1 := Nat.floor_le hpos
        rw [hfl] at h1
        linarith
      · have h1 := Nat.lt_floor_add_one (|x.val.val.im| - H)
        rw [hfl] at h1
        linarith
    -- termwise: divide by (H+k)²
    have hterm : ∀ x ∈ F.filter (fun x => κ x = k),
        (ZD.xiOrderNat x.val.val : ℝ) / ‖x.val.val‖ ^ 2
        ≤ (ZD.xiOrderNat x.val.val : ℝ) * ((H + k) ^ (2:ℕ))⁻¹ := by
      intro x hx
      obtain ⟨hlow, _⟩ := hmem_facts x hx
      have hnorm : H + k ≤ ‖x.val.val‖ := by
        calc H + k ≤ |x.val.val.im| := hlow
          _ ≤ ‖x.val.val‖ := Complex.abs_im_le_norm _
      have hsq : (H + k) ^ (2:ℕ) ≤ ‖x.val.val‖ ^ 2 := by
        have := pow_le_pow_left₀ (by linarith) hnorm 2
        simpa using this
      rw [div_eq_mul_inv]
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      rw [← one_div, ← one_div]
      exact one_div_le_one_div_of_le (by positivity) hsq
    -- the fiber's multiplicity total via the window count
    obtain ⟨W, hWmem, hWbound⟩ := abs_window_xiOrderNat_count
      (T := H + k + 1/2) (by linarith)
    have hsub : (F.filter (fun x => κ x = k)).image
        (fun x => x.val.val) ⊆ W := by
      intro u hu
      rw [Finset.mem_image] at hu
      obtain ⟨x, hx, rfl⟩ := hu
      obtain ⟨hlow, hup⟩ := hmem_facts x hx
      rw [hWmem]
      refine ⟨x.val.property, ?_⟩
      rw [abs_le]
      constructor <;> linarith
    have hinj : Set.InjOn (fun x : {ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros} //
        H < |ρ.val.im|} => x.val.val) (F.filter (fun x => κ x = k)) := by
      intro a _ b _ h
      exact Subtype.ext (Subtype.ext h)
    have hcount : (∑ x ∈ F.filter (fun x => κ x = k),
        (ZD.xiOrderNat x.val.val : ℝ))
        ≤ 96 * Real.log (H + k + 1/2) := by
      calc (∑ x ∈ F.filter (fun x => κ x = k),
          (ZD.xiOrderNat x.val.val : ℝ))
          = ∑ u ∈ (F.filter (fun x => κ x = k)).image (fun x => x.val.val),
              (ZD.xiOrderNat u : ℝ) :=
            (Finset.sum_image (f := fun u : ℂ => (ZD.xiOrderNat u : ℝ))
              (fun a ha b hb h => hinj ha hb h)).symm
        _ ≤ ∑ u ∈ W, (ZD.xiOrderNat u : ℝ) := by
            apply Finset.sum_le_sum_of_subset_of_nonneg hsub
            intro u _ _
            exact Nat.cast_nonneg _
        _ ≤ 96 * Real.log (H + k + 1/2) := hWbound
    calc (∑ x ∈ F.filter (fun x => κ x = k),
        (ZD.xiOrderNat x.val.val : ℝ) / ‖x.val.val‖ ^ 2)
        ≤ ∑ x ∈ F.filter (fun x => κ x = k),
            (ZD.xiOrderNat x.val.val : ℝ) * ((H + k) ^ (2:ℕ))⁻¹ :=
          Finset.sum_le_sum hterm
      _ = (∑ x ∈ F.filter (fun x => κ x = k),
            (ZD.xiOrderNat x.val.val : ℝ)) * ((H + k) ^ (2:ℕ))⁻¹ := by
          rw [← Finset.sum_mul]
      _ ≤ (96 * Real.log (H + k + 1/2)) * ((H + k) ^ (2:ℕ))⁻¹ := by
          apply mul_le_mul_of_nonneg_right hcount (by positivity)
      _ ≤ (H + k) ^ (-(2:ℝ)) * (96 * Real.log (H + k + 1)) := by
          have hrp : (H + k) ^ (-(2:ℝ)) = ((H + k) ^ (2:ℕ))⁻¹ := by
            rw [Real.rpow_neg hHk.le, Real.rpow_two]
          rw [hrp]
          have hlog_mono : Real.log (H + k + 1/2) ≤ Real.log (H + k + 1) :=
            Real.log_le_log (by linarith) (by linarith)
          have hlognn : (0:ℝ) ≤ Real.log (H + k + 1/2) :=
            Real.log_nonneg (by linarith)
          have hp : (0:ℝ) ≤ ((H + k) ^ (2:ℕ))⁻¹ := by positivity
          nlinarith
  -- assemble: image-sum ≤ range-sum ≤ telescope
  set K : ℕ := (F.image κ).sup id + 1 with hK
  have himg_sub : F.image κ ⊆ Finset.range K := by
    intro k hk
    rw [Finset.mem_range, hK]
    have hle : k ≤ (F.image κ).sup id := Finset.le_sup (f := id) hk
    omega
  calc (∑ k ∈ F.image κ, ∑ x ∈ F.filter (fun x => κ x = k),
      (ZD.xiOrderNat x.val.val : ℝ) / ‖x.val.val‖ ^ 2)
      ≤ ∑ k ∈ F.image κ,
          ((H + k) ^ (-(2:ℝ)) * (96 * Real.log (H + k + 1))) :=
        Finset.sum_le_sum hfiber
    _ ≤ ∑ k ∈ Finset.range K,
          ((H + k) ^ (-(2:ℝ)) * (96 * Real.log (H + k + 1))) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg himg_sub
        intro k _ _
        have hk0 : (0:ℝ) ≤ (k:ℝ) := Nat.cast_nonneg k
        have h1 : (0:ℝ) ≤ (H + k) ^ (-(2:ℝ)) :=
          Real.rpow_nonneg (by linarith) _
        have h2 : (0:ℝ) ≤ Real.log (H + k + 1) :=
          Real.log_nonneg (by linarith)
        positivity
    _ = 96 * ∑ k ∈ Finset.range K,
          ((H + k) ^ (-(2:ℝ)) * Real.log (H + k + 1)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k _
        ring
    _ ≤ 96 * (2 * (2 * (Real.log H + 1) / H)) := by
        apply mul_le_mul_of_nonneg_left (htel K) (by norm_num)
    _ ≤ 400 * (Real.log H + 1) / H := by
        rw [show (96:ℝ) * (2 * (2 * (Real.log H + 1) / H))
          = 384 * (Real.log H + 1) / H by ring]
        apply div_le_div_of_nonneg_right _ hHpos.le
        nlinarith

/-- **The QUANTITATIVE band floor.**  If every zero of height ≤ `H` is on
the line (`H ≥ e⁴+1`), then at every admissible near-line strip anchor of
height ≤ `H/2` with a zero within unit horizontal distance, the seat energy
is at least `4/5 − 3200·(log H + 1)/H` — an explicit floor converging to
`4/5` as the verified band grows. -/
theorem seat_energy_ge_quantitative_floor {H : ℝ}
    (hH : Real.exp 4 + 1 ≤ H)
    (hon : ∀ ρ ∈ ZD.NontrivialZeros, |ρ.im| ≤ H → ρ.re = 1 / 2)
    {w : ℂ}
    (hw : (1 / 2 + Complex.I * w) ∉ ZD.NontrivialZeros)
    (hw' : (1 / 2 + Complex.I * (starRingEnd ℂ) w) ∉ ZD.NontrivialZeros)
    (hwim : w - (starRingEnd ℂ) w ≠ 0)
    (hre : |w.re| ≤ H / 2) (himw : |w.im| ≤ 1 / 2)
    {ρ₁ : ℂ} (hρ₁ : ρ₁ ∈ ZD.NontrivialZeros) (hρ₁h : |ρ₁.im| ≤ H)
    (hnear : |ρ₁.im - w.re| ≤ 1) :
    4 / 5 - 3200 * (Real.log H + 1) / H
      ≤ (∑' ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros},
          (ZD.xiOrderNat ρ.val : ℂ) *
            ((CriticalLinePhasor.HilbertPolya.spectralCoord ρ.val - w)⁻¹ *
              (CriticalLinePhasor.HilbertPolya.spectralCoord ρ.val
                - (starRingEnd ℂ) w)⁻¹)).re := by
  have hE4 : (50:ℝ) ≤ Real.exp 4 := by
    have he2 : (7.38:ℝ) ≤ Real.exp 1 * Real.exp 1 := by
      nlinarith [Real.exp_one_gt_d9]
    have h4 : Real.exp 4 = Real.exp 1 * Real.exp 1
        * (Real.exp 1 * Real.exp 1) := by
      rw [← Real.exp_add, ← Real.exp_add]
      norm_num
    nlinarith [he2, Real.exp_pos 1]
  have hfloor := seat_energy_ge_floor_of_band_online
    (H := H) (by linarith) hon hw hw' hwim hre himw hρ₁ hρ₁h hnear
  have htau := tail_tau_bound hH
  have h8 : (3200:ℝ) * (Real.log H + 1) / H
      = 8 * (400 * (Real.log H + 1) / H) := by
    ring
  linarith

/-- **The full-depth local rung.**  At any admissible anchor whose UNIT
WINDOW is verified on-line — every zero within horizontal distance ½ of the
anchor height has `β = ½` — the seat energy is nonnegative at EVERY depth.
The ladder's remaining content is exactly this window hypothesis at all
heights: locally verified windows buy full-depth positivity outright. -/
theorem seat_rung_of_window_online {w : ℂ}
    (hon : ∀ ρ ∈ ZD.NontrivialZeros, |ρ.im - w.re| < 1/2 → ρ.re = 1/2)
    (hw : (1/2 + Complex.I * w) ∉ ZD.NontrivialZeros)
    (hw' : (1/2 + Complex.I * (starRingEnd ℂ) w) ∉ ZD.NontrivialZeros)
    (hwim : w - (starRingEnd ℂ) w ≠ 0) :
    0 ≤ (∑' ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros},
        (ZD.xiOrderNat ρ.val : ℂ) *
          ((CriticalLinePhasor.HilbertPolya.spectralCoord ρ.val - w)⁻¹ *
            (CriticalLinePhasor.HilbertPolya.spectralCoord ρ.val
              - (starRingEnd ℂ) w)⁻¹)).re := by
  have hwindow := seat_energy_ge_window hw hw' hwim
  have hempty : IsEmpty {ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros} //
      |ρ.val.im - w.re| < 1 / 2 ∧ |w.im| < |ρ.val.re - 1 / 2|} := by
    constructor
    rintro ⟨⟨ρ, hρ⟩, hnear, hdeep⟩
    simp only at hnear hdeep
    have hre := hon ρ hρ hnear
    rw [hre] at hdeep
    simp at hdeep
    linarith [abs_nonneg w.im, hdeep]
  have hzero : (∑' x : {ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros} //
      |ρ.val.im - w.re| < 1 / 2 ∧ |w.im| < |ρ.val.re - 1 / 2|},
      (ZD.xiOrderNat x.val.val : ℂ) *
        ((CriticalLinePhasor.HilbertPolya.spectralCoord x.val.val - w)⁻¹ *
          (CriticalLinePhasor.HilbertPolya.spectralCoord x.val.val
            - (starRingEnd ℂ) w)⁻¹)) = 0 :=
    tsum_empty
  rw [hzero] at hwindow
  simpa using hwindow

set_option maxHeartbeats 3200000 in
/-- **The WIDE-window band floor.**  Same as the compiled band floor but
with the near zero allowed at horizontal distance `W` (matching the
Backlund-density windows): the floor becomes `1/(W² + ¼) − 8·τ(H)`. -/
theorem seat_energy_ge_floor_of_band_online_wide {H W : ℝ} (hH : 2 ≤ H)
    (hW : 1 ≤ W)
    (hon : ∀ ρ ∈ ZD.NontrivialZeros, |ρ.im| ≤ H → ρ.re = 1 / 2)
    {w : ℂ}
    (hw : (1 / 2 + Complex.I * w) ∉ ZD.NontrivialZeros)
    (hw' : (1 / 2 + Complex.I * (starRingEnd ℂ) w) ∉ ZD.NontrivialZeros)
    (hwim : w - (starRingEnd ℂ) w ≠ 0)
    (hre : |w.re| ≤ H / 2) (himw : |w.im| ≤ 1 / 2)
    {ρ₁ : ℂ} (hρ₁ : ρ₁ ∈ ZD.NontrivialZeros) (hρ₁h : |ρ₁.im| ≤ H)
    (hnear : |ρ₁.im - w.re| ≤ W) :
    1 / (W^2 + 1/4)
      - 8 * (∑' x : {ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros} // H < |ρ.val.im|},
        (ZD.xiOrderNat x.val.val : ℝ) / ‖x.val.val‖ ^ 2)
      ≤ (∑' ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros},
          (ZD.xiOrderNat ρ.val : ℂ) *
            ((spectralCoord ρ.val - w)⁻¹ *
              (spectralCoord ρ.val - (starRingEnd ℂ) w)⁻¹)).re := by
  classical
  set f : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros} → ℂ := fun ρ =>
    (ZD.xiOrderNat ρ.val : ℂ) *
      ((spectralCoord ρ.val - w)⁻¹ *
        (spectralCoord ρ.val - (starRingEnd ℂ) w)⁻¹) with hf
  have hsumm : Summable f := summable_seat_energy hw hw' hwim
  set s : Set {ρ : ℂ // ρ ∈ ZD.NontrivialZeros} := {ρ | H < |ρ.val.im|}
    with hs
  have hsum_s : Summable fun x : s => f x.val := hsumm.subtype _
  have hsum_sc : Summable fun x : ↑sᶜ => f x.val := hsumm.subtype _
  have hsplit : (∑' x : s, f x.val) + (∑' x : ↑sᶜ, f x.val) = ∑' x, f x :=
    hsum_s.tsum_add_tsum_compl hsum_sc
  have hbelow_term : ∀ x : ↑sᶜ,
      f x.val = ((ZD.xiOrderNat x.val.val : ℝ) *
        (Complex.normSq (spectralCoord x.val.val - w))⁻¹ : ℝ) := by
    rintro ⟨ρ, hρc⟩
    have hband : |ρ.val.im| ≤ H := by
      have := hρc
      simp only [hs, Set.mem_compl_iff, Set.mem_setOf_eq, not_lt] at this
      exact this
    have honρ : ρ.val.re = 1 / 2 := hon ρ.val ρ.2 hband
    have hreal : (starRingEnd ℂ) (spectralCoord ρ.val)
        = spectralCoord ρ.val :=
      spectralCoord_real_of_online honρ
    have hfac : spectralCoord ρ.val - (starRingEnd ℂ) w
        = (starRingEnd ℂ) (spectralCoord ρ.val - w) := by
      rw [map_sub, hreal]
    simp only [hf]
    rw [hfac, ← map_inv₀, Complex.mul_conj, Complex.normSq_inv]
    push_cast
    ring
  have hbelow_nonneg : ∀ x : ↑sᶜ, 0 ≤ (f x.val).re := by
    intro x
    rw [hbelow_term x, Complex.ofReal_re]
    exact mul_nonneg (Nat.cast_nonneg _)
      (inv_nonneg.mpr (Complex.normSq_nonneg _))
  set P₁ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros} := ⟨ρ₁, hρ₁⟩ with hP₁
  have hP₁mem : P₁ ∈ sᶜ := by
    simp only [hs, Set.mem_compl_iff, Set.mem_setOf_eq, not_lt, hP₁]
    exact hρ₁h
  have hterm₁ : 1 / (W^2 + 1/4) ≤ (f P₁).re := by
    have honρ₁ : ρ₁.re = 1 / 2 := hon ρ₁ hρ₁ hρ₁h
    have hns : Complex.normSq (spectralCoord ρ₁ - w) ≤ W^2 + 1/4 := by
      have hre₁ : (spectralCoord ρ₁ - w).re = ρ₁.im - w.re := by
        rw [Complex.sub_re, spectralCoord_re]
      have him₁ : |(spectralCoord ρ₁ - w).im| ≤ 1 / 2 := by
        rw [Complex.sub_im]
        have : (spectralCoord ρ₁).im = 0 := by
          have := spectralCoord_real_of_online honρ₁
          rw [Complex.conj_eq_iff_im] at this
          exact this
        rw [this, zero_sub, abs_neg]
        exact himw
      rw [Complex.normSq_apply]
      have h1 : (spectralCoord ρ₁ - w).re ^ 2 ≤ W^2 := by
        rw [hre₁]
        nlinarith [hnear, sq_abs (ρ₁.im - w.re), abs_nonneg (ρ₁.im - w.re)]
      have h2 : (spectralCoord ρ₁ - w).im ^ 2 ≤ 1 / 4 := by
        nlinarith [him₁, sq_abs (spectralCoord ρ₁ - w).im,
          abs_nonneg (spectralCoord ρ₁ - w).im]
      nlinarith [h1, h2]
    have hnspos : 0 < Complex.normSq (spectralCoord ρ₁ - w) := by
      rw [Complex.normSq_pos]
      rw [sub_ne_zero]
      intro h
      have := spectral_sub_ne hw P₁
      rw [hP₁] at this
      exact this (by rw [← h]; ring)
    have hm₁ : (1:ℝ) ≤ (ZD.xiOrderNat ρ₁ : ℝ) := by
      exact_mod_cast ZD.xiOrderNat_pos_of_mem_NontrivialZeros hρ₁
    have hb : 1 / (W^2 + 1/4)
        ≤ (Complex.normSq (spectralCoord ρ₁ - w))⁻¹ := by
      rw [← one_div]
      exact one_div_le_one_div_of_le hnspos hns
    have := hbelow_term ⟨P₁, hP₁mem⟩
    rw [this, Complex.ofReal_re]
    calc 1 / (W^2 + 1/4)
        ≤ (Complex.normSq (spectralCoord ρ₁ - w))⁻¹ := hb
      _ ≤ (ZD.xiOrderNat ρ₁ : ℝ)
          * (Complex.normSq (spectralCoord ρ₁ - w))⁻¹ := by
          nlinarith [hb, hm₁,
            inv_nonneg.mpr (Complex.normSq_nonneg
              (spectralCoord ρ₁ - w))]
  have hbelow_ge : 1 / (W^2 + 1/4) ≤ (∑' x : ↑sᶜ, f x.val).re := by
    have hre_summ : Summable fun x : ↑sᶜ => (f x.val).re :=
      (Complex.hasSum_re hsum_sc.hasSum).summable
    rw [Complex.re_tsum hsum_sc]
    calc 1 / (W^2 + 1/4) ≤ (f P₁).re := hterm₁
      _ ≤ ∑' x : ↑sᶜ, (f x.val).re :=
          hre_summ.le_tsum ⟨P₁, hP₁mem⟩ fun j _ => hbelow_nonneg j
  have habove : -(8 * (∑' x : {ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros} //
      H < |ρ.val.im|},
      (ZD.xiOrderNat x.val.val : ℝ) / ‖x.val.val‖ ^ 2))
      ≤ (∑' x : s, f x.val).re := by
    have h1 : |(∑' x : s, f x.val).re| ≤ ‖∑' x : s, f x.val‖ :=
      Complex.abs_re_le_norm _
    have h2 := seat_tail_tsum_le (w := w) hH hre
    have h3 : ‖∑' x : s, f x.val‖
        ≤ 8 * (∑' x : {ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros} //
          H < |ρ.val.im|},
          (ZD.xiOrderNat x.val.val : ℝ) / ‖x.val.val‖ ^ 2) := h2
    have := abs_le.mp (le_trans h1 h3)
    linarith [this.1]
  have htot : (∑' x, f x).re
      = (∑' x : s, f x.val).re + (∑' x : ↑sᶜ, f x.val).re := by
    rw [← hsplit, Complex.add_re]
  rw [htot]
  linarith [hbelow_ge, habove]

/-- **The HYPOTHESIS-FREE band floor.**  The RvM lower density discharges
the per-anchor near-zero input: above the density threshold, band
verification to height `H` alone buys the explicit seat floor
`1/(300² + ¼) − 8·τ(H)` at every admissible near-line anchor in the range.
No per-anchor hypothesis remains. -/
theorem seat_energy_ge_floor_of_band_online_auto :
    ∃ T₀ : ℝ, 0 ≤ T₀ ∧ ∀ H : ℝ, 2 ≤ H →
    (∀ ρ ∈ ZD.NontrivialZeros, |ρ.im| ≤ H → ρ.re = 1/2) →
    ∀ w : ℂ,
    (1/2 + Complex.I * w) ∉ ZD.NontrivialZeros →
    (1/2 + Complex.I * (starRingEnd ℂ) w) ∉ ZD.NontrivialZeros →
    (w - (starRingEnd ℂ) w ≠ 0) →
    T₀ ≤ |w.re| → |w.re| ≤ H/2 - 301 → |w.im| ≤ 1/2 →
    1/(300^2 + 1/4)
      - 8 * (∑' x : {ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros} //
          H < |ρ.val.im|},
        (ZD.xiOrderNat x.val.val : ℝ) / ‖x.val.val‖ ^ 2)
      ≤ (∑' ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros},
          (ZD.xiOrderNat ρ.val : ℂ) *
            ((spectralCoord ρ.val - w)⁻¹ *
              (spectralCoord ρ.val - (starRingEnd ℂ) w)⁻¹)).re := by
  obtain ⟨T₀, hdens⟩ := exists_zero_near_height
  refine ⟨max T₀ 1, le_trans zero_le_one (le_max_right _ _),
    fun H hH hon w hw hw' hwim hre hreu himw => ?_⟩
  have hreT₀ : T₀ ≤ |w.re| := le_trans (le_max_left _ _) hre
  have hre1 : (1:ℝ) ≤ |w.re| := le_trans (le_max_right _ _) hre
  -- the density supplies a zero near |w.re|
  obtain ⟨ρ₀, hρ₀mem, hρ₀pos, hρ₀near⟩ := hdens (|w.re|) hreT₀
  -- reflect for negative anchor heights
  rcases le_or_gt 0 w.re with hsign | hsign
  · -- positive: use ρ₀ directly
    rw [abs_of_nonneg hsign] at hρ₀near
    have hρ₀h : |ρ₀.im| ≤ H := by
      rw [abs_of_pos hρ₀pos]
      have := abs_le.mp hρ₀near
      have h1 : |w.re| = w.re := abs_of_nonneg hsign
      rw [h1] at hreu
      linarith [this.2]
    have hnear : |ρ₀.im - w.re| ≤ 300 := hρ₀near
    exact seat_energy_ge_floor_of_band_online_wide hH (by norm_num)
      hon hw hw' hwim (by linarith) himw hρ₀mem hρ₀h hnear
  · -- negative: use the conjugate zero
    rw [abs_of_neg hsign] at hρ₀near
    set ρ₁ : ℂ := (starRingEnd ℂ) ρ₀ with hρ₁def
    have hρ₁mem : ρ₁ ∈ ZD.NontrivialZeros := conj_mem_NontrivialZeros hρ₀mem
    have hρ₁im : ρ₁.im = -ρ₀.im := Complex.conj_im ρ₀
    have hρ₁h : |ρ₁.im| ≤ H := by
      rw [hρ₁im, abs_neg, abs_of_pos hρ₀pos]
      have := abs_le.mp hρ₀near
      have h1 : |w.re| = -w.re := abs_of_neg hsign
      rw [h1] at hreu
      linarith [this.2]
    have hnear : |ρ₁.im - w.re| ≤ 300 := by
      rw [hρ₁im]
      have : -ρ₀.im - w.re = -(ρ₀.im - (-w.re)) := by ring
      rw [this, abs_neg]
      exact hρ₀near
    exact seat_energy_ge_floor_of_band_online_wide hH (by norm_num)
      hon hw hw' hwim (by linarith) himw hρ₁mem hρ₁h hnear

/-- **R6′: THE INTERIOR POSITIVITY RUNG FROM HEIGHT e⁴ + 2 ≈ 57.**
The fixed-center region (`zero_free_region_exponent_one'`, threshold e⁴)
runs the empty deep-window argument from height `e⁴ + 2` instead of
`e³² + 2` — twelve orders of magnitude lower, same depth `½ − c/log`. -/
theorem seat_interior_rung_one' : ∃ c : ℝ, 0 < c ∧ ∀ w : ℂ,
    Real.exp 4 + 2 ≤ |w.re| →
    1/2 - c / Real.log (|w.re| + 1/2) ≤ |w.im| →
    ((1/2 + Complex.I * w) ∉ ZD.NontrivialZeros) →
    ((1/2 + Complex.I * (starRingEnd ℂ) w) ∉ ZD.NontrivialZeros) →
    (w - (starRingEnd ℂ) w ≠ 0) →
    0 ≤ (∑' ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros},
        (ZD.xiOrderNat ρ.val : ℂ) *
          ((CriticalLinePhasor.HilbertPolya.spectralCoord ρ.val - w)⁻¹ *
            (CriticalLinePhasor.HilbertPolya.spectralCoord ρ.val
              - (starRingEnd ℂ) w)⁻¹)).re := by
  obtain ⟨c, hcpos, hregion⟩ := zero_free_region_exponent_one'
  refine ⟨c, hcpos, fun w hre him hw hw' hwim => ?_⟩
  have hwindow := seat_energy_ge_window hw hw' hwim
  -- the deep-window is empty
  have hempty : IsEmpty {ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros} //
      |ρ.val.im - w.re| < 1 / 2 ∧ |w.im| < |ρ.val.re - 1 / 2|} := by
    constructor
    rintro ⟨⟨ρ, hρ⟩, hnear, hdeep⟩
    simp only at hnear hdeep
    set β : ℝ := ρ.re with hβdef
    set γ : ℝ := ρ.im with hγdef
    have hβ0 : 0 < β := hρ.1
    have hβ1' : β < 1 := hρ.2.1
    -- the ordinate is high
    have hγlb : |w.re| - 1/2 ≤ |γ| := by
      have h1 := abs_sub_abs_le_abs_sub w.re γ
      rw [abs_sub_comm γ w.re] at hnear
      linarith [hnear, h1]
    have hγ4 : Real.exp 4 ≤ |γ| := by linarith
    have hγub : |γ| ≤ |w.re| + 1/2 := by
      have h1 := abs_sub_abs_le_abs_sub γ w.re
      linarith [hnear, h1]
    set L : ℝ := Real.log |γ| with hLdef
    have hγpos : (0:ℝ) < |γ| := by linarith [Real.exp_pos 4]
    have hL4 : (4:ℝ) ≤ L := by
      rw [hLdef]
      have := Real.log_le_log (Real.exp_pos 4) hγ4
      rwa [Real.log_exp] at this
    have hLpos : (0:ℝ) < L := by linarith
    -- region: upper bound on β
    have hβup : β ≤ 1 - c / L := by
      have h := hregion ρ hρ.2.2 (by rw [← hγdef]; exact hγ4)
      rw [← hγdef, ← hLdef] at h
      rw [hβdef]
      exact h
    -- region at the FE partner: lower bound on β
    have hβlow : c / L ≤ β := by
      have hmem' :=
        CriticalLinePhasor.FoliatedGlobalPolarization.feReflect_mem hρ
      have hpt' : ((1 - β : ℝ) : ℂ) + I * γ
          = CriticalLinePhasor.FoliatedPolarization.feReflect ρ := by
        rw [CriticalLinePhasor.FoliatedPolarization.feReflect, hβdef, hγdef]
        apply Complex.ext <;> simp
      have hζ' : riemannZeta (((1 - β : ℝ) : ℂ) + I * γ) = 0 := by
        rw [hpt']
        exact hmem'.2.2
      have hpim : (((1 - β : ℝ) : ℂ) + I * γ).im = γ := by
        simp
      have hpre : (((1 - β : ℝ) : ℂ) + I * γ).re = 1 - β := by
        simp
      have h := hregion (((1 - β : ℝ) : ℂ) + I * γ) hζ'
        (by rw [hpim]; exact hγ4)
      rw [hpre, hpim, ← hLdef] at h
      linarith
    -- depth cap
    have hdepth_cap : |β - 1/2| ≤ 1/2 - c / L := by
      rw [abs_le]
      constructor <;> linarith
    -- the anchor is at least that deep
    have hΛ : L ≤ Real.log (|w.re| + 1/2) := by
      rw [hLdef]
      apply Real.log_le_log hγpos
      exact hγub
    have hmono : c / Real.log (|w.re| + 1/2) ≤ c / L :=
      div_le_div_of_nonneg_left (le_of_lt hcpos) hLpos hΛ
    have hanchor : |β - 1/2| ≤ |w.im| := by
      calc |β - 1/2| ≤ 1/2 - c / L := hdepth_cap
        _ ≤ 1/2 - c / Real.log (|w.re| + 1/2) := by linarith
        _ ≤ |w.im| := him
    rw [hβdef] at hanchor
    linarith [hdeep, hanchor]
  -- empty window ⟹ zero window sum ⟹ nonneg energy
  have hzero : (∑' x : {ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros} //
      |ρ.val.im - w.re| < 1 / 2 ∧ |w.im| < |ρ.val.re - 1 / 2|},
      (ZD.xiOrderNat x.val.val : ℂ) *
        ((CriticalLinePhasor.HilbertPolya.spectralCoord x.val.val - w)⁻¹ *
          (CriticalLinePhasor.HilbertPolya.spectralCoord x.val.val
            - (starRingEnd ℂ) w)⁻¹)) = 0 := by
    exact tsum_empty
  rw [hzero] at hwindow
  simpa using hwindow

/-- **The capstone, localized (a REDUCTION, not a closure).**  RH is
equivalent to seat positivity on the RESIDUAL domain only: anchors of
height `< e⁴ + 2 ≈ 57`, or of depth `< ½ − c/log(height + ½)`.  The
complement — high and deep — is covered unconditionally by
`seat_interior_rung_one'`.  This compiles exactly where the open content
lives; it does not diminish its strength. -/
theorem seat_criterion_residual_iff : ∃ c : ℝ, 0 < c ∧
    ((∀ ρ ∈ ZD.NontrivialZeros, ρ.re = 1 / 2)
      ↔ ∀ w : ℂ, ((1/2 + Complex.I * w) ∉ ZD.NontrivialZeros) →
          ((1/2 + Complex.I * (starRingEnd ℂ) w) ∉ ZD.NontrivialZeros) →
          (w - (starRingEnd ℂ) w ≠ 0) →
          (|w.re| < Real.exp 4 + 2 ∨
            |w.im| < 1/2 - c / Real.log (|w.re| + 1/2)) →
          0 ≤ (∑' ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros},
              (ZD.xiOrderNat ρ.val : ℂ) *
                ((CriticalLinePhasor.HilbertPolya.spectralCoord ρ.val - w)⁻¹ *
                  (CriticalLinePhasor.HilbertPolya.spectralCoord ρ.val
                    - (starRingEnd ℂ) w)⁻¹)).re) := by
  obtain ⟨c, hcpos, hrung⟩ := seat_interior_rung_one'
  refine ⟨c, hcpos, ?_⟩
  constructor
  · intro hon w hw hw' him _
    exact seat_criterion_iff.mp hon w hw hw' him
  · intro hres
    apply seat_criterion_iff.mpr
    intro w hw hw' him
    by_cases hcase : |w.re| < Real.exp 4 + 2 ∨
        |w.im| < 1/2 - c / Real.log (|w.re| + 1/2)
    · exact hres w hw hw' him hcase
    · push_neg at hcase
      exact hrung w hcase.1 hcase.2 hw hw' him

/-- **The capstone, factored (a REDUCTION, not a closure).**  RH is
equivalent to the conjunction of
(1) a FINITE statement — the zeros of ordinate `< e⁴ + 5/2 ≈ 57.1`
    (finitely many; classically eleven) lie on the line — and
(2) the shallow channel — seat positivity at anchors of height `≥ e⁴ + 2`
    and depth `< ½ − c/log(height + ½)`.
Low anchors are covered by (1) through the window law (an on-line window
zero has depth `0`, so the deep-window is empty at EVERY anchor depth);
high-and-deep anchors by `seat_interior_rung_one'`; high-and-shallow is
(2).  Item (2) carries the full open content. -/
theorem seat_criterion_split_iff : ∃ c : ℝ, 0 < c ∧
    ((∀ ρ ∈ ZD.NontrivialZeros, ρ.re = 1 / 2)
      ↔ ((∀ ρ ∈ ZD.NontrivialZeros,
            |ρ.im| < Real.exp 4 + 5/2 → ρ.re = 1 / 2) ∧
        ∀ w : ℂ, ((1/2 + Complex.I * w) ∉ ZD.NontrivialZeros) →
          ((1/2 + Complex.I * (starRingEnd ℂ) w) ∉ ZD.NontrivialZeros) →
          (w - (starRingEnd ℂ) w ≠ 0) →
          Real.exp 4 + 2 ≤ |w.re| →
          |w.im| < 1/2 - c / Real.log (|w.re| + 1/2) →
          0 ≤ (∑' ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros},
              (ZD.xiOrderNat ρ.val : ℂ) *
                ((CriticalLinePhasor.HilbertPolya.spectralCoord ρ.val - w)⁻¹ *
                  (CriticalLinePhasor.HilbertPolya.spectralCoord ρ.val
                    - (starRingEnd ℂ) w)⁻¹)).re)) := by
  obtain ⟨c, hcpos, hrung⟩ := seat_interior_rung_one'
  refine ⟨c, hcpos, ?_⟩
  constructor
  · intro hon
    exact ⟨fun ρ hρ _ => hon ρ hρ,
      fun w hw hw' him _ _ => seat_criterion_iff.mp hon w hw hw' him⟩
  · rintro ⟨hfin, hchan⟩
    apply seat_criterion_iff.mpr
    intro w hw hw' him
    by_cases hlow : |w.re| < Real.exp 4 + 2
    · -- the low strip: window zeros are on the line, deep-window empty
      have hwindow := seat_energy_ge_window hw hw' him
      have hempty : IsEmpty {ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros} //
          |ρ.val.im - w.re| < 1 / 2 ∧ |w.im| < |ρ.val.re - 1 / 2|} := by
        constructor
        rintro ⟨⟨ρ, hρ⟩, hnear, hdeep⟩
        simp only at hnear hdeep
        have hγlow : |ρ.im| < Real.exp 4 + 5/2 := by
          have h1 := abs_sub_abs_le_abs_sub ρ.im w.re
          linarith [hnear, h1]
        have hre := hfin ρ hρ hγlow
        rw [hre] at hdeep
        simp only [sub_self, abs_zero] at hdeep
        exact absurd hdeep (not_lt.mpr (abs_nonneg _))
      have hzero : (∑' x : {ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros} //
          |ρ.val.im - w.re| < 1 / 2 ∧ |w.im| < |ρ.val.re - 1 / 2|},
          (ZD.xiOrderNat x.val.val : ℂ) *
            ((CriticalLinePhasor.HilbertPolya.spectralCoord x.val.val - w)⁻¹ *
              (CriticalLinePhasor.HilbertPolya.spectralCoord x.val.val
                - (starRingEnd ℂ) w)⁻¹)) = 0 := by
        exact tsum_empty
      rw [hzero] at hwindow
      simpa using hwindow
    · push_neg at hlow
      by_cases hdeep : 1/2 - c / Real.log (|w.re| + 1/2) ≤ |w.im|
      · exact hrung w hlow hdeep hw hw' him
      · push_neg at hdeep
        exact hchan w hw hw' him hlow hdeep

end CriticalLinePhasor.DVP

section AxiomAudit
#print axioms CriticalLinePhasor.DVP.seat_interior_rung_one
#print axioms CriticalLinePhasor.DVP.seat_interior_rung_one'
#print axioms CriticalLinePhasor.DVP.seat_criterion_residual_iff
#print axioms CriticalLinePhasor.DVP.seat_criterion_split_iff
#print axioms CriticalLinePhasor.DVP.window_xiOrderNat_count
#print axioms CriticalLinePhasor.DVP.abs_window_xiOrderNat_count
#print axioms CriticalLinePhasor.DVP.tail_tau_bound
#print axioms CriticalLinePhasor.DVP.seat_energy_ge_quantitative_floor
#print axioms CriticalLinePhasor.DVP.seat_rung_of_window_online
#print axioms CriticalLinePhasor.DVP.seat_energy_ge_floor_of_band_online_wide
#print axioms CriticalLinePhasor.DVP.seat_energy_ge_floor_of_band_online_auto
end AxiomAudit
