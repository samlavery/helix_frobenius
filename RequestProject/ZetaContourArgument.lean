import RequestProject.StClockJumpLaw
import RequestProject.ZetaZeroDefs
import RequestProject.DifferencedResolvent
import RequestProject.ZetaBound
import RequestProject.ArgumentPrincipleAnalytic
import RequestProject.ContourLiftCalculus
import Mathlib.Analysis.Complex.CoveringMap
import Mathlib.Analysis.Complex.BranchLogRoot
import Mathlib.Analysis.Meromorphic.FactorizedRational
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Topology.ContinuousMap.Interval
import Mathlib.Topology.Homotopy.Lifting

/-!
# The independently continued argument of zeta

For a height which is not the ordinate of a nontrivial zero, this file constructs the
classical broken path

`2 → 2 + iT → 1/2 + iT`

and lifts its nonvanishing zeta image through `Complex.exp : ℂ → ℂˣ`.  The resulting
endpoint imaginary part is therefore a continued argument of `riemannZeta (1/2 + iT)` defined
from the contour itself.  In particular, neither `zeroEventCount`, `zeroEventCountMult`, `S`, nor
`Smult` occurs in its definition.
-/

open Complex ComplexConjugate Set Topology MeasureTheory

noncomputable section

namespace CriticalLinePhasor.ContourArgument

open CriticalLinePhasor CriticalLinePhasor.CarrierScale CriticalLinePhasor.ResidueJump
  CriticalLinePhasor.ResolventLimit

/-! ## Real structure of the completed function -/

/-- Mellin transforms of real-valued complex functions commute with conjugation of the
Mellin coordinate. -/
private theorem mellin_conj_of_real_values (f : ℝ → ℂ) (hf : ∀ x, conj (f x) = f x) (s : ℂ) :
    conj (mellin f s) = mellin f (conj s) := by
  unfold mellin
  rw [← integral_conj]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro x hx
  change conj ((x : ℂ) ^ (s - 1) * f x) = (x : ℂ) ^ (conj s - 1) * f x
  rw [map_mul, hf]
  have harg : (x : ℂ).arg ≠ Real.pi := by
    rw [show (x : ℂ) = (x : ℂ) * 1 by ring, Complex.arg_real_mul 1 hx]
    simp
    exact Real.pi_ne_zero.symm
  have hc : conj ((x : ℂ) ^ (s - 1)) = (x : ℂ) ^ conj (s - 1) := by
    simpa using (Complex.cpow_conj (x : ℂ) (s - 1) harg).symm
  rw [hc]
  simp

/-- The entire completed zeta function has real coefficients. -/
theorem completedRiemannZeta₀_conj (s : ℂ) :
    completedRiemannZeta₀ (conj s) = conj (completedRiemannZeta₀ s) := by
  change ((HurwitzZeta.hurwitzEvenFEPair 0).Λ₀ (conj s / 2)) / 2 =
    conj (((HurwitzZeta.hurwitzEvenFEPair 0).Λ₀ (s / 2)) / 2)
  rw [map_div₀, map_ofNat]
  congr 1
  unfold WeakFEPair.Λ₀
  rw [mellin_conj_of_real_values]
  · congr 2
    rw [map_div₀, map_ofNat]
  · intro x
    by_cases h1 : x ∈ Ioi (1 : ℝ) <;> by_cases h2 : x ∈ Ioo (0 : ℝ) 1 <;>
      simp [WeakFEPair.f_modif, HurwitzZeta.hurwitzEvenFEPair, h1, h2]

/-- Conjugation symmetry of the entire completed function. -/
theorem riemannXi_conj (s : ℂ) : ZD.riemannXi (conj s) = conj (ZD.riemannXi s) := by
  unfold ZD.riemannXi
  rw [completedRiemannZeta₀_conj]
  simp only [map_add, map_div₀, map_mul, map_sub, map_one, map_ofNat]

/-- Reflection in the critical line followed by conjugation fixes `riemannXi`. -/
theorem riemannXi_one_sub_conj (s : ℂ) :
    ZD.riemannXi (1 - conj s) = conj (ZD.riemannXi s) := by
  rw [ZD.ZeroCount.riemannXi_one_sub, riemannXi_conj]

/-- A height at which the horizontal part of the standard zeta contour meets no nontrivial
zero.  Positivity also keeps that horizontal segment away from the pole at `1`. -/
def GoodHeight (T : ℝ) : Prop :=
  0 < T ∧ ∀ ρ : ℂ, ρ ∈ ZD.NontrivialZeros → ρ.im ≠ T

/-- Every height below `2` is good.  This is the compiled zero-free base range used to
normalize the contour count. -/
theorem goodHeight_of_pos_of_lt_two {T : ℝ} (hT0 : 0 < T) (hT2 : T < 2) : GoodHeight T := by
  refine ⟨hT0, ?_⟩
  intro ρ hρ hρT
  have htriv : ∀ n : ℕ, ρ ≠ -2 * ((n : ℂ) + 1) := by
    intro n hn
    have hre := congrArg Complex.re hn
    simp at hre
    linarith [hρ.1]
  have him := riemannZeta_nontrivial_zero_im_ge_two hρ.2.2 htriv
  rw [abs_of_pos (hρT.symm ▸ hT0)] at him
  linarith

/-- The convenient unit-height base point is a good height. -/
theorem goodHeight_one : GoodHeight 1 :=
  goodHeight_of_pos_of_lt_two (by norm_num) (by norm_num)

/-! ## A normalized logarithm of the Archimedean factor -/

/-- The open right half-plane, on which `Gammaℝ` is holomorphic and nonvanishing. -/
def rightHalfPlane : Set ℂ := {s : ℂ | 0 < s.re}

private theorem rightHalfPlane_convex : Convex ℝ rightHalfPlane := by
  intro x hx y hy a b ha hb hab
  simp only [rightHalfPlane, Set.mem_setOf_eq] at hx hy ⊢
  rw [Complex.add_re, Complex.smul_re, Complex.smul_re]
  simp only [smul_eq_mul]
  by_cases ha0 : a = 0
  · subst a
    simp at hab
    subst b
    simpa using hy
  · have hapos : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
    exact add_pos_of_pos_of_nonneg (mul_pos hapos hx) (mul_nonneg hb hy.le)

private theorem rightHalfPlane_isSimplyConnected : IsSimplyConnected rightHalfPlane := by
  letI : ContractibleSpace rightHalfPlane :=
    rightHalfPlane_convex.contractibleSpace ⟨(1 : ℂ), by simp [rightHalfPlane]⟩
  exact SimplyConnectedSpace.ofContractible rightHalfPlane

private theorem rightHalfPlane_isOpen : IsOpen rightHalfPlane :=
  isOpen_lt continuous_const Complex.continuous_re

private theorem exists_gammaLogRaw :
    ∃ L : ℂ → ℂ, ContinuousOn L rightHalfPlane ∧
      ∀ s ∈ rightHalfPlane, Complex.exp (L s) = Gammaℝ s := by
  have hcont : ContinuousOn Gammaℝ rightHalfPlane := by
    intro s hs
    exact (gammaR_differentiableAt hs).continuousAt.continuousWithinAt
  have hzero : 0 ∉ Gammaℝ '' rightHalfPlane := by
    rintro ⟨s, hs, h⟩
    exact Gammaℝ_ne_zero_of_re_pos hs h
  obtain ⟨L, hL, hexp⟩ := Complex.exists_continuousOn_eqOn_exp_comp
    rightHalfPlane_isSimplyConnected rightHalfPlane_isOpen hcont hzero
  exact ⟨L, hL, fun s hs ↦ hexp hs⟩

/-- An arbitrary continuous logarithm of `Gammaℝ` on the right half-plane. -/
noncomputable def gammaLogRaw : ℂ → ℂ := exists_gammaLogRaw.choose

private theorem gammaLogRaw_continuousOn : ContinuousOn gammaLogRaw rightHalfPlane :=
  exists_gammaLogRaw.choose_spec.1

private theorem exp_gammaLogRaw {s : ℂ} (hs : s ∈ rightHalfPlane) :
    Complex.exp (gammaLogRaw s) = Gammaℝ s :=
  exists_gammaLogRaw.choose_spec.2 s hs

private theorem gammaR_two : Gammaℝ (2 : ℂ) = (1 / Real.pi : ℝ) := by
  rw [Gammaℝ_def]
  norm_num
  rw [Complex.cpow_neg, Complex.cpow_one]

/-- The right-half-plane logarithm normalized to the real logarithm of `Gammaℝ(2)=1/π`. -/
noncomputable def gammaLog (s : ℂ) : ℂ :=
  gammaLogRaw s - gammaLogRaw 2 + Real.log (1 / Real.pi)

private theorem gammaLog_continuousOn : ContinuousOn gammaLog rightHalfPlane := by
  exact gammaLogRaw_continuousOn.sub continuousOn_const |>.add continuousOn_const

private theorem gammaLog_two : gammaLog 2 = Real.log (1 / Real.pi) := by
  simp [gammaLog]

private theorem exp_gammaLog {s : ℂ} (hs : s ∈ rightHalfPlane) :
    Complex.exp (gammaLog s) = Gammaℝ s := by
  have h2 : (2 : ℂ) ∈ rightHalfPlane := by simp [rightHalfPlane]
  rw [gammaLog, Complex.exp_add, Complex.exp_sub, exp_gammaLogRaw hs,
    exp_gammaLogRaw h2, gammaR_two, ← Complex.ofReal_exp,
    Real.exp_log (by positivity : 0 < 1 / Real.pi)]
  push_cast
  field_simp [Real.pi_ne_zero]

private theorem gammaR_ofReal_pos {x : ℝ} (hx : 0 < x) :
    ∃ r : ℝ, 0 < r ∧ Gammaℝ (x : ℂ) = (r : ℂ) := by
  refine ⟨Real.pi ^ (-(x / 2)) * Real.Gamma (x / 2), ?_, ?_⟩
  · exact mul_pos (Real.rpow_pos_of_pos Real.pi_pos _) (Real.Gamma_pos_of_pos (by positivity))
  · rw [Gammaℝ_def]
    rw [show -(x : ℂ) / 2 = ((-(x / 2) : ℝ) : ℂ) by push_cast; ring]
    rw [show (x : ℂ) / 2 = ((x / 2 : ℝ) : ℂ) by push_cast; ring]
    rw [← Complex.ofReal_cpow Real.pi_pos.le, Complex.Gamma_ofReal]
    push_cast
    rfl

private theorem gammaLog_im_ofReal_eq_zero {x : ℝ} (hx : 0 < x) :
    (gammaLog (x : ℂ)).im = 0 := by
  let φ : ℝ → ℝ := fun u ↦ (gammaLog (u : ℂ)).im
  have hφcont : ContinuousOn φ (Ioi 0) := by
    have hmap : MapsTo (fun u : ℝ ↦ (u : ℂ)) (Ioi 0) rightHalfPlane := by
      intro u hu
      change 0 < ((u : ℂ)).re
      simpa using hu
    exact Complex.continuous_im.comp_continuousOn
      (gammaLog_continuousOn.comp continuous_ofReal.continuousOn hmap)
  have hvalues : ∀ u ∈ Ioi (0 : ℝ), ∃ k : ℤ, φ u = 2 * Real.pi * k := by
    intro u hu
    obtain ⟨r, hr, hΓ⟩ := gammaR_ofReal_pos hu
    have hexp : Complex.exp (gammaLog (u : ℂ)) =
        Complex.exp (Real.log r : ℂ) := by
      rw [exp_gammaLog (by simpa [rightHalfPlane] using hu), hΓ, ← Complex.ofReal_exp,
        Real.exp_log hr]
    obtain ⟨k, hk⟩ := Complex.exp_eq_exp_iff_exists_int.mp hexp
    refine ⟨k, ?_⟩
    have him := congrArg Complex.im hk
    simp [φ, Complex.mul_im] at him
    linarith
  have hsub : φ '' Ioi (0 : ℝ) ⊆ Set.range (fun k : ℤ ↦ 2 * Real.pi * (k : ℝ)) := by
    rintro y ⟨u, hu, rfl⟩
    obtain ⟨k, hk⟩ := hvalues u hu
    exact ⟨k, hk.symm⟩
  have hcount : (φ '' Ioi (0 : ℝ)).Countable := (Set.countable_range _).mono hsub
  have hpre : IsPreconnected (φ '' Ioi (0 : ℝ)) := by
    exact (convex_Ioi (0 : ℝ)).isPreconnected.image φ hφcont
  have hsingle := CarrierReachability.subsingleton_of_countable_preconnected hcount hpre
  have hxmem : φ x ∈ φ '' Ioi (0 : ℝ) := ⟨x, hx, rfl⟩
  have h2mem : φ 2 ∈ φ '' Ioi (0 : ℝ) := ⟨2, by norm_num, rfl⟩
  have heq := hsingle hxmem h2mem
  simpa [φ, gammaLog_two] using heq

/-- The normalized Gamma logarithm has exactly the independently integrated clock as its
imaginary part on the critical line. -/
theorem gammaLog_line_im (t : ℝ) : (gammaLog (line t)).im = theta t := by
  let φ : ℝ → ℝ := fun u ↦ (gammaLog (line u)).im
  have hcont : Continuous φ := by
    rw [continuous_iff_continuousAt]
    intro u
    exact (Complex.continuous_im.continuousAt.comp
      ((gammaLog_continuousOn (line u) (by simp [rightHalfPlane, line_re])).continuousAt
        (rightHalfPlane_isOpen.mem_nhds (by simp [rightHalfPlane, line_re])))).comp
          continuous_line.continuousAt
  have h0 : φ 0 = 0 := by
    simpa [φ, line, lineC] using gammaLog_im_ofReal_eq_zero (by norm_num : (0 : ℝ) < 1 / 2)
  apply theta_unique φ hcont h0
  intro u
  have hexp := exp_gammaLog (s := line u) (by simp [rightHalfPlane, line_re])
  calc
    Gammaℝ (line u) = Complex.exp (gammaLog (line u)) := hexp.symm
    _ =
        ((Real.exp (gammaLog (line u)).re : ℝ) : ℂ) *
          Complex.exp (I * (((φ u : ℝ)) : ℂ)) := by
            rw [show gammaLog (line u) =
              ((gammaLog (line u)).re : ℂ) + ((gammaLog (line u)).im : ℂ) * I by
                exact (Complex.re_add_im _).symm,
              Complex.exp_add, Complex.ofReal_exp]
            simp [φ]
            ring
    _ = ((‖Gammaℝ (line u)‖ : ℝ) : ℂ) *
          Complex.exp (I * (((φ u : ℝ)) : ℂ)) := by
            have hn : Real.exp (gammaLog (line u)).re = ‖Gammaℝ (line u)‖ := by
              rw [← Complex.norm_exp, hexp]
            rw [hn]

/-- The upper-right corner `2 + iT` of the standard broken contour. -/
def upperRight (T : ℝ) : ℂ := 2 + (T : ℂ) * I

@[simp] theorem upperRight_re (T : ℝ) : (upperRight T).re = 2 := by
  simp [upperRight]

@[simp] theorem upperRight_im (T : ℝ) : (upperRight T).im = T := by
  simp [upperRight]

/-- The standard path used to continue `arg ζ` from the positive value `ζ(2)` to the
critical-line point at height `T`. -/
def standardContour (T : ℝ) : Path (2 : ℂ) (line T) :=
  (Path.segment (2 : ℂ) (upperRight T)).trans
    (Path.segment (upperRight T) (line T))

private theorem zeta_ne_zero_vertical (T : ℝ) (u : unitInterval) :
    riemannZeta (Path.segment (2 : ℂ) (upperRight T) u) ≠ 0 := by
  apply riemannZeta_ne_zero_of_one_le_re
  change 1 ≤ (AffineMap.lineMap (2 : ℂ) (upperRight T) (u : ℝ)).re
  rw [AffineMap.lineMap_apply_module]
  simp [upperRight]
  ring_nf
  norm_num

private theorem topSegment_re_bounds (T : ℝ) (u : unitInterval) :
    (1 / 2 : ℝ) ≤ (Path.segment (upperRight T) (line T) u).re ∧
      (Path.segment (upperRight T) (line T) u).re ≤ 2 := by
  change (1 / 2 : ℝ) ≤
      (AffineMap.lineMap (upperRight T) (line T) (u : ℝ)).re ∧
    (AffineMap.lineMap (upperRight T) (line T) (u : ℝ)).re ≤ 2
  rw [AffineMap.lineMap_apply_module]
  constructor <;> simp [upperRight, line, lineC] <;>
    nlinarith [u.property.1, u.property.2]

private theorem topSegment_im (T : ℝ) (u : unitInterval) :
    (Path.segment (upperRight T) (line T) u).im = T := by
  change (AffineMap.lineMap (upperRight T) (line T) (u : ℝ)).im = T
  rw [AffineMap.lineMap_apply_module]
  simp [upperRight, line, lineC]
  ring

private theorem zeta_ne_zero_top {T : ℝ} (hT : GoodHeight T) (u : unitInterval) :
    riemannZeta (Path.segment (upperRight T) (line T) u) ≠ 0 := by
  intro hz
  let s : ℂ := Path.segment (upperRight T) (line T) u
  have hb := topSegment_re_bounds T u
  by_cases h1 : 1 ≤ s.re
  · exact (riemannZeta_ne_zero_of_one_le_re h1) hz
  · have hsnt : s ∈ ZD.NontrivialZeros := by
      refine ⟨?_, lt_of_not_ge h1, hz⟩
      exact lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 2) hb.1
    exact hT.2 s hsnt (topSegment_im T u)

/-- At a good height the zeta image of every point of the standard contour is nonzero. -/
theorem zeta_ne_zero_standardContour {T : ℝ} (hT : GoodHeight T) (u : unitInterval) :
    riemannZeta (standardContour T u) ≠ 0 := by
  rw [standardContour, Path.trans_apply]
  split_ifs
  · exact zeta_ne_zero_vertical T _
  · exact zeta_ne_zero_top hT _

/-- The standard contour never meets the pole of zeta. -/
theorem standardContour_ne_one {T : ℝ} (hT : GoodHeight T) (u : unitInterval) :
    standardContour T u ≠ 1 := by
  rw [standardContour, Path.trans_apply]
  split_ifs
  · intro hu
    have hre := congrArg Complex.re hu
    change (AffineMap.lineMap (2 : ℂ) (upperRight T) _).re = 1 at hre
    rw [AffineMap.lineMap_apply_module] at hre
    simp [upperRight] at hre
    linarith
  · intro hu
    have him := congrArg Complex.im hu
    rw [topSegment_im] at him
    simp at him
    exact hT.1.ne' him

/-- The zeta image of the contour, valued in the punctured plane. -/
def zetaContourPath {T : ℝ} (hT : GoodHeight T) :
    Path (⟨riemannZeta 2, riemannZeta_ne_zero_of_one_le_re (by norm_num)⟩ : {ζ : ℂ // ζ ≠ 0})
      ⟨riemannZeta (line T), by simpa using zeta_ne_zero_standardContour hT 1⟩ where
  toFun u := ⟨riemannZeta (standardContour T u), zeta_ne_zero_standardContour hT u⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    rw [continuous_iff_continuousAt]
    intro u
    exact (differentiableAt_riemannZeta (standardContour_ne_one hT u)).continuousAt.comp
      (standardContour T).continuous.continuousAt
  source' := by simp [standardContour]
  target' := by simp [standardContour]

/-- The real logarithm of the positive starting value `ζ(2) = π²/6`. -/
def initialLog : ℂ := Real.log ((Real.pi ^ 2) / 6)

theorem exp_initialLog : Complex.exp initialLog = riemannZeta 2 := by
  rw [initialLog, ← Complex.ofReal_exp, Real.exp_log (by positivity), riemannZeta_two]
  norm_num

private theorem zetaContourPath_zero {T : ℝ} (hT : GoodHeight T) :
    (zetaContourPath hT).toContinuousMap 0 =
      (⟨Complex.exp initialLog, Complex.exp_ne_zero _⟩ : {ζ : ℂ // ζ ≠ 0}) := by
  apply Subtype.ext
  simpa [zetaContourPath, standardContour] using exp_initialLog.symm

/-- The unique logarithmic lift of the zeta image of the standard contour, normalized by the
real logarithm of `ζ(2)`.  This is the independent contour construction. -/
def contourLogLift {T : ℝ} (hT : GoodHeight T) : C(unitInterval, ℂ) :=
  Complex.isCoveringMap_exp.liftPath (zetaContourPath hT).toContinuousMap initialLog (by
    exact zetaContourPath_zero hT)

/-- The lift exponentiates pointwise to the zeta value on the contour. -/
theorem exp_contourLogLift {T : ℝ} (hT : GoodHeight T) (u : unitInterval) :
    Complex.exp (contourLogLift hT u) = riemannZeta (standardContour T u) := by
  have h := congr_fun (Complex.isCoveringMap_exp.liftPath_lifts
    (zetaContourPath hT).toContinuousMap initialLog (zetaContourPath_zero hT)) u
  exact congrArg Subtype.val h

private theorem standardContour_re_pos {T : ℝ} (hT : GoodHeight T) (u : unitInterval) :
    0 < (standardContour T u).re := by
  rw [standardContour, Path.trans_apply]
  split_ifs
  · change 0 < (AffineMap.lineMap (2 : ℂ) (upperRight T) _).re
    rw [AffineMap.lineMap_apply_module]
    simp [upperRight]
    ring_nf
    norm_num
  · change 0 < (AffineMap.lineMap (upperRight T) (line T) _).re
    rw [AffineMap.lineMap_apply_module]
    simp [upperRight, line, lineC]
    nlinarith [u.property.1, u.property.2]

private theorem standardContour_sub_one_mem_slitPlane {T : ℝ} (hT : GoodHeight T)
    (u : unitInterval) : standardContour T u - 1 ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff]
  rw [standardContour, Path.trans_apply]
  split_ifs
  · left
    change 0 < (AffineMap.lineMap (2 : ℂ) (upperRight T) _ - 1).re
    rw [AffineMap.lineMap_apply_module]
    simp [upperRight]
    ring_nf
    norm_num
  · right
    simp only [Complex.sub_im, Complex.one_im, sub_zero]
    rw [topSegment_im]
    exact hT.1.ne'

/-- The logarithm of the polynomial completion factor, continued through the upper half-plane. -/
noncomputable def xiPolynomialLog (s : ℂ) : ℂ :=
  Complex.log s + Complex.log (s - 1) - Real.log 2

private theorem exp_xiPolynomialLog {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    Complex.exp (xiPolynomialLog s) = s * (s - 1) / 2 := by
  rw [xiPolynomialLog, Complex.exp_sub, Complex.exp_add, Complex.exp_log hs0,
    Complex.exp_log (sub_ne_zero.mpr hs1), ← Complex.ofReal_exp, Real.exp_log (by norm_num)]
  norm_num

private theorem continuous_xiPolynomialLog_standardContour {T : ℝ} (hT : GoodHeight T) :
    Continuous (fun u : unitInterval ↦ xiPolynomialLog (standardContour T u)) := by
  rw [continuous_iff_continuousAt]
  intro u
  have hs : standardContour T u ∈ Complex.slitPlane :=
    Complex.mem_slitPlane_iff.mpr (Or.inl (standardContour_re_pos hT u))
  have hs1 := standardContour_sub_one_mem_slitPlane hT u
  have hcsub : ContinuousAt (fun v : unitInterval ↦ standardContour T v - 1) u := by
    fun_prop
  have hlogsub : ContinuousAt
      (fun v : unitInterval ↦ Complex.log (standardContour T v - 1)) u := by
    exact (continuousAt_clog hs1).comp_of_eq hcsub rfl
  exact ((continuousAt_clog hs).comp (standardContour T).continuous.continuousAt).add
    hlogsub |>.sub continuousAt_const

private theorem xiPolynomialLog_two : xiPolynomialLog 2 = 0 := by
  have hlog : Complex.log (2 : ℂ) = (Real.log 2 : ℂ) :=
    (Complex.ofReal_log (by norm_num : (0 : ℝ) ≤ 2)).symm
  rw [xiPolynomialLog, hlog]
  norm_num

/-- The completion polynomial contributes exactly one upper-half-plane half-turn at the
critical-line endpoint. -/
theorem xiPolynomialLog_line_im {T : ℝ} (hT : GoodHeight T) :
    (xiPolynomialLog (line T)).im = Real.pi := by
  have hrel : line T - 1 = -conj (line T) := by
    apply Complex.ext <;> simp [line, lineC] <;> ring
  have himconj : (conj (line T)).im < 0 := by
    simp [line, lineC]
    linarith [hT.1]
  have hargne : (line T).arg ≠ Real.pi := by
    intro h
    have hre := (Complex.arg_eq_pi_iff.mp h).1
    rw [line_re] at hre
    norm_num at hre
  rw [xiPolynomialLog]
  simp only [Complex.sub_im, Complex.add_im, Complex.log_im, Complex.ofReal_im, sub_zero]
  rw [hrel, Complex.arg_neg_eq_arg_add_pi_of_im_neg himconj, Complex.arg_conj,
    if_neg hargne]
  ring

private theorem continuous_gammaLog_standardContour {T : ℝ} (hT : GoodHeight T) :
    Continuous (fun u : unitInterval ↦ gammaLog (standardContour T u)) := by
  rw [continuous_iff_continuousAt]
  intro u
  exact (gammaLog_continuousOn (standardContour T u)
      (by exact standardContour_re_pos hT u)).continuousAt
        (rightHalfPlane_isOpen.mem_nhds (standardContour_re_pos hT u)) |>.comp
          (standardContour T).continuous.continuousAt

/-- The logarithmic lift of the completed function along the standard half-contour. -/
noncomputable def xiContourLog {T : ℝ} (hT : GoodHeight T) : C(unitInterval, ℂ) where
  toFun u := xiPolynomialLog (standardContour T u) + gammaLog (standardContour T u) +
    contourLogLift hT u
  continuous_toFun :=
    (continuous_xiPolynomialLog_standardContour hT).add
      (continuous_gammaLog_standardContour hT) |>.add (contourLogLift hT).continuous

/-- The completed lift exponentiates to the actual entire ξ-function all along the contour. -/
theorem exp_xiContourLog {T : ℝ} (hT : GoodHeight T) (u : unitInterval) :
    Complex.exp (xiContourLog hT u) = ZD.riemannXi (standardContour T u) := by
  have hre := standardContour_re_pos hT u
  have hs0 : standardContour T u ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  have hs1 := standardContour_ne_one hT u
  change Complex.exp (xiPolynomialLog (standardContour T u) +
    gammaLog (standardContour T u) + contourLogLift hT u) = _
  rw [Complex.exp_add, Complex.exp_add,
    exp_xiPolynomialLog hs0 hs1,
    exp_gammaLog (show standardContour T u ∈ rightHalfPlane from hre),
    exp_contourLogLift, riemannXi_eq_unit_mul_zeta hre hs1]
  ring

/-- The lift starts with argument zero because `ζ(2)` is positive. -/
@[simp] theorem contourLogLift_zero {T : ℝ} (hT : GoodHeight T) :
    contourLogLift hT 0 = initialLog := by
  exact Complex.isCoveringMap_exp.liftPath_zero _ _ _

/-- Endpoint identification: the lifted logarithm is a logarithm of the actual critical-line
zeta value, not of a counting formula. -/
theorem exp_contourLogLift_one {T : ℝ} (hT : GoodHeight T) :
    Complex.exp (contourLogLift hT 1) = riemannZeta (line T) := by
  simpa [standardContour] using exp_contourLogLift hT 1

/-- The classical continued argument in `π`-units, defined solely from the standard contour. -/
def classicalSContour {T : ℝ} (hT : GoodHeight T) : ℝ :=
  (contourLogLift hT 1).im / Real.pi

/-- Endpoint phase of the completed lift: zeta continuation plus the Gamma clock plus the
completion polynomial's geometric half-turn. -/
theorem xiContourLog_one_im {T : ℝ} (hT : GoodHeight T) :
    (xiContourLog hT 1).im =
      Real.pi * (classicalSContour hT + theta T / Real.pi + 1) := by
  rw [xiContourLog]
  simp only [ContinuousMap.coe_mk, Function.comp_apply, Complex.add_im]
  have hpoly : (xiPolynomialLog (standardContour T 1)).im = Real.pi := by
    simpa [standardContour] using xiPolynomialLog_line_im hT
  have hgamma : (gammaLog (standardContour T 1)).im = theta T := by
    simpa [standardContour] using gammaLog_line_im T
  rw [hpoly, hgamma]
  unfold classicalSContour
  field_simp [Real.pi_ne_zero]
  ring

/-- The completed contour lift extended continuously from `[0,1]` to the real parameter line. -/
noncomputable def xiContourLogReal {T : ℝ} (hT : GoodHeight T) : C(ℝ, ℂ) :=
  ContinuousMap.IccExtendCM (xiContourLog hT)

private theorem xiContourLogReal_of_mem {T : ℝ} (hT : GoodHeight T) {u : ℝ}
    (hu : u ∈ Icc (0 : ℝ) 1) :
    xiContourLogReal hT u = xiContourLog hT ⟨u, hu⟩ := by
  exact ContinuousMap.IccExtendCM_of_mem hu

/-- Reparametrization of the completed lift along the right vertical edge. -/
noncomputable def xiVerticalLift {T : ℝ} (hT : GoodHeight T) (y : ℝ) : ℂ :=
  xiContourLogReal hT (y / (2 * T))

/-- Reparametrization of the completed lift along the upper edge, from `x=2` back to `x=1/2`. -/
noncomputable def xiTopLift {T : ℝ} (hT : GoodHeight T) (x : ℝ) : ℂ :=
  xiContourLogReal hT ((7 / 2 - x) / 3)

private theorem continuous_xiVerticalLift {T : ℝ} (hT : GoodHeight T) :
    Continuous (xiVerticalLift hT) := by
  unfold xiVerticalLift
  fun_prop

private theorem continuous_xiTopLift {T : ℝ} (hT : GoodHeight T) :
    Continuous (xiTopLift hT) := by
  unfold xiTopLift
  fun_prop

private theorem exp_xiVerticalLift {T : ℝ} (hT : GoodHeight T) {y : ℝ}
    (hy : y ∈ Icc (0 : ℝ) T) :
    Complex.exp (xiVerticalLift hT y) = ZD.riemannXi (2 + (y : ℂ) * I) := by
  have hTne : T ≠ 0 := hT.1.ne'
  have hden0 : 0 ≤ 2 * T := mul_nonneg (by norm_num) hT.1.le
  have hdenpos : 0 < 2 * T := mul_pos (by norm_num) hT.1
  have hu0 : 0 ≤ y / (2 * T) := div_nonneg hy.1 hden0
  have huhalf : y / (2 * T) ≤ 1 / 2 := by
    rw [div_le_iff₀ hdenpos]
    linarith [hy.2]
  have hu1 : y / (2 * T) ≤ 1 := huhalf.trans (by norm_num)
  have hu : y / (2 * T) ∈ Icc (0 : ℝ) 1 := ⟨hu0, hu1⟩
  rw [xiVerticalLift, xiContourLogReal_of_mem hT hu, exp_xiContourLog]
  rw [standardContour, Path.trans_apply]
  split_ifs with hbranch
  · change ZD.riemannXi (AffineMap.lineMap (2 : ℂ) (upperRight T) _) = _
    rw [AffineMap.lineMap_apply_module]
    congr 1
    apply Complex.ext
    · simp [upperRight, Complex.mul_re, Complex.mul_im, Complex.div_re,
        Complex.div_im, Complex.normSq_apply]
      ring
    · simp [upperRight, Complex.mul_re, Complex.mul_im, Complex.div_re,
        Complex.div_im, Complex.normSq_apply]
      field_simp [hTne]
  · exact (hbranch (by simpa using huhalf)).elim

private theorem exp_xiTopLift {T : ℝ} (hT : GoodHeight T) {x : ℝ}
    (hx : x ∈ Icc (1 / 2 : ℝ) 2) :
    Complex.exp (xiTopLift hT x) = ZD.riemannXi ((x : ℂ) + (T : ℂ) * I) := by
  let u : ℝ := (7 / 2 - x) / 3
  have hu0 : 0 ≤ u := by dsimp [u]; linarith [hx.2]
  have hu1 : u ≤ 1 := by dsimp [u]; linarith [hx.1]
  have huhalf : 1 / 2 ≤ u := by dsimp [u]; linarith [hx.2]
  have hu : u ∈ Icc (0 : ℝ) 1 := ⟨hu0, hu1⟩
  rw [xiTopLift, show (7 / 2 - x) / 3 = u by rfl,
    xiContourLogReal_of_mem hT hu, exp_xiContourLog]
  rw [standardContour, Path.trans_apply]
  split_ifs with hbranch
  · have hle : u ≤ 1 / 2 := by simpa using hbranch
    have hueq : u = 1 / 2 := le_antisymm hle huhalf
    have hxeq : x = 2 := by dsimp [u] at hueq; linarith
    subst x
    change ZD.riemannXi (AffineMap.lineMap (2 : ℂ) (upperRight T) _) = _
    rw [AffineMap.lineMap_apply_module]
    congr 1
    apply Complex.ext <;> simp [u, upperRight] <;> ring
  · change ZD.riemannXi (AffineMap.lineMap (upperRight T) (line T) _) = _
    rw [AffineMap.lineMap_apply_module]
    congr 1
    apply Complex.ext <;> simp [u, upperRight, line, lineC] <;> ring

private theorem continuous_deriv_riemannXi : Continuous (deriv ZD.riemannXi) := by
  rw [continuous_iff_continuousAt]
  intro s
  exact ((ZD.riemannXi_differentiable.analyticAt s).deriv).continuousAt

private theorem hasDerivAt_riemannXi_vertical (y : ℝ) :
    HasDerivAt (fun t : ℝ ↦ ZD.riemannXi (2 + (t : ℂ) * I))
      (deriv ZD.riemannXi (2 + (y : ℂ) * I) * I) y := by
  have haff : HasDerivAt (fun t : ℝ ↦ (2 : ℂ) + (t : ℂ) * I) I y := by
    have ht : HasDerivAt (fun t : ℝ ↦ (t : ℂ)) 1 y := (hasDerivAt_id y).ofReal_comp
    simpa using (ht.mul_const I).const_add (2 : ℂ)
  exact (ZD.riemannXi_differentiable (2 + (y : ℂ) * I)).hasDerivAt.comp y haff

private theorem hasDerivAt_riemannXi_top (T x : ℝ) :
    HasDerivAt (fun t : ℝ ↦ ZD.riemannXi ((t : ℂ) + (T : ℂ) * I))
      (deriv ZD.riemannXi ((x : ℂ) + (T : ℂ) * I)) x := by
  have haff : HasDerivAt (fun t : ℝ ↦ (t : ℂ) + (T : ℂ) * I) 1 x := by
    have ht : HasDerivAt (fun t : ℝ ↦ (t : ℂ)) 1 x := (hasDerivAt_id x).ofReal_comp
    simpa using ht.const_add ((T : ℂ) * I)
  change HasDerivAt (ZD.riemannXi ∘ fun t : ℝ ↦ (t : ℂ) + (T : ℂ) * I)
    (deriv ZD.riemannXi ((x : ℂ) + (T : ℂ) * I)) x
  exact ((ZD.riemannXi_differentiable ((x : ℂ) + (T : ℂ) * I)).hasDerivAt.comp x haff).congr_deriv
    (mul_one _)

private theorem xi_vertical_ne_zero {T : ℝ} (hT : GoodHeight T) {y : ℝ}
    (hy : y ∈ Icc (0 : ℝ) T) : ZD.riemannXi (2 + (y : ℂ) * I) ≠ 0 := by
  rw [← exp_xiVerticalLift hT hy]
  exact Complex.exp_ne_zero _

private theorem xi_top_ne_zero {T : ℝ} (hT : GoodHeight T) {x : ℝ}
    (hx : x ∈ Icc (1 / 2 : ℝ) 2) :
    ZD.riemannXi ((x : ℂ) + (T : ℂ) * I) ≠ 0 := by
  rw [← exp_xiTopLift hT hx]
  exact Complex.exp_ne_zero _

private theorem intervalIntegrable_xi_vertical_logDeriv {T : ℝ} (hT : GoodHeight T) :
    IntervalIntegrable
      (fun y : ℝ ↦ deriv ZD.riemannXi (2 + (y : ℂ) * I) * I /
        ZD.riemannXi (2 + (y : ℂ) * I)) MeasureTheory.volume 0 T := by
  have haff : Continuous (fun y : ℝ ↦ (2 : ℂ) + (y : ℂ) * I) := by fun_prop
  apply ContinuousOn.intervalIntegrable
  exact ((continuous_deriv_riemannXi.comp haff).mul continuous_const).continuousOn.div
    (ZD.riemannXi_differentiable.continuous.comp haff).continuousOn
    (fun y hy ↦ xi_vertical_ne_zero hT (by simpa [uIcc_of_le hT.1.le] using hy))

private theorem intervalIntegrable_xi_top_logDeriv {T : ℝ} (hT : GoodHeight T) :
    IntervalIntegrable
      (fun x : ℝ ↦ deriv ZD.riemannXi ((x : ℂ) + (T : ℂ) * I) /
        ZD.riemannXi ((x : ℂ) + (T : ℂ) * I)) MeasureTheory.volume (1 / 2) 2 := by
  have haff : Continuous (fun x : ℝ ↦ (x : ℂ) + (T : ℂ) * I) := by fun_prop
  apply ContinuousOn.intervalIntegrable
  exact (continuous_deriv_riemannXi.comp haff).continuousOn.div
    (ZD.riemannXi_differentiable.continuous.comp haff).continuousOn
    (fun x hx ↦ by
      rw [uIcc_of_le (by norm_num : (1 / 2 : ℝ) ≤ 2)] at hx
      exact xi_top_ne_zero hT hx)

private theorem vertical_logDeriv_integral_eq_lift_sub {T : ℝ} (hT : GoodHeight T) :
    I * (∫ y in (0 : ℝ)..T, logDeriv ZD.riemannXi (2 + (y : ℂ) * I)) =
      xiVerticalLift hT T - xiVerticalLift hT 0 := by
  have hFTC := intervalIntegral_logDeriv_eq_lift_sub_of_le hT.1.le
    (continuous_xiVerticalLift hT)
    (fun y hy ↦ exp_xiVerticalLift hT hy)
    (fun y _ ↦ hasDerivAt_riemannXi_vertical y)
    (intervalIntegrable_xi_vertical_logDeriv hT)
  have heq : (fun y : ℝ ↦ deriv ZD.riemannXi (2 + (y : ℂ) * I) * I /
      ZD.riemannXi (2 + (y : ℂ) * I)) =
      fun y : ℝ ↦ I * logDeriv ZD.riemannXi (2 + (y : ℂ) * I) := by
    funext y
    simp only [logDeriv_apply]
    ring
  rw [heq] at hFTC
  rw [intervalIntegral.integral_const_mul] at hFTC
  exact hFTC

private theorem top_logDeriv_integral_eq_lift_sub {T : ℝ} (hT : GoodHeight T) :
    (∫ x in (1 / 2 : ℝ)..2, logDeriv ZD.riemannXi ((x : ℂ) + (T : ℂ) * I)) =
      xiTopLift hT 2 - xiTopLift hT (1 / 2) := by
  simpa only [logDeriv_apply] using
    intervalIntegral_logDeriv_eq_lift_sub_of_le (by norm_num : (1 / 2 : ℝ) ≤ 2)
      (continuous_xiTopLift hT)
      (fun x hx ↦ exp_xiTopLift hT hx)
      (fun x _ ↦ hasDerivAt_riemannXi_top T x)
      (intervalIntegrable_xi_top_logDeriv hT)

/-- The logarithmic-derivative integral along `2 → 2+iT → 1/2+iT` is exactly the
increment of the independently constructed completed logarithmic lift. -/
theorem halfContourIntegral_logDeriv_riemannXi_eq_lift_sub {T : ℝ} (hT : GoodHeight T) :
    I * (∫ y in (0 : ℝ)..T, logDeriv ZD.riemannXi (2 + (y : ℂ) * I)) -
        (∫ x in (1 / 2 : ℝ)..2,
          logDeriv ZD.riemannXi ((x : ℂ) + (T : ℂ) * I)) =
      xiContourLog hT 1 - xiContourLog hT 0 := by
  rw [vertical_logDeriv_integral_eq_lift_sub hT,
    top_logDeriv_integral_eq_lift_sub hT]
  have hv0 : xiVerticalLift hT 0 = xiContourLog hT 0 := by
    rw [xiVerticalLift]
    simp only [zero_div]
    exact xiContourLogReal_of_mem hT (by norm_num)
  have hvT : xiVerticalLift hT T =
      xiContourLog hT (⟨1 / 2, by norm_num⟩ : unitInterval) := by
    rw [xiVerticalLift]
    have hTne : T ≠ 0 := hT.1.ne'
    rw [show T / (2 * T) = (1 / 2 : ℝ) by field_simp [hTne]]
    exact xiContourLogReal_of_mem hT (by norm_num)
  have ht2 : xiTopLift hT 2 =
      xiContourLog hT (⟨1 / 2, by norm_num⟩ : unitInterval) := by
    rw [xiTopLift]
    rw [show (7 / 2 - (2 : ℝ)) / 3 = (1 / 2 : ℝ) by norm_num]
    exact xiContourLogReal_of_mem hT (by norm_num)
  have hthalf : xiTopLift hT (1 / 2) = xiContourLog hT 1 := by
    rw [xiTopLift]
    rw [show (7 / 2 - (1 / 2 : ℝ)) / 3 = (1 : ℝ) by norm_num]
    exact xiContourLogReal_of_mem hT (by norm_num)
  rw [hv0, hvT, ht2, hthalf]
  ring

private theorem deriv_riemannXi_conj (s : ℂ) :
    deriv ZD.riemannXi (conj s) = conj (deriv ZD.riemannXi s) := by
  have hfun : (conj ∘ ZD.riemannXi ∘ conj) = ZD.riemannXi := by
    funext z
    simp [Function.comp_apply, riemannXi_conj]
  have hd : deriv ZD.riemannXi = conj ∘ deriv ZD.riemannXi ∘ conj := by
    rw [← deriv_conj_conj, hfun]
  have h := congr_fun hd (conj s)
  simpa using h

private theorem logDeriv_riemannXi_conj (s : ℂ) :
    logDeriv ZD.riemannXi (conj s) = conj (logDeriv ZD.riemannXi s) := by
  simp only [logDeriv_apply, deriv_riemannXi_conj, riemannXi_conj, map_div₀]

private theorem deriv_riemannXi_one_sub (s : ℂ) :
    deriv ZD.riemannXi (1 - s) = -deriv ZD.riemannXi s := by
  have hfun : (fun z : ℂ ↦ ZD.riemannXi (1 - z)) = ZD.riemannXi := by
    funext z
    exact ZD.ZeroCount.riemannXi_one_sub z
  have hd := congr_fun (congrArg deriv hfun) s
  rw [deriv_comp_const_sub] at hd
  have hneg := congrArg Neg.neg hd
  simpa using hneg

private theorem logDeriv_riemannXi_one_sub (s : ℂ) :
    logDeriv ZD.riemannXi (1 - s) = -logDeriv ZD.riemannXi s := by
  simp only [logDeriv_apply, deriv_riemannXi_one_sub,
    ZD.ZeroCount.riemannXi_one_sub]
  ring

private theorem logDeriv_riemannXi_one_sub_conj (s : ℂ) :
    logDeriv ZD.riemannXi (1 - conj s) = -conj (logDeriv ZD.riemannXi s) := by
  rw [logDeriv_riemannXi_one_sub, logDeriv_riemannXi_conj]

private theorem xi_top_ne_zero_all {T : ℝ} (hT : GoodHeight T) (x : ℝ) :
    ZD.riemannXi ((x : ℂ) + (T : ℂ) * I) ≠ 0 := by
  intro hz
  have hntz : (x : ℂ) + (T : ℂ) * I ∈ ZD.NontrivialZeros :=
    (ZD.riemannXi_eq_zero_iff _).mp hz
  exact hT.2 _ hntz (by simp)

private theorem continuous_top_logDeriv_riemannXi {T : ℝ} (hT : GoodHeight T) :
    Continuous (fun x : ℝ ↦ logDeriv ZD.riemannXi ((x : ℂ) + (T : ℂ) * I)) := by
  have haff : Continuous (fun x : ℝ ↦ (x : ℂ) + (T : ℂ) * I) := by fun_prop
  simp only [logDeriv_apply]
  exact (continuous_deriv_riemannXi.comp haff).div
    (ZD.riemannXi_differentiable.continuous.comp haff)
    (xi_top_ne_zero_all hT)

private theorem bottom_logDeriv_integral_eq_zero :
    (∫ x in (-1 : ℝ)..2, logDeriv ZD.riemannXi (x : ℂ)) = 0 := by
  let f : ℝ → ℂ := fun x ↦ logDeriv ZD.riemannXi (x : ℂ)
  have hchange : (∫ x in (-1 : ℝ)..2, f (1 - x)) = ∫ x in (-1 : ℝ)..2, f x := by
    convert (intervalIntegral.integral_comp_sub_left
      (f := f) (a := (-1 : ℝ)) (b := 2) 1) using 1 <;> norm_num
  have hneg : (∫ x in (-1 : ℝ)..2, f (1 - x)) = -∫ x in (-1 : ℝ)..2, f x := by
    calc
      _ = ∫ x in (-1 : ℝ)..2, -f x := by
        apply intervalIntegral.integral_congr
        intro x _
        simpa [f] using logDeriv_riemannXi_one_sub (x : ℂ)
      _ = _ := intervalIntegral.integral_neg
  have := hchange.symm.trans hneg
  linear_combination (1 / 2 : ℂ) * this

private theorem left_vertical_logDeriv_integral_eq_neg_conj {T : ℝ} :
    (∫ y in (0 : ℝ)..T, logDeriv ZD.riemannXi (-1 + (y : ℂ) * I)) =
      -conj (∫ y in (0 : ℝ)..T, logDeriv ZD.riemannXi (2 + (y : ℂ) * I)) := by
  calc
    _ = ∫ y in (0 : ℝ)..T,
        -conj (logDeriv ZD.riemannXi (2 + (y : ℂ) * I)) := by
      apply intervalIntegral.integral_congr
      intro y _
      have h := logDeriv_riemannXi_one_sub_conj (2 + (y : ℂ) * I)
      have hcoord : 1 - conj (2 + (y : ℂ) * I) = -1 + (y : ℂ) * I := by
        apply Complex.ext <;> simp <;> norm_num
      change logDeriv ZD.riemannXi (-1 + (y : ℂ) * I) =
        -conj (logDeriv ZD.riemannXi (2 + (y : ℂ) * I))
      rw [← hcoord]
      exact h
    _ = -(∫ y in (0 : ℝ)..T,
        conj (logDeriv ZD.riemannXi (2 + (y : ℂ) * I))) := intervalIntegral.integral_neg
    _ = _ := by rw [intervalIntegral.intervalIntegral_conj]

private theorem top_logDeriv_integral_split_conj {T : ℝ} (hT : GoodHeight T) :
    (∫ x in (-1 : ℝ)..2,
        logDeriv ZD.riemannXi ((x : ℂ) + (T : ℂ) * I)) =
      (∫ x in (1 / 2 : ℝ)..2,
        logDeriv ZD.riemannXi ((x : ℂ) + (T : ℂ) * I)) -
      conj (∫ x in (1 / 2 : ℝ)..2,
        logDeriv ZD.riemannXi ((x : ℂ) + (T : ℂ) * I)) := by
  let f : ℝ → ℂ := fun x ↦ logDeriv ZD.riemannXi ((x : ℂ) + (T : ℂ) * I)
  have hf : Continuous f := continuous_top_logDeriv_riemannXi hT
  have hleft : (∫ x in (-1 : ℝ)..(1 / 2), f x) =
      -conj (∫ x in (1 / 2 : ℝ)..2, f x) := by
    calc
      _ = ∫ x in (1 / 2 : ℝ)..2, f (1 - x) := by
        convert (intervalIntegral.integral_comp_sub_left
          (f := f) (a := (1 / 2 : ℝ)) (b := 2) 1).symm using 1 <;> norm_num
      _ = ∫ x in (1 / 2 : ℝ)..2, -conj (f x) := by
        apply intervalIntegral.integral_congr
        intro x _
        have h := logDeriv_riemannXi_one_sub_conj ((x : ℂ) + (T : ℂ) * I)
        have hcoord : 1 - conj ((x : ℂ) + (T : ℂ) * I) =
            (1 - x : ℝ) + (T : ℂ) * I := by
          apply Complex.ext <;> simp
        dsimp [f]
        rw [← hcoord]
        exact h
      _ = -(∫ x in (1 / 2 : ℝ)..2, conj (f x)) := intervalIntegral.integral_neg
      _ = _ := by rw [intervalIntegral.intervalIntegral_conj]
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (hf.intervalIntegrable (-1) (1 / 2)) (hf.intervalIntegrable (1 / 2) 2), hleft]
  ring

/-- Reflection and conjugation double the standard half-contour increment to the positively
oriented full rectangle boundary. -/
theorem rectangleBoundaryIntegral_logDeriv_riemannXi_eq_half_sub_conj
    {T : ℝ} (hT : GoodHeight T) :
    rectangleBoundaryIntegral (logDeriv ZD.riemannXi) (-1) 2 0 T =
      (I * (∫ y in (0 : ℝ)..T, logDeriv ZD.riemannXi (2 + (y : ℂ) * I)) -
        (∫ x in (1 / 2 : ℝ)..2,
          logDeriv ZD.riemannXi ((x : ℂ) + (T : ℂ) * I))) -
      conj (I * (∫ y in (0 : ℝ)..T,
          logDeriv ZD.riemannXi (2 + (y : ℂ) * I)) -
        (∫ x in (1 / 2 : ℝ)..2,
          logDeriv ZD.riemannXi ((x : ℂ) + (T : ℂ) * I))) := by
  unfold rectangleBoundaryIntegral
  simp only [Complex.ofReal_zero, zero_mul, add_zero]
  norm_num
  rw [bottom_logDeriv_integral_eq_zero,
    top_logDeriv_integral_split_conj hT,
    left_vertical_logDeriv_integral_eq_neg_conj]
  ring

private theorem xiContourLog_zero_im {T : ℝ} (hT : GoodHeight T) :
    (xiContourLog hT 0).im = 0 := by
  rw [xiContourLog]
  have hcontour : standardContour T 0 = 2 := by simp [standardContour]
  simp only [ContinuousMap.coe_mk, Complex.add_im]
  rw [hcontour, xiPolynomialLog_two, gammaLog_two, contourLogLift_zero]
  simp [initialLog]

/-- The full ξ boundary integral is the doubled imaginary increment of the completed lift.
The `+1` is the proved upper-half-plane turn of `s(s-1)/2`. -/
theorem rectangleBoundaryIntegral_logDeriv_riemannXi_eq_contour_phase
    {T : ℝ} (hT : GoodHeight T) :
    rectangleBoundaryIntegral (logDeriv ZD.riemannXi) (-1) 2 0 T =
      (2 * Real.pi * I) *
        ((classicalSContour hT + theta T / Real.pi + 1 : ℝ) : ℂ) := by
  rw [rectangleBoundaryIntegral_logDeriv_riemannXi_eq_half_sub_conj hT,
    halfContourIntegral_logDeriv_riemannXi_eq_lift_sub hT]
  let z : ℂ := xiContourLog hT 1 - xiContourLog hT 0
  have hz : z - conj z = 2 * I * ((z.im : ℝ) : ℂ) := by
    apply Complex.ext <;> simp [z, Complex.mul_re, Complex.mul_im] <;> ring
  rw [show xiContourLog hT 1 - xiContourLog hT 0 = z by rfl, hz]
  have hzim : z.im = Real.pi *
      (classicalSContour hT + theta T / Real.pi + 1) := by
    change (xiContourLog hT 1 - xiContourLog hT 0).im = _
    rw [Complex.sub_im, xiContourLog_one_im hT, xiContourLog_zero_im hT, sub_zero]
  rw [hzim]
  push_cast
  ring

/-- The endpoint phase reconstruction for the independently defined contour argument. -/
theorem zeta_eq_norm_mul_exp_classicalSContour {T : ℝ} (hT : GoodHeight T) :
    riemannZeta (line T) =
      ((Real.exp (contourLogLift hT 1).re : ℝ) : ℂ) *
        Complex.exp (I * ((Real.pi * classicalSContour hT : ℝ) : ℂ)) := by
  rw [← exp_contourLogLift_one hT]
  let z := contourLogLift hT 1
  have harg : I * ((Real.pi * classicalSContour hT : ℝ) : ℂ) = (z.im : ℂ) * I := by
    unfold classicalSContour z
    push_cast
    field_simp [Real.pi_ne_zero]
  change Complex.exp z = ((Real.exp z.re : ℝ) : ℂ) *
    Complex.exp (I * ((Real.pi * classicalSContour hT : ℝ) : ℂ))
  rw [harg]
  calc
    Complex.exp z = Complex.exp ((z.re : ℂ) + (z.im : ℂ) * I) := by
      rw [Complex.re_add_im]
    _ = ((Real.exp z.re : ℝ) : ℂ) * Complex.exp ((z.im : ℂ) * I) := by
      rw [Complex.exp_add, Complex.ofReal_exp]

/-- The radial part of the lifted logarithm is the absolute value of the real native state. -/
theorem exp_contourLogLift_re_eq_abs_rsZ {T : ℝ} (hT : GoodHeight T) :
    Real.exp (contourLogLift hT 1).re = |rsZ T| := by
  have hnorm : Real.exp (contourLogLift hT 1).re = ‖riemannZeta (line T)‖ := by
    rw [← exp_contourLogLift_one hT, Complex.norm_exp]
  rw [hnorm, unit_chart_factorization, norm_mul]
  simp [Complex.norm_exp]

/-- After the independently continued zeta argument is combined with the independently derived
Gamma clock, the endpoint phase is exactly the sign of the real native state. -/
theorem contour_phase_times_clock_eq_sign_rsZ {T : ℝ} (hT : GoodHeight T) :
    Complex.exp (I * (((Real.pi * classicalSContour hT + theta T : ℝ)) : ℂ)) =
      (((rsZ T / |rsZ T| : ℝ) : ℂ)) := by
  have hrs_ne : rsZ T ≠ 0 := by
    intro hrs
    have hz : riemannZeta (line T) = 0 := (rsZ_zero_iff T).mp hrs
    exact (zeta_ne_zero_standardContour hT 1) (by simpa [standardContour] using hz)
  have habs_ne : |rsZ T| ≠ 0 := abs_ne_zero.mpr hrs_ne
  have hzeta := zeta_eq_norm_mul_exp_classicalSContour hT
  rw [unit_chart_factorization, exp_contourLogLift_re_eq_abs_rsZ hT] at hzeta
  have hq_ne : Complex.exp (I * ((theta T : ℝ) : ℂ)) ≠ 0 := Complex.exp_ne_zero _
  have hmul :
      ((|rsZ T| : ℝ) : ℂ) *
          Complex.exp (I * ((Real.pi * classicalSContour hT : ℝ) : ℂ)) *
          Complex.exp (I * ((theta T : ℝ) : ℂ)) = (rsZ T : ℂ) := by
    calc
      ((|rsZ T| : ℝ) : ℂ) *
            Complex.exp (I * ((Real.pi * classicalSContour hT : ℝ) : ℂ)) *
            Complex.exp (I * ((theta T : ℝ) : ℂ)) =
          ((rsZ T : ℝ) : ℂ) * Complex.exp (-(I * ((theta T : ℝ) : ℂ))) *
            Complex.exp (I * ((theta T : ℝ) : ℂ)) := by rw [← hzeta]
      _ = (rsZ T : ℂ) := by
        rw [Complex.exp_neg]
        field_simp
  rw [Complex.ofReal_div]
  apply (eq_div_iff (Complex.ofReal_ne_zero.mpr habs_ne)).2
  rw [← hmul]
  have hadd :
      I * (((Real.pi * classicalSContour hT + theta T : ℝ)) : ℂ) =
        I * ((Real.pi * classicalSContour hT : ℝ) : ℂ) +
          I * ((theta T : ℝ) : ℂ) := by
    push_cast
    ring
  rw [hadd, Complex.exp_add]
  ring

/-- The contour-plus-clock coordinate is quantized in integer units of `π`.  The integer is
obtained from the exponential covering; it is not supplied by a zero count. -/
theorem exists_contourWindingIndex {T : ℝ} (hT : GoodHeight T) :
    ∃ k : ℤ, classicalSContour hT + theta T / Real.pi = k := by
  have hphase := contour_phase_times_clock_eq_sign_rsZ hT
  have hrs_ne : rsZ T ≠ 0 := by
    intro hrs
    have hz : riemannZeta (line T) = 0 := (rsZ_zero_iff T).mp hrs
    exact (zeta_ne_zero_standardContour hT 1) (by simpa [standardContour] using hz)
  have habs_ne : |rsZ T| ≠ 0 := abs_ne_zero.mpr hrs_ne
  have hsq :
      Complex.exp (2 * (I * (((Real.pi * classicalSContour hT + theta T : ℝ)) : ℂ))) = 1 := by
    calc
      Complex.exp (2 * (I * (((Real.pi * classicalSContour hT + theta T : ℝ)) : ℂ))) =
          Complex.exp (I * (((Real.pi * classicalSContour hT + theta T : ℝ)) : ℂ)) ^ 2 := by
            simpa using (Complex.exp_nat_mul
              (I * (((Real.pi * classicalSContour hT + theta T : ℝ)) : ℂ)) 2)
      _ = 1 := by
        rw [hphase]
        push_cast
        field_simp [habs_ne]
        norm_cast
        exact (sq_abs (rsZ T)).symm
  rw [Complex.exp_eq_one_iff] at hsq
  obtain ⟨k, hk⟩ := hsq
  refine ⟨k, ?_⟩
  have him := congrArg Complex.im hk
  simp [Complex.mul_im] at him
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  field_simp [hpi]
  linarith

/-- The integer selected by the independently lifted contour. -/
def contourWindingIndex {T : ℝ} (hT : GoodHeight T) : ℤ :=
  (exists_contourWindingIndex hT).choose

/-- **Contour-argument identification.**  The classical continued argument is the global
integer winding coordinate minus the Archimedean clock, in `π`-units. -/
theorem classicalSContour_eq_winding_sub_clock {T : ℝ} (hT : GoodHeight T) :
    classicalSContour hT = contourWindingIndex hT - theta T / Real.pi := by
  have hk := (exists_contourWindingIndex hT).choose_spec
  unfold contourWindingIndex
  linarith

/-- The independently selected winding integer is the normalized ξ boundary integral; the
constant term is the polynomial completion factor's proved half-turn. -/
theorem rectangleBoundaryIntegral_logDeriv_riemannXi_eq_winding_add_one
    {T : ℝ} (hT : GoodHeight T) :
    rectangleBoundaryIntegral (logDeriv ZD.riemannXi) (-1) 2 0 T =
      (2 * Real.pi * I) * (((contourWindingIndex hT + 1 : ℤ) : ℂ)) := by
  rw [rectangleBoundaryIntegral_logDeriv_riemannXi_eq_contour_phase hT]
  have hphase : classicalSContour hT + theta T / Real.pi + 1 =
      (contourWindingIndex hT : ℝ) + 1 := by
    rw [classicalSContour_eq_winding_sub_clock hT]
    ring
  rw [hphase]
  push_cast
  rfl

/-! ## The independently defined strip census

This is kept separate from the contour lift.  It is a finite sum over Mathlib's actual
nontrivial-zero set, not a definition through `classicalSContour` or its winding index.
-/

/-- Nontrivial zeros in the upper strip through height `T`. -/
def stripZeroWindow (T : ℝ) : Set ℂ :=
  {ρ : ℂ | ρ ∈ ZD.NontrivialZeros ∧ 0 < ρ.im ∧ ρ.im ≤ T}

/-- Every finite-height upper-strip zero window is finite. -/
theorem stripZeroWindow_finite (T : ℝ) : (stripZeroWindow T).Finite := by
  apply Set.Finite.subset
    (ZD.ZeroCount.NontrivialZeros_inter_closedBall_finite (|T| + 1))
  intro ρ hρ
  refine ⟨hρ.1, ?_⟩
  rw [Metric.mem_closedBall, dist_zero_right]
  calc
    ‖ρ‖ = ‖(ρ.re : ℂ) + (ρ.im : ℂ) * I‖ := by rw [Complex.re_add_im]
    _ ≤ ‖(ρ.re : ℂ)‖ + ‖(ρ.im : ℂ) * I‖ := norm_add_le _ _
    _ = |ρ.re| + |ρ.im| := by simp
    _ ≤ |T| + 1 := by
      rw [abs_of_pos hρ.1.1, abs_of_pos hρ.2.1]
      have hT0 : 0 ≤ T := le_trans hρ.2.1.le hρ.2.2
      rw [abs_of_nonneg hT0]
      have hre : ρ.re < 1 := hρ.1.2.1
      have him : ρ.im ≤ T := hρ.2.2
      linarith

/-- The finite upper-strip zero window as a finset. -/
def stripZeroFinset (T : ℝ) : Finset ℂ := (stripZeroWindow_finite T).toFinset

/-- Above every real ordinate there is a good contour height.  The construction uses the first
zero ordinate in the next finite strip window when one exists, and takes a strict midpoint below
it; otherwise it takes the midpoint of the empty unit window. -/
theorem exists_goodHeight_gt (a : ℝ) : ∃ T : ℝ, a < T ∧ GoodHeight T := by
  classical
  let b : ℝ := max a 0
  let O : Finset ℝ :=
    ((stripZeroFinset (b + 1)).image Complex.im).filter (fun y => b < y)
  by_cases hO : O.Nonempty
  · let m : ℝ := O.min' hO
    have hmO : m ∈ O := Finset.min'_mem O hO
    have hbm : b < m := (Finset.mem_filter.mp hmO).2
    have hmle : m ≤ b + 1 := by
      obtain ⟨ρ, hρ, hρm⟩ := Finset.mem_image.mp (Finset.mem_filter.mp hmO).1
      have hstrip := (stripZeroWindow_finite (b + 1)).mem_toFinset.mp hρ
      rw [← hρm]
      exact hstrip.2.2
    let T : ℝ := (b + m) / 2
    have hbT : b < T := by dsimp [T]; linarith
    have hTm : T < m := by dsimp [T]; linarith
    have hTpos : 0 < T := lt_of_le_of_lt (le_max_right a 0) hbT
    refine ⟨T, lt_of_le_of_lt (le_max_left a 0) hbT, hTpos, ?_⟩
    intro ρ hρ hρT
    have hTle : T ≤ b + 1 := hTm.le.trans hmle
    have hρstrip : ρ ∈ stripZeroFinset (b + 1) := by
      apply (stripZeroWindow_finite (b + 1)).mem_toFinset.mpr
      exact ⟨hρ, hρT.symm ▸ hTpos, hρT.symm ▸ hTle⟩
    have himO : ρ.im ∈ O := by
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_image.mpr ⟨ρ, hρstrip, rfl⟩, hρT.symm ▸ hbT⟩
    have hmT : m ≤ T := by
      rw [← hρT]
      exact Finset.min'_le O ρ.im himO
    exact (not_le_of_gt hTm) hmT
  · let T : ℝ := b + 1 / 2
    have hbT : b < T := by dsimp [T]; norm_num
    have hTle : T ≤ b + 1 := by dsimp [T]; norm_num
    have hTpos : 0 < T := lt_of_le_of_lt (le_max_right a 0) hbT
    refine ⟨T, lt_of_le_of_lt (le_max_left a 0) hbT, hTpos, ?_⟩
    intro ρ hρ hρT
    apply hO
    refine ⟨ρ.im, Finset.mem_filter.mpr ⟨?_, hρT.symm ▸ hbT⟩⟩
    apply Finset.mem_image.mpr
    refine ⟨ρ, ?_, rfl⟩
    apply (stripZeroWindow_finite (b + 1)).mem_toFinset.mpr
    exact ⟨hρ, hρT.symm ▸ hTpos, hρT.symm ▸ hTle⟩

/-- The multiplicity-weighted count of all nontrivial zeros in the upper strip. -/
def stripZeroCountMult (T : ℝ) : ℕ :=
  ∑ ρ ∈ stripZeroFinset T, ZD.xiOrderNat ρ

/-- **Summed ξ-divisor kernel on the upper strip.** Every member of the independent strip
census lies strictly inside the rectangle `[-1,2] × [0,T]` at a good height, so summing the
one-point `2πi` kernel gives `2πi` times the multiplicity-weighted strip count. -/
theorem rectangleBoundaryIntegral_strip_xi_divisor {T : ℝ} (hT : GoodHeight T) :
    rectangleBoundaryIntegral
        (fun z ↦ ∑ ρ ∈ stripZeroFinset T,
          (ZD.xiOrderNat ρ : ℂ) * (z - ρ)⁻¹) (-1) 2 0 T =
      (2 * Real.pi * I) * (stripZeroCountMult T : ℂ) := by
  have hinside : ∀ ρ ∈ stripZeroFinset T,
      (-1 : ℝ) < ρ.re ∧ ρ.re < 2 ∧ 0 < ρ.im ∧ ρ.im < T := by
    intro ρ hρ
    have hs := (stripZeroWindow_finite T).mem_toFinset.mp hρ
    refine ⟨by linarith [hs.1.1], by linarith [hs.1.2.1], hs.2.1, ?_⟩
    exact lt_of_le_of_ne hs.2.2 (hT.2 ρ hs.1)
  have hsum := rectangleBoundaryIntegral_weighted_divisor
    (stripZeroFinset T) (fun ρ ↦ (ZD.xiOrderNat ρ : ℂ)) hinside
  unfold stripZeroCountMult
  push_cast
  exact hsum

/-- The analytic argument principle applied directly to the entire ξ-function on the standard
rectangle.  This intermediate form still displays Mathlib's analytic divisor explicitly. -/
theorem rectangleBoundaryIntegral_logDeriv_riemannXi_eq_divisor_sum
    {T : ℝ} (hT : GoodHeight T) :
    let R := T + 4
    let D := MeromorphicOn.divisor ZD.riemannXi (Metric.closedBall (0 : ℂ) R)
    let S := (D.finiteSupport (isCompact_closedBall 0 R)).toFinset
    rectangleBoundaryIntegral (logDeriv ZD.riemannXi) (-1) 2 0 T =
      (2 * Real.pi * I) *
        ∑ ρ ∈ S.filter (fun ρ ↦
          (-1 : ℝ) < ρ.re ∧ ρ.re < 2 ∧ 0 < ρ.im ∧ ρ.im < T), (D ρ : ℂ) := by
  apply rectangleBoundaryIntegral_logDeriv_eq_divisor_sum
  · linarith [hT.1]
  · norm_num
  · exact hT.1.le
  · intro z hz
    rw [Metric.mem_closedBall, dist_zero_right]
    have hre_abs : |z.re| ≤ 2 := by
      rw [abs_le]
      exact ⟨by linarith [hz.1.1], hz.1.2⟩
    have him_abs : |z.im| = z.im := abs_of_nonneg hz.2.1
    calc
      ‖z‖ = ‖(z.re : ℂ) + (z.im : ℂ) * I‖ := by rw [Complex.re_add_im]
      _ ≤ ‖(z.re : ℂ)‖ + ‖(z.im : ℂ) * I‖ := norm_add_le _ _
      _ = |z.re| + |z.im| := by simp
      _ ≤ 2 + T := by rw [him_abs]; linarith [hz.2.2]
      _ ≤ T + 4 := by linarith
  · exact ZD.ZeroCount.riemannXi_analyticOnNhd_univ.mono (Set.subset_univ _)
  · intro u
    rw [(ZD.ZeroCount.riemannXi_analyticOnNhd_univ u (Set.mem_univ _)).meromorphicOrderAt_eq]
    intro hmap
    exact ZD.riemannXi_analyticOrderAt_ne_top_everywhere u
      (ENat.map_eq_top_iff.mp hmap)
  · intro ρ hD
    let U : Set ℂ := Metric.closedBall (0 : ℂ) (T + 4)
    have hAnal : AnalyticOnNhd ℂ ZD.riemannXi U :=
      ZD.ZeroCount.riemannXi_analyticOnNhd_univ.mono (Set.subset_univ _)
    have hord : ∀ u : U, meromorphicOrderAt ZD.riemannXi u ≠ ⊤ := by
      intro u
      rw [(ZD.ZeroCount.riemannXi_analyticOnNhd_univ u (Set.mem_univ _)).meromorphicOrderAt_eq]
      intro hmap
      exact ZD.riemannXi_analyticOrderAt_ne_top_everywhere u
        (ENat.map_eq_top_iff.mp hmap)
    have hsupp : ρ ∈ Function.support (MeromorphicOn.divisor ZD.riemannXi U) := by
      exact hD
    have hzmem : ρ ∈ U ∩ ZD.riemannXi ⁻¹' {0} := by
      rw [hAnal.meromorphicNFOn.zero_set_eq_divisor_support hord]
      exact hsupp
    have hntz : ρ ∈ ZD.NontrivialZeros :=
      (ZD.riemannXi_eq_zero_iff ρ).mp hzmem.2
    have him0 : ρ.im ≠ 0 := by
      intro him
      have htriv : ∀ n : ℕ, ρ ≠ -2 * ((n : ℂ) + 1) := by
        intro n hn
        have hre := congrArg Complex.re hn
        simp at hre
        linarith [hntz.1]
      have hbound := riemannZeta_nontrivial_zero_im_ge_two hntz.2.2 htriv
      rw [him, abs_zero] at hbound
      norm_num at hbound
    refine ⟨by linarith [hntz.1], by linarith [hntz.2.1], him0, ?_⟩
    exact hT.2 ρ hntz

/-- The interior support of ξ's analytic divisor on the containing disk is exactly the independently
defined upper-strip zero finset. -/
theorem riemannXi_divisor_interior_finset_eq_stripZeroFinset
    {T : ℝ} (hT : GoodHeight T) :
    let R := T + 4
    let U := Metric.closedBall (0 : ℂ) R
    let D := MeromorphicOn.divisor ZD.riemannXi U
    let S := (D.finiteSupport (isCompact_closedBall 0 R)).toFinset
    S.filter (fun ρ ↦
      (-1 : ℝ) < ρ.re ∧ ρ.re < 2 ∧ 0 < ρ.im ∧ ρ.im < T) = stripZeroFinset T := by
  dsimp only
  let R : ℝ := T + 4
  let U : Set ℂ := Metric.closedBall (0 : ℂ) R
  let D := MeromorphicOn.divisor ZD.riemannXi U
  let S : Finset ℂ := (D.finiteSupport (isCompact_closedBall 0 R)).toFinset
  have hAnal : AnalyticOnNhd ℂ ZD.riemannXi U :=
    ZD.ZeroCount.riemannXi_analyticOnNhd_univ.mono (Set.subset_univ _)
  have hord : ∀ u : U, meromorphicOrderAt ZD.riemannXi u ≠ ⊤ := by
    intro u
    rw [(ZD.ZeroCount.riemannXi_analyticOnNhd_univ u (Set.mem_univ _)).meromorphicOrderAt_eq]
    intro hmap
    exact ZD.riemannXi_analyticOrderAt_ne_top_everywhere u
      (ENat.map_eq_top_iff.mp hmap)
  have hzeros := hAnal.meromorphicNFOn.zero_set_eq_divisor_support hord
  have hstrip_ball : ∀ ρ ∈ stripZeroFinset T, ρ ∈ U := by
    intro ρ hρ
    have hs := (stripZeroWindow_finite T).mem_toFinset.mp hρ
    dsimp [U, R]
    rw [Metric.mem_closedBall, dist_zero_right]
    calc
      ‖ρ‖ = ‖(ρ.re : ℂ) + (ρ.im : ℂ) * I‖ := by rw [Complex.re_add_im]
      _ ≤ ‖(ρ.re : ℂ)‖ + ‖(ρ.im : ℂ) * I‖ := norm_add_le _ _
      _ = |ρ.re| + |ρ.im| := by simp
      _ = ρ.re + ρ.im := by rw [abs_of_pos hs.1.1, abs_of_pos hs.2.1]
      _ ≤ 1 + T := by linarith [hs.1.2.1, hs.2.2]
      _ ≤ T + 4 := by linarith
  ext ρ
  constructor
  · intro hρ
    have hfilt := Finset.mem_filter.mp hρ
    have hsupp : ρ ∈ Function.support D := by
      exact (D.finiteSupport (isCompact_closedBall 0 R)).mem_toFinset.mp hfilt.1
    have hzmem : ρ ∈ U ∩ ZD.riemannXi ⁻¹' {0} := by
      rw [hzeros]
      exact hsupp
    have hntz : ρ ∈ ZD.NontrivialZeros := (ZD.riemannXi_eq_zero_iff ρ).mp hzmem.2
    apply (stripZeroWindow_finite T).mem_toFinset.mpr
    exact ⟨hntz, hfilt.2.2.2.1, hfilt.2.2.2.2.le⟩
  · intro hρ
    have hs := (stripZeroWindow_finite T).mem_toFinset.mp hρ
    apply Finset.mem_filter.mpr
    constructor
    · apply (D.finiteSupport (isCompact_closedBall 0 R)).mem_toFinset.mpr
      have hzmem : ρ ∈ U ∩ ZD.riemannXi ⁻¹' {0} :=
        ⟨hstrip_ball ρ hρ, (ZD.riemannXi_eq_zero_iff ρ).mpr hs.1⟩
      rw [hzeros] at hzmem
      simpa [D] using hzmem
    · refine ⟨by linarith [hs.1.1], by linarith [hs.1.2.1], hs.2.1, ?_⟩
      exact lt_of_le_of_ne hs.2.2 (hT.2 ρ hs.1)

/-- On the independent strip window, the analytic divisor coefficient of ξ is exactly
`xiOrderNat`, so the divisor sum carries the intended zero multiplicities. -/
theorem riemannXi_divisor_eq_xiOrderNat_of_mem_stripZeroFinset
    {T : ℝ} {ρ : ℂ} (hρ : ρ ∈ stripZeroFinset T) :
    let U := Metric.closedBall (0 : ℂ) (T + 4)
    ((MeromorphicOn.divisor ZD.riemannXi U ρ : ℤ) : ℂ) =
      (ZD.xiOrderNat ρ : ℂ) := by
  dsimp only
  let U : Set ℂ := Metric.closedBall (0 : ℂ) (T + 4)
  have hs := (stripZeroWindow_finite T).mem_toFinset.mp hρ
  have hρU : ρ ∈ U := by
    dsimp [U]
    rw [Metric.mem_closedBall, dist_zero_right]
    calc
      ‖ρ‖ = ‖(ρ.re : ℂ) + (ρ.im : ℂ) * I‖ := by rw [Complex.re_add_im]
      _ ≤ ‖(ρ.re : ℂ)‖ + ‖(ρ.im : ℂ) * I‖ := norm_add_le _ _
      _ = |ρ.re| + |ρ.im| := by simp
      _ = ρ.re + ρ.im := by rw [abs_of_pos hs.1.1, abs_of_pos hs.2.1]
      _ ≤ 1 + T := by linarith [hs.1.2.1, hs.2.2]
      _ ≤ T + 4 := by linarith
  have hAnal : AnalyticOnNhd ℂ ZD.riemannXi U :=
    ZD.ZeroCount.riemannXi_analyticOnNhd_univ.mono (Set.subset_univ _)
  have hAnalρ : AnalyticAt ℂ ZD.riemannXi ρ :=
    ZD.ZeroCount.riemannXi_analyticOnNhd_univ ρ (Set.mem_univ _)
  have hne := ZD.riemannXi_analyticOrderAt_ne_top_everywhere ρ
  rw [MeromorphicOn.divisor_apply hAnal.meromorphicOn hρU, hAnalρ.meromorphicOrderAt_eq]
  unfold ZD.xiOrderNat analyticOrderNatAt
  rw [← ENat.coe_toNat hne]
  simp

/-- **Independent ξ argument principle.** The boundary integral of `ξ'/ξ` around the standard
rectangle is exactly `2πi` times the independently defined multiplicity-weighted strip census. -/
theorem rectangleBoundaryIntegral_logDeriv_riemannXi
    {T : ℝ} (hT : GoodHeight T) :
    rectangleBoundaryIntegral (logDeriv ZD.riemannXi) (-1) 2 0 T =
      (2 * Real.pi * I) * (stripZeroCountMult T : ℂ) := by
  let U : Set ℂ := Metric.closedBall (0 : ℂ) (T + 4)
  let D := MeromorphicOn.divisor ZD.riemannXi U
  let S : Finset ℂ := (D.finiteSupport (isCompact_closedBall 0 (T + 4))).toFinset
  have harg := rectangleBoundaryIntegral_logDeriv_riemannXi_eq_divisor_sum hT
  dsimp only at harg
  have hfin := riemannXi_divisor_interior_finset_eq_stripZeroFinset hT
  dsimp only at hfin
  have hsum :
      (∑ ρ ∈ stripZeroFinset T, (D ρ : ℂ)) = (stripZeroCountMult T : ℂ) := by
    unfold stripZeroCountMult
    push_cast
    apply Finset.sum_congr rfl
    intro ρ hρ
    exact riemannXi_divisor_eq_xiOrderNat_of_mem_stripZeroFinset hρ
  change rectangleBoundaryIntegral (logDeriv ZD.riemannXi) (-1) 2 0 T = _
  rw [harg]
  change (2 * Real.pi * I) *
      (∑ ρ ∈ S.filter (fun ρ ↦
        (-1 : ℝ) < ρ.re ∧ ρ.re < 2 ∧ 0 < ρ.im ∧ ρ.im < T), (D ρ : ℂ)) = _
  rw [show S.filter (fun ρ ↦
      (-1 : ℝ) < ρ.re ∧ ρ.re < 2 ∧ 0 < ρ.im ∧ ρ.im < T) = stripZeroFinset T by
        simpa [S, D, U] using hfin,
    hsum]

/-- **Independent contour-count identification.** The winding selected solely by the continued
zeta argument and Archimedean clock, plus the completion polynomial's geometric half-turn,
equals the multiplicity-weighted census of the actual ξ zeros in the strip. -/
theorem contourWindingIndex_add_one_eq_stripZeroCountMult
    {T : ℝ} (hT : GoodHeight T) :
    contourWindingIndex hT + 1 = stripZeroCountMult T := by
  have hw := rectangleBoundaryIntegral_logDeriv_riemannXi_eq_winding_add_one hT
  have hz := rectangleBoundaryIntegral_logDeriv_riemannXi hT
  have hprod :
      (2 * Real.pi * I) * (((contourWindingIndex hT + 1 : ℤ) : ℂ)) =
        (2 * Real.pi * I) * (stripZeroCountMult T : ℂ) := hw.symm.trans hz
  have hcoeff : (2 * Real.pi * I : ℂ) ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) I_ne_zero
  have hcast := mul_left_cancel₀ hcoeff hprod
  have hre := congrArg Complex.re hcast
  norm_num at hre
  exact_mod_cast hre

/-- The independent strip census is empty below height `2`. -/
theorem stripZeroCountMult_eq_zero_of_lt_two {T : ℝ} (hT2 : T < 2) :
    stripZeroCountMult T = 0 := by
  classical
  unfold stripZeroCountMult
  apply Finset.sum_eq_zero
  intro ρ hρ
  have hs := (stripZeroWindow_finite T).mem_toFinset.mp hρ
  have htriv : ∀ n : ℕ, ρ ≠ -2 * ((n : ℂ) + 1) := by
    intro n hn
    have hre := congrArg Complex.re hn
    simp at hre
    linarith [hs.1.1]
  have him := riemannZeta_nontrivial_zero_im_ge_two hs.1.2.2 htriv
  rw [abs_of_pos hs.2.1] at him
  have : False := by linarith [hs.2.2]
  exact this.elim

/-- The on-line portion of the same independently defined strip window. -/
def onLineStripZeroCountMult (T : ℝ) : ℕ :=
  ∑ ρ ∈ (stripZeroFinset T).filter (fun ρ => ρ.re = 1 / 2), ZD.xiOrderNat ρ

/-- The off-line portion of the same independently defined strip window. -/
def offLineStripZeroCountMult (T : ℝ) : ℕ :=
  ∑ ρ ∈ (stripZeroFinset T).filter (fun ρ => ρ.re ≠ 1 / 2), ZD.xiOrderNat ρ

/-- The strip census partitions exactly into its on-line and off-line multiplicity ledgers. -/
theorem stripZeroCountMult_eq_onLine_add_offLine (T : ℝ) :
    stripZeroCountMult T = onLineStripZeroCountMult T + offLineStripZeroCountMult T := by
  classical
  unfold stripZeroCountMult onLineStripZeroCountMult offLineStripZeroCountMult
  rw [← Finset.sum_union]
  · congr 1
    ext ρ
    simp only [Finset.mem_union, Finset.mem_filter]
    by_cases hρ : ρ.re = 1 / 2
    · simp [hρ]
    · constructor
      · intro hmem
        exact Or.inr ⟨hmem, hρ⟩
      · rintro (hline | hoff)
        · exact hline.1
        · exact hoff.1
  · rw [Finset.disjoint_left]
    intro ρ hline hoff
    exact (Finset.mem_filter.mp hoff).2 (Finset.mem_filter.mp hline).2

/-- The on-line part of the complex strip census is exactly the existing line multiplicity
ledger.  The proof is the bijection `γ ↦ 1/2+iγ`, with vanishing orders transported by the
analytic-unit order bridge for `riemannXi`. -/
theorem onLineStripZeroCountMult_eq_zeroEventCountMult (T : ℝ) :
    onLineStripZeroCountMult T = zeroEventCountMult T := by
  classical
  unfold onLineStripZeroCountMult zeroEventCountMult
  symm
  apply Finset.sum_bij (fun γ _ => line γ)
  · intro γ hγ
    rw [Finset.mem_filter]
    constructor
    · apply (stripZeroWindow_finite T).mem_toFinset.mpr
      have he := (events_finite T).mem_toFinset.mp hγ
      exact ⟨⟨by rw [line_re]; norm_num, by rw [line_re]; norm_num, he.2⟩,
        by simpa [line, lineC] using he.1.1, by simpa [line, lineC] using he.1.2⟩
    · rw [line_re]
  · intro γ₁ _ γ₂ _ hline
    exact line_injective hline
  · intro ρ hρ
    have hfilter := Finset.mem_filter.mp hρ
    have hstrip := (stripZeroWindow_finite T).mem_toFinset.mp hfilter.1
    refine ⟨ρ.im, ?_, ?_⟩
    · apply (events_finite T).mem_toFinset.mpr
      refine ⟨⟨hstrip.2.1, hstrip.2.2⟩, ?_⟩
      have hline : line ρ.im = ρ := by
        apply Complex.ext
        · rw [line_re, hfilter.2]
        · simp [line, lineC]
      rw [hline]
      exact hstrip.1.2.2
    · apply Complex.ext
      · rw [line_re, hfilter.2]
      · simp [line, lineC]
  · intro γ hγ
    exact eventOrder_eq_xiOrderNat γ ((events_finite T).mem_toFinset.mp hγ).1.1

/-- The independently defined strip census therefore splits into the existing on-line ledger
and a separately typed off-line ledger. -/
theorem stripZeroCountMult_eq_line_add_offLine (T : ℝ) :
    stripZeroCountMult T = zeroEventCountMult T + offLineStripZeroCountMult T := by
  rw [stripZeroCountMult_eq_onLine_add_offLine,
    onLineStripZeroCountMult_eq_zeroEventCountMult]

/-- The off-line multiplicity is exactly the excess of the independently lifted contour
winding over the native line-event multiplicity.  Both sides are integers; no argument branch
or zero-set identification occurs in this subtraction. -/
theorem offLineStripZeroCountMult_eq_winding_sub_line
    {T : ℝ} (hT : GoodHeight T) :
    (offLineStripZeroCountMult T : ℤ) =
      contourWindingIndex hT + 1 - zeroEventCountMult T := by
  have hw := contourWindingIndex_add_one_eq_stripZeroCountMult hT
  have hsplit := stripZeroCountMult_eq_line_add_offLine T
  omega

/-- **Global-coordinate registration law.**  The independently continued classical argument
is the native multiplicity ledger plus the multiplicity of the analytic zeros not represented
by line events.  Thus `S_mult` is the native 3D coordinate and the second summand is the exact,
nonnegative coverage defect of the scalar strip census. -/
theorem classicalSContour_eq_Smult_add_offLine
    {T : ℝ} (hT : GoodHeight T) :
    classicalSContour hT =
      Smult T + (offLineStripZeroCountMult T : ℝ) := by
  have hw := contourWindingIndex_add_one_eq_stripZeroCountMult hT
  have hsplit := stripZeroCountMult_eq_line_add_offLine T
  rw [classicalSContour_eq_winding_sub_clock hT]
  unfold Smult
  have hwR : (contourWindingIndex hT : ℝ) + 1 =
      (stripZeroCountMult T : ℝ) := by exact_mod_cast hw
  have hsplitR : (stripZeroCountMult T : ℝ) =
      (zeroEventCountMult T : ℝ) + (offLineStripZeroCountMult T : ℝ) := by
    exact_mod_cast hsplit
  linarith

/-- Equality of the independent contour coordinate and the native registration coordinate is
equivalent, at each good height, to vanishing of the off-line multiplicity ledger. -/
theorem classicalSContour_eq_Smult_iff_offLine_eq_zero
    {T : ℝ} (hT : GoodHeight T) :
    classicalSContour hT = Smult T ↔ offLineStripZeroCountMult T = 0 := by
  rw [classicalSContour_eq_Smult_add_offLine hT]
  constructor
  · intro h
    have : (offLineStripZeroCountMult T : ℝ) = 0 := by linarith
    exact_mod_cast this
  · intro h
    simp [h]

/-- Every analytic zero in a good finite strip is either represented by the native line ledger,
or it forces a detectable discrepancy between the independently continued global coordinate and
the native multiplicity coordinate.  Positivity of the analytic order prevents an off-line zero
from disappearing inside the summed defect. -/
theorem mem_stripZeroFinset_line_or_coordinate_defect
    {T : ℝ} (hT : GoodHeight T) {ρ : ℂ} (hρ : ρ ∈ stripZeroFinset T) :
    ρ.re = 1 / 2 ∨ classicalSContour hT ≠ Smult T := by
  by_cases hline : ρ.re = 1 / 2
  · exact Or.inl hline
  · right
    intro hcoordinate
    have hoff : offLineStripZeroCountMult T = 0 :=
      (classicalSContour_eq_Smult_iff_offLine_eq_zero hT).mp hcoordinate
    have hρoff : ρ ∈ (stripZeroFinset T).filter (fun z => z.re ≠ 1 / 2) :=
      Finset.mem_filter.mpr ⟨hρ, hline⟩
    have hterm : ZD.xiOrderNat ρ = 0 := by
      unfold offLineStripZeroCountMult at hoff
      exact (Finset.sum_eq_zero_iff_of_nonneg
        (fun z _ => Nat.zero_le (ZD.xiOrderNat z))).mp hoff ρ hρoff
    have hstrip := (stripZeroWindow_finite T).mem_toFinset.mp hρ
    exact (Nat.ne_of_gt (ZD.xiOrderNat_pos_of_mem_NontrivialZeros hstrip.1)) hterm

/-- Global upper-half-plane form of the coverage dichotomy.  Every nontrivial zero is enclosed
by a strictly higher good contour; hence it is either represented on the native line or supplies
an explicit good height at which the independent and native global coordinates differ. -/
theorem upper_nontrivialZero_line_or_globalCoordinateDefect
    {ρ : ℂ} (hρ : ρ ∈ ZD.NontrivialZeros) (hρim : 0 < ρ.im) :
    ρ.re = 1 / 2 ∨
      ∃ T : ℝ, ∃ hT : GoodHeight T,
        ρ.im < T ∧ classicalSContour hT ≠ Smult T := by
  obtain ⟨T, hρT, hT⟩ := exists_goodHeight_gt ρ.im
  have hρstrip : ρ ∈ stripZeroFinset T := by
    apply (stripZeroWindow_finite T).mem_toFinset.mpr
    exact ⟨hρ, hρim, hρT.le⟩
  rcases mem_stripZeroFinset_line_or_coordinate_defect hT hρstrip with hline | hdefect
  · exact Or.inl hline
  · exact Or.inr ⟨T, hT, hρT, hdefect⟩

/-- Any continuous logarithmic lift of the same contour with the same positive normalization is
the constructed lift.  Thus the continued argument has no branch choice left in it. -/
theorem contourLogLift_unique {T : ℝ} (hT : GoodHeight T) (L : C(unitInterval, ℂ))
    (hLexp : ∀ u, Complex.exp (L u) = riemannZeta (standardContour T u))
    (hLzero : L 0 = initialLog) : L = contourLogLift hT := by
  apply (Complex.isCoveringMap_exp.eq_liftPath_iff' (zetaContourPath_zero hT)).mpr
  constructor
  · funext u
    apply Subtype.ext
    exact hLexp u
  · exact hLzero

end CriticalLinePhasor.ContourArgument

#print axioms CriticalLinePhasor.ContourArgument.zeta_ne_zero_standardContour
#print axioms CriticalLinePhasor.ContourArgument.exp_contourLogLift
#print axioms CriticalLinePhasor.ContourArgument.exp_contourLogLift_one
#print axioms CriticalLinePhasor.ContourArgument.zeta_eq_norm_mul_exp_classicalSContour
#print axioms CriticalLinePhasor.ContourArgument.contour_phase_times_clock_eq_sign_rsZ
#print axioms CriticalLinePhasor.ContourArgument.exists_contourWindingIndex
#print axioms CriticalLinePhasor.ContourArgument.classicalSContour_eq_winding_sub_clock
#print axioms CriticalLinePhasor.ContourArgument.stripZeroWindow_finite
#print axioms CriticalLinePhasor.ContourArgument.rectangleBoundaryIntegral_strip_xi_divisor
#print axioms CriticalLinePhasor.ContourArgument.stripZeroCountMult_eq_onLine_add_offLine
#print axioms CriticalLinePhasor.ContourArgument.onLineStripZeroCountMult_eq_zeroEventCountMult
#print axioms CriticalLinePhasor.ContourArgument.stripZeroCountMult_eq_line_add_offLine
#print axioms CriticalLinePhasor.ContourArgument.contourLogLift_unique
#print axioms CriticalLinePhasor.ContourArgument.gammaLog_line_im
#print axioms CriticalLinePhasor.ContourArgument.xiPolynomialLog_line_im
#print axioms CriticalLinePhasor.ContourArgument.exp_xiContourLog
#print axioms CriticalLinePhasor.ContourArgument.halfContourIntegral_logDeriv_riemannXi_eq_lift_sub
#print axioms CriticalLinePhasor.ContourArgument.rectangleBoundaryIntegral_logDeriv_riemannXi_eq_contour_phase
#print axioms CriticalLinePhasor.ContourArgument.rectangleBoundaryIntegral_logDeriv_riemannXi
#print axioms CriticalLinePhasor.ContourArgument.contourWindingIndex_add_one_eq_stripZeroCountMult
#print axioms CriticalLinePhasor.ContourArgument.exists_goodHeight_gt
#print axioms CriticalLinePhasor.ContourArgument.offLineStripZeroCountMult_eq_winding_sub_line
#print axioms CriticalLinePhasor.ContourArgument.classicalSContour_eq_Smult_add_offLine
#print axioms CriticalLinePhasor.ContourArgument.classicalSContour_eq_Smult_iff_offLine_eq_zero
#print axioms CriticalLinePhasor.ContourArgument.mem_stripZeroFinset_line_or_coordinate_defect
#print axioms CriticalLinePhasor.ContourArgument.upper_nontrivialZero_line_or_globalCoordinateDefect
