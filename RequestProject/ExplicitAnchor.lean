import RequestProject.HerglotzSweep
import RequestProject.ConductionClockToeplitz
import RequestProject.WeilExplicitFormula
import Mathlib.NumberTheory.LSeries.Deriv
import Mathlib.NumberTheory.LSeries.Dirichlet

/-!
# The explicit anchor: the transported measure's coefficients from primes and Γ (ledger 628)

At an anchor `s` with `Re s < 0`, the reflected point `1 − s` has real part `> 1`, so the compiled
prime-side formula `logDeriv_xi_eq_arch_sub_lseries` (with `logDeriv_xi_reflect`) gives, on the open
half-plane `Re s < 0`,

  `ξ′/ξ(s) = −weilArch(1 − s) + LSeries Λ (1 − s)`   (`xiLogDeriv_eq_explicit`),

an identity of functions. Hence every jet of `ξ′/ξ` at `s` is a jet of this explicit function
(`jets_xiLogDeriv_eq_explicit`), and the prime side's jets are absolutely convergent L-series of
`Λ(n)(log n)^{m−1}` at `1 − s` (`jets_primeSide`, by Mathlib's `LSeries_hasDerivAt` through the reflection).
The transported measure's Toeplitz coefficients at such an anchor split into an Archimedean part and a
prime part (`explicitAnchor_toeplitzCoeff_split`), and the Herglotz function of the sweep is the explicit
function at the moved anchor as long as the moved anchor stays in `Re < 0` (`xiHerglotz_explicit`).
No zero enters any hypothesis: the half-plane `Re < 0` is zero-free by the definition of the zero set.
-/

open Complex Finset LSeries
open CriticalLinePhasor.ContourArgument

namespace CriticalLinePhasor.SeatingLedger

/-- The prime side at the reflected point, `Σ Λ(n) n^{s−1} = LSeries Λ (1 − s)`. -/
noncomputable def primeSide (s : ℂ) : ℂ := LSeries vonMangoldtC (1 - s)

/-- The Archimedean side at the reflected point. -/
noncomputable def archSide (s : ℂ) : ℂ := -weilArch (1 - s)

/-- The explicit function equal to `ξ′/ξ` on `Re s < 0`. -/
noncomputable def explicitLogDeriv (s : ℂ) : ℂ := archSide s + primeSide s

theorem explicitLogDeriv_eq : explicitLogDeriv = archSide + primeSide := rfl

theorem isOpen_left : IsOpen {s : ℂ | s.re < 0} := isOpen_lt Complex.continuous_re continuous_const

theorem abscissa_vonMangoldtC_le_one : abscissaOfAbsConv vonMangoldtC ≤ 1 :=
  LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable
    (fun y hy => ArithmeticFunction.LSeriesSummable_vonMangoldt (by simpa using hy))

theorem one_sub_re_gt {s : ℂ} (hs : s.re < 0) : (1 : ℝ) < (1 - s).re := by
  simp only [Complex.sub_re, Complex.one_re]; linarith

theorem abscissa_lt_one_sub_re {s : ℂ} (hs : s.re < 0) {f : ℕ → ℂ} (hf : abscissaOfAbsConv f ≤ 1) :
    abscissaOfAbsConv f < (1 - s).re := by
  calc abscissaOfAbsConv f ≤ 1 := hf
    _ < ((1 - s).re : EReal) := by exact_mod_cast one_sub_re_gt hs

/-- **`ξ′/ξ` is the explicit function on `Re s < 0`.** -/
theorem xiLogDeriv_eq_explicit {s : ℂ} (hs : s.re < 0) :
    logDeriv ZD.riemannXi s = explicitLogDeriv s := by
  rw [logDeriv_xi_reflect, logDeriv_xi_eq_arch_sub_lseries (one_sub_re_gt hs)]
  unfold explicitLogDeriv archSide primeSide
  ring

/-- The jets of `ξ′/ξ` at an explicit anchor are the jets of the explicit function. -/
theorem jets_xiLogDeriv_eq_explicit {s : ℂ} (hs : s.re < 0) :
    jets (logDeriv ZD.riemannXi) s = jets explicitLogDeriv s := by
  have hev : logDeriv ZD.riemannXi =ᶠ[nhds s] explicitLogDeriv := by
    filter_upwards [isOpen_left.mem_nhds hs] with s' hs'
    exact xiLogDeriv_eq_explicit hs'
  funext m
  cases m with
  | zero => rfl
  | succ m =>
    simp only [jets]
    rw [iteratedDeriv_congr_nhds hev m]

/-- The prime side differentiates termwise through the reflection: `∂_s LSeries f (1 − s) = LSeries (log·f) (1 − s)`. -/
theorem lseries_reflected_hasDerivAt {s : ℂ} (hs : s.re < 0) (f : ℕ → ℂ)
    (hf : abscissaOfAbsConv f ≤ 1) :
    HasDerivAt (fun s => LSeries f (1 - s)) (LSeries (logMul f) (1 - s)) s := by
  have h1 : HasDerivAt (fun s : ℂ => 1 - s) (-1) s := (hasDerivAt_id s).const_sub 1
  have := (LSeries_hasDerivAt (abscissa_lt_one_sub_re hs hf)).comp s h1
  exact this.congr_deriv (by ring)

theorem lseries_reflected_iteratedDeriv {s : ℂ} (hs : s.re < 0) (f : ℕ → ℂ)
    (hf : abscissaOfAbsConv f ≤ 1) (k : ℕ) :
    iteratedDeriv k (fun s => LSeries f (1 - s)) s = LSeries (logMul^[k] f) (1 - s) := by
  induction k generalizing f s with
  | zero => simp
  | succ k ih =>
    rw [iteratedDeriv_succ']
    have hev : deriv (fun s => LSeries f (1 - s)) =ᶠ[nhds s] fun s => LSeries (logMul f) (1 - s) := by
      filter_upwards [isOpen_left.mem_nhds hs] with s' hs'
      exact (lseries_reflected_hasDerivAt hs' f hf).deriv
    rw [iteratedDeriv_congr_nhds hev k,
      ih hs (logMul f) (by rw [LSeries.abscissaOfAbsConv_logMul]; exact hf), Function.iterate_succ_apply]

/-- **The prime side's jets are absolutely convergent L-series**:
`jets primeSide s (m+1) = (−1)^m/m! · Σ_n Λ(n) (log n)^m n^{s−1}`. -/
theorem jets_primeSide {s : ℂ} (hs : s.re < 0) (m : ℕ) :
    jets primeSide s (m + 1)
      = (-1) ^ m / (m.factorial : ℂ) * LSeries (logMul^[m] vonMangoldtC) (1 - s) := by
  simp only [jets]
  rw [show primeSide = fun s => LSeries vonMangoldtC (1 - s) from rfl,
    lseries_reflected_iteratedDeriv hs vonMangoldtC abscissa_vonMangoldtC_le_one m]

/-- The half-plane `Re s ≤ 0` is zero-free. -/
theorem notMem_nontrivialZeros_of_re_nonpos {s : ℂ} (hs : s.re ≤ 0) : s ∉ ZD.NontrivialZeros := by
  intro h
  obtain ⟨h1, -, -⟩ := h
  linarith

/-- The half-plane `Re s ≥ 1` is zero-free. -/
theorem notMem_nontrivialZeros_of_one_le_re {s : ℂ} (hs : 1 ≤ s.re) : s ∉ ZD.NontrivialZeros := by
  intro h
  obtain ⟨-, h2, -⟩ := h
  linarith

theorem primeSide_differentiableOn : DifferentiableOn ℂ primeSide {s : ℂ | s.re < 0} := by
  intro s hs
  exact (lseries_reflected_hasDerivAt hs vonMangoldtC abscissa_vonMangoldtC_le_one).differentiableAt
    |>.differentiableWithinAt

theorem xiLogDeriv_differentiableOn :
    DifferentiableOn ℂ (logDeriv ZD.riemannXi) {s : ℂ | s.re < 0} := by
  have hξ : AnalyticOnNhd ℂ ZD.riemannXi Set.univ :=
    ZD.riemannXi_differentiable.differentiableOn.analyticOnNhd isOpen_univ
  have hd : DifferentiableOn ℂ (deriv ZD.riemannXi) {s : ℂ | s.re < 0} :=
    (hξ.deriv.differentiableOn).mono (Set.subset_univ _)
  have hξ' : DifferentiableOn ℂ ZD.riemannXi {s : ℂ | s.re < 0} :=
    ZD.riemannXi_differentiable.differentiableOn
  refine (hd.div hξ' ?_).congr (fun s _ => logDeriv_apply _ _)
  intro s hs
  intro h0
  exact notMem_nontrivialZeros_of_re_nonpos (le_of_lt hs) ((ZD.riemannXi_eq_zero_iff s).mp h0)

theorem archSide_contDiffOn : ContDiffOn ℂ ⊤ archSide {s : ℂ | s.re < 0} := by
  have hL : ContDiffOn ℂ ⊤ (logDeriv ZD.riemannXi) {s : ℂ | s.re < 0} :=
    xiLogDeriv_differentiableOn.contDiffOn isOpen_left
  have hP : ContDiffOn ℂ ⊤ primeSide {s : ℂ | s.re < 0} :=
    primeSide_differentiableOn.contDiffOn isOpen_left
  refine (hL.sub hP).congr (fun s hs => ?_)
  rw [xiLogDeriv_eq_explicit hs]
  unfold explicitLogDeriv
  ring

theorem primeSide_contDiffOn : ContDiffOn ℂ ⊤ primeSide {s : ℂ | s.re < 0} :=
  primeSide_differentiableOn.contDiffOn isOpen_left

/-- The jets of the explicit function split into Archimedean and prime jets. -/
theorem jets_explicit_split {s : ℂ} (hs : s.re < 0) :
    jets explicitLogDeriv s = jets archSide s + jets primeSide s := by
  funext m
  cases m with
  | zero => simp [jets]
  | succ m =>
    simp only [jets, Pi.add_apply]
    have hU := isOpen_left
    have hsU : s ∈ {s : ℂ | s.re < 0} := hs
    have hA : ContDiffWithinAt ℂ m archSide {s : ℂ | s.re < 0} s :=
      (archSide_contDiffOn s hsU).of_le le_top
    have hP : ContDiffWithinAt ℂ m primeSide {s : ℂ | s.re < 0} s :=
      (primeSide_contDiffOn s hsU).of_le le_top
    rw [explicitLogDeriv_eq, ← iteratedDerivWithin_of_isOpen (f := archSide + primeSide) hU hsU,
      ← iteratedDerivWithin_of_isOpen (f := archSide) hU hsU,
      ← iteratedDerivWithin_of_isOpen (f := primeSide) hU hsU,
      iteratedDerivWithin_add hsU hU.uniqueDiffOn hA hP]
    ring

/-- **The explicit anchor's jets**: for `Re s < 0`,
`jets (ξ′/ξ) s (m+1) = jets archSide s (m+1) + (−1)^m/m! · Σ_n Λ(n)(log n)^m n^{s−1}`. -/
theorem jets_xiLogDeriv_explicit {s : ℂ} (hs : s.re < 0) (m : ℕ) :
    jets (logDeriv ZD.riemannXi) s (m + 1)
      = jets archSide s (m + 1)
        + (-1) ^ m / (m.factorial : ℂ) * LSeries (logMul^[m] vonMangoldtC) (1 - s) := by
  rw [jets_xiLogDeriv_eq_explicit hs, jets_explicit_split hs, Pi.add_apply, jets_primeSide hs m]

/-- **The transported measure's Toeplitz coefficients at an explicit anchor** split into an
Archimedean part and a prime part, each built from explicit jets. -/
theorem explicitAnchor_toeplitzCoeff_split {s : ℂ} (hs : s.re < 0) (d : ℂ) (k : ℕ) :
    toeplitzCoeff d (jets (logDeriv ZD.riemannXi) s) k
      = toeplitzCoeff d (jets archSide s) k + toeplitzCoeff d (jets primeSide s) k := by
  rw [jets_xiLogDeriv_eq_explicit hs, jets_explicit_split hs, toeplitzCoeff_add]

/-- The prime part's higher coefficients, written out: a finite binomial combination of the
absolutely convergent L-series `LSeries (logMul^[j] Λ) (1 − s)`. -/
theorem primeSide_toeplitzCoeff_succ {s : ℂ} (hs : s.re < 0) (d : ℂ) (k : ℕ) :
    toeplitzCoeff d (jets primeSide s) (k + 1)
      = ∑ i ∈ range (k + 1), (k.choose i : ℂ) * d ^ (k - i) * (-1) ^ i
          * ((-1) ^ (k + 1 - i) / ((k + 1 - i).factorial : ℂ)
              * LSeries (logMul^[k + 1 - i] vonMangoldtC) (1 - s)) := by
  simp only [toeplitzCoeff]
  refine Finset.sum_congr rfl (fun i hi => ?_)
  rw [Finset.mem_range] at hi
  rw [show k + 2 - i = (k + 1 - i) + 1 by omega, jets_primeSide hs]

/-- **The sweep at an explicit anchor**: while the moved anchor stays in `Re < 0`, the Herglotz
function is the explicit function at the moved anchor. -/
theorem xiHerglotz_explicit {s z : ℂ} (hs : s.re < 0) (hz : 1 + z ≠ 0)
    (hsz : (movedAnchor s z).re < 0) :
    xiHerglotz s z = 2 / ((2 * s.re - 1 : ℝ) : ℂ)
      * (explicitLogDeriv (movedAnchor s z) - I * ((explicitLogDeriv s).im : ℂ)) := by
  have hc : 1 - (starRingEnd ℂ) s ∉ ZD.NontrivialZeros := by
    apply notMem_nontrivialZeros_of_one_le_re
    simp only [Complex.sub_re, Complex.one_re, Complex.conj_re]
    linarith
  rw [xiHerglotz_eq' (notMem_nontrivialZeros_of_re_nonpos hs.le) hc hz
    (notMem_nontrivialZeros_of_re_nonpos hsz.le) (by intro h; linarith),
    xiLogDeriv_eq_explicit hs, xiLogDeriv_eq_explicit hsz]

end CriticalLinePhasor.SeatingLedger

#print axioms CriticalLinePhasor.SeatingLedger.xiLogDeriv_eq_explicit
#print axioms CriticalLinePhasor.SeatingLedger.jets_primeSide
#print axioms CriticalLinePhasor.SeatingLedger.jets_xiLogDeriv_explicit
#print axioms CriticalLinePhasor.SeatingLedger.explicitAnchor_toeplitzCoeff_split
#print axioms CriticalLinePhasor.SeatingLedger.xiHerglotz_explicit
