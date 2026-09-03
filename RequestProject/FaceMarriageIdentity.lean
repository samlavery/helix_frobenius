import RequestProject.SeatMassEtaForm
import RequestProject.SeatingFloorOdd

/-!
# The face-marriage identity at finite conduction set `Q` (HP_SKELETON [HP-LEAF]; ledger 531)

The conduction clock of `q` is `1 − q^{1−s}`: multiplying `ζ` by it converts the fiber into a
closed-cell bank of period `q` (cell sum zero), convergent on `Re s > 0`; `q = 2` is the eta bank
(`zeta_logDeriv_eq_etaLim`).  Its log-derivative splits as DC plus face,
`logDeriv (1 − q^{1−·}) s = −log q + log q/(1 − q^{1−s})`, and the face is minus the reflected
geometric term `log q · x/(1 − x)`, `x = q^{s−1}`, whose expansion `Σ_{k≥1} log q · q^{−k(1−s)}` is
the von Mangoldt sum over the powers of `q` read at the reflected point `1 − s`.

With the functional equation in the form `logDeriv ζ(s) + logDeriv ζ(1−s) = −(E(s) + E(1−s))`,
`E = 1/s + 1/(s−1) − ½ log π + ½ Γ′/Γ(s/2)` (from `logDeriv_riemannXi_splice` and
`xiLogDeriv_odd`), the closed-cell bank `(∏_{q∈Q}(1 − q^{1−s}))·ζ(s)` satisfies, exactly,

  `logDeriv(closed-cell bank)(s) + Σ_{q∈Q} log q = −(E(s) + E(1−s)) − [logDeriv ζ(1−s) + P_Q(1−s)]`,

`P_Q(w) = Σ_{q∈Q} log q · q^{−w}/(1 − q^{−w})` the `Q`-smooth von Mangoldt sum.  So the closed-cell
face with its DC removed is the Archimedean/ends pair minus the reflected Euler defect.  att531
measured the defect: it is dominated by the END term `Q^{1−w}/(1−w)` of the truncated explicit
formula (the pole at `s = 0`, `w = 1`, read at the cutoff), and only after subtracting it does the
remainder carry the zeros' decay `Q^{½ − Re w}`.

No `sorry`, no `axiom`.
-/

open Complex Filter Topology

noncomputable section

namespace CriticalLinePhasor.SeatingLedger

/-- The conduction clock of `q`: `1 − q^{1−s}`. -/
def conductionClock (q : ℕ) (s : ℂ) : ℂ := 1 - (q : ℂ) ^ ((1 : ℂ) - s)

theorem conductionClock_hasDerivAt {q : ℕ} (hq : 1 < q) (s : ℂ) :
    HasDerivAt (conductionClock q)
      ((q : ℂ) ^ ((1 : ℂ) - s) * ((Real.log q : ℝ) : ℂ)) s := by
  have hq0 : (q : ℂ) ≠ 0 := by exact_mod_cast (by omega : q ≠ 0)
  have h1 : HasDerivAt (fun w : ℂ => (1 : ℂ) - w) (-1) s := (hasDerivAt_id s).const_sub 1
  have h2 := h1.const_cpow (Or.inl hq0)
  have h3 := (hasDerivAt_const s (1 : ℂ)).sub h2
  unfold conductionClock
  refine h3.congr_deriv ?_
  rw [← Complex.natCast_log]
  ring

theorem conductionClock_norm_cpow {q : ℕ} (hq : 1 < q) {s : ℂ} (hs1 : s.re < 1) :
    1 < ‖(q : ℂ) ^ ((1 : ℂ) - s)‖ := by
  rw [Complex.norm_natCast_cpow_of_pos (by omega : 0 < q)]
  have hre : ((1 : ℂ) - s).re = 1 - s.re := by simp
  rw [hre]
  exact Real.one_lt_rpow (by exact_mod_cast hq) (by linarith)

theorem conductionClock_ne_zero {q : ℕ} (hq : 1 < q) {s : ℂ} (hs1 : s.re < 1) :
    conductionClock q s ≠ 0 := by
  unfold conductionClock
  intro h
  have h1 : (q : ℂ) ^ ((1 : ℂ) - s) = 1 := by linear_combination -h
  have hn := conductionClock_norm_cpow hq hs1
  rw [h1, norm_one] at hn
  exact lt_irrefl _ hn

/-- **DC plus face**: `logDeriv (1 − q^{1−·}) s = −log q + log q/(1 − q^{1−s})`. -/
theorem logDeriv_conductionClock {q : ℕ} (hq : 1 < q) {s : ℂ} (hs1 : s.re < 1) :
    logDeriv (conductionClock q) s
      = -((Real.log q : ℝ) : ℂ) + ((Real.log q : ℝ) : ℂ) / conductionClock q s := by
  have hne := conductionClock_ne_zero hq hs1
  rw [logDeriv_apply, (conductionClock_hasDerivAt hq s).deriv]
  unfold conductionClock at hne ⊢
  field_simp
  ring

theorem reflected_norm_lt_one {q : ℕ} (hq : 1 < q) {s : ℂ} (hs1 : s.re < 1) :
    ‖(q : ℂ) ^ (s - 1)‖ < 1 := by
  rw [Complex.norm_natCast_cpow_of_pos (by omega : 0 < q)]
  have hre : (s - 1).re = s.re - 1 := by simp
  rw [hre]
  exact Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hq) (by linarith)

theorem reflected_ne_one {q : ℕ} (hq : 1 < q) {s : ℂ} (hs1 : s.re < 1) :
    (1 : ℂ) - (q : ℂ) ^ (s - 1) ≠ 0 := by
  intro h
  have h1 : (q : ℂ) ^ (s - 1) = 1 := by linear_combination -h
  have hn := reflected_norm_lt_one hq hs1
  rw [h1, norm_one] at hn
  exact lt_irrefl _ hn

/-- **The face is the reflected geometric term**: `log q/(1 − q^{1−s}) = −log q · x/(1 − x)`,
`x = q^{s−1}`. -/
theorem conduction_face_eq_reflected {q : ℕ} (hq : 1 < q) {s : ℂ} (hs1 : s.re < 1) :
    ((Real.log q : ℝ) : ℂ) / conductionClock q s
      = -(((Real.log q : ℝ) : ℂ) * (q : ℂ) ^ (s - 1) / (1 - (q : ℂ) ^ (s - 1))) := by
  have hq0 : (q : ℂ) ≠ 0 := by exact_mod_cast (by omega : q ≠ 0)
  have hx : (q : ℂ) ^ ((1 : ℂ) - s) = ((q : ℂ) ^ (s - 1))⁻¹ := by
    rw [← Complex.cpow_neg]
    congr 1
    ring
  have hx0 : (q : ℂ) ^ (s - 1) ≠ 0 := by
    rw [Ne, Complex.cpow_eq_zero_iff]
    rintro ⟨h, _⟩
    exact hq0 h
  have hx1 := reflected_ne_one hq hs1
  unfold conductionClock
  rw [hx]
  have key : (1 : ℂ) - ((q : ℂ) ^ (s - 1))⁻¹ = ((q : ℂ) ^ (s - 1) - 1) / (q : ℂ) ^ (s - 1) := by
    rw [sub_div, div_self hx0, one_div]
  rw [key, div_div_eq_mul_div, ← neg_sub (1 : ℂ) ((q : ℂ) ^ (s - 1)), div_neg]

/-- **The von Mangoldt reading of the face**: `log q · x/(1 − x) = Σ_{k≥0} log q · x^{k+1}`,
i.e. `Σ_{k≥1} Λ(q^k) q^{−k(1−s)}` — the reflected Euler sum over the powers of `q`. -/
theorem conduction_face_hasSum {q : ℕ} (hq : 1 < q) {s : ℂ} (hs1 : s.re < 1) :
    HasSum (fun k : ℕ => ((Real.log q : ℝ) : ℂ) * ((q : ℂ) ^ (s - 1)) ^ (k + 1))
      (((Real.log q : ℝ) : ℂ) * (q : ℂ) ^ (s - 1) / (1 - (q : ℂ) ^ (s - 1))) := by
  have hxn := reflected_norm_lt_one hq hs1
  have h := ((hasSum_geometric_of_norm_lt_one hxn).mul_left ((q : ℂ) ^ (s - 1))).mul_left
    ((Real.log q : ℝ) : ℂ)
  have hf : (fun k : ℕ => ((Real.log q : ℝ) : ℂ) * ((q : ℂ) ^ (s - 1)) ^ (k + 1))
      = fun i : ℕ => ((Real.log q : ℝ) : ℂ) * ((q : ℂ) ^ (s - 1) * ((q : ℂ) ^ (s - 1)) ^ i) := by
    funext k
    ring
  have hv : ((Real.log q : ℝ) : ℂ) * (q : ℂ) ^ (s - 1) / (1 - (q : ℂ) ^ (s - 1))
      = ((Real.log q : ℝ) : ℂ) * ((q : ℂ) ^ (s - 1) * (1 - (q : ℂ) ^ (s - 1))⁻¹) := by
    ring
  rw [hf, hv]
  exact h

/-- The ends and the Archimedean clock: `1/s + 1/(s−1) − ½ log π + ½ Γ′/Γ(s/2)`. -/
def endsArch (s : ℂ) : ℂ :=
  1 / s + 1 / (s - 1) - ((Real.log Real.pi : ℝ) : ℂ) / 2 + logDeriv Complex.Gamma (s / 2) / 2

/-- `ζ(s) ≠ 0 ⟹ ζ(1−s) ≠ 0` in the strip, through the completed function. -/
theorem zeta_one_sub_ne_zero {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1)
    (hz : riemannZeta s ≠ 0) : riemannZeta (1 - s) ≠ 0 := by
  have hs1' : s ≠ 1 := by
    intro h
    rw [h] at hs1
    simp at hs1
  have hs0' : s ≠ 0 := by
    intro h
    rw [h] at hs0
    simp at hs0
  have hre' : 0 < (1 - s).re := by
    simp
    linarith
  have hne1' : (1 : ℂ) - s ≠ 1 := by
    intro h
    apply hs0'
    linear_combination -h
  intro h0
  have hξ : ZD.riemannXi (1 - s) = 0 := by
    rw [riemannXi_eq_poly_mul_Gammaℝ_mul_zeta hre' hne1', h0]
    ring
  rw [ZD.ZeroCount.riemannXi_one_sub, riemannXi_eq_poly_mul_Gammaℝ_mul_zeta hs0 hs1'] at hξ
  have hpoly : s * (s - 1) / 2 ≠ 0 :=
    div_ne_zero (mul_ne_zero hs0' (sub_ne_zero.mpr hs1')) two_ne_zero
  have hΓ : Gammaℝ s ≠ 0 := Gammaℝ_ne_zero_of_re_pos hs0
  exact (mul_ne_zero hpoly (mul_ne_zero hΓ hz)) hξ

/-- **The functional equation in log-derivative form**:
`logDeriv ζ(s) + logDeriv ζ(1−s) = −(E(s) + E(1−s))`. -/
theorem logDeriv_zeta_add_reflected {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1)
    (hz : riemannZeta s ≠ 0) :
    logDeriv riemannZeta s + logDeriv riemannZeta (1 - s)
      = -(endsArch s + endsArch (1 - s)) := by
  have hs1' : s ≠ 1 := by
    intro h
    rw [h] at hs1
    simp at hs1
  have hs0' : s ≠ 0 := by
    intro h
    rw [h] at hs0
    simp at hs0
  have hre' : 0 < (1 - s).re := by
    simp
    linarith
  have hne1' : (1 : ℂ) - s ≠ 1 := by
    intro h
    apply hs0'
    linear_combination -h
  have hz' := zeta_one_sub_ne_zero hs0 hs1 hz
  have h1 := logDeriv_riemannXi_splice hs0 hs1' hz
  have h2 := logDeriv_riemannXi_splice hre' hne1' hz'
  have hodd := xiLogDeriv_odd s
  unfold endsArch
  linear_combination (-1 : ℂ) * h1 + (-1 : ℂ) * h2 + hodd

/-- The reflected `Q`-smooth von Mangoldt sum, in closed form. -/
def reflectedEulerSum (Q : Finset ℕ) (s : ℂ) : ℂ :=
  ∑ q ∈ Q, ((Real.log q : ℝ) : ℂ) * (q : ℂ) ^ (s - 1) / (1 - (q : ℂ) ^ (s - 1))

/-- The closed-cell bank of conduction set `Q`: `(∏_{q∈Q}(1 − q^{1−s}))·ζ(s)`. -/
def closedCellBank (Q : Finset ℕ) (s : ℂ) : ℂ := (∏ q ∈ Q, conductionClock q s) * riemannZeta s

/-- **The face-marriage identity at finite `Q`.**  The closed-cell face with its DC removed is
the Archimedean/ends pair minus the reflected Euler defect. -/
theorem closedCellBank_marriage (Q : Finset ℕ) (hQ : ∀ q ∈ Q, 1 < q) {s : ℂ}
    (hs0 : 0 < s.re) (hs1 : s.re < 1) (hz : riemannZeta s ≠ 0) :
    logDeriv (closedCellBank Q) s + ∑ q ∈ Q, ((Real.log q : ℝ) : ℂ)
      = -(endsArch s + endsArch (1 - s))
        - (logDeriv riemannZeta (1 - s) + reflectedEulerSum Q s) := by
  have hs1' : s ≠ 1 := by
    intro h
    rw [h] at hs1
    simp at hs1
  have hne : ∀ q ∈ Q, conductionClock q s ≠ 0 :=
    fun q hq => conductionClock_ne_zero (hQ q hq) hs1
  have hdiff : ∀ q ∈ Q, DifferentiableAt ℂ (conductionClock q) s :=
    fun q hq => (conductionClock_hasDerivAt (hQ q hq) s).differentiableAt
  have hprod_ne : (∏ q ∈ Q, conductionClock q s) ≠ 0 := Finset.prod_ne_zero_iff.mpr hne
  have hprod_diff : DifferentiableAt ℂ (fun w => ∏ q ∈ Q, conductionClock q w) s :=
    DifferentiableAt.fun_finsetProd hdiff
  have hsplit : logDeriv (closedCellBank Q) s
      = logDeriv (fun w => ∏ q ∈ Q, conductionClock q w) s + logDeriv riemannZeta s := by
    unfold closedCellBank
    exact logDeriv_mul (f := fun w => ∏ q ∈ Q, conductionClock q w) (g := riemannZeta) s
      hprod_ne hz hprod_diff (differentiableAt_riemannZeta hs1')
  have hprodlog : logDeriv (fun w => ∏ q ∈ Q, conductionClock q w) s
      = ∑ q ∈ Q, logDeriv (conductionClock q) s :=
    logDeriv_prod hne hdiff
  have hterm : ∀ q ∈ Q, logDeriv (conductionClock q) s
      = -((Real.log q : ℝ) : ℂ)
        - ((Real.log q : ℝ) : ℂ) * (q : ℂ) ^ (s - 1) / (1 - (q : ℂ) ^ (s - 1)) := by
    intro q hq
    rw [logDeriv_conductionClock (hQ q hq) hs1, conduction_face_eq_reflected (hQ q hq) hs1]
    ring
  have hFE := logDeriv_zeta_add_reflected hs0 hs1 hz
  rw [hsplit, hprodlog, Finset.sum_congr rfl hterm, Finset.sum_sub_distrib,
    Finset.sum_neg_distrib]
  unfold reflectedEulerSum
  linear_combination hFE

end CriticalLinePhasor.SeatingLedger

#print axioms CriticalLinePhasor.SeatingLedger.logDeriv_conductionClock
#print axioms CriticalLinePhasor.SeatingLedger.conduction_face_hasSum
#print axioms CriticalLinePhasor.SeatingLedger.logDeriv_zeta_add_reflected
#print axioms CriticalLinePhasor.SeatingLedger.closedCellBank_marriage
