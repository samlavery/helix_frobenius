import RequestProject.IntegratedRegistrationReduction

/-!
# Harmonized-cell telescoping: local residue control closes the S(t) identification

The final wiring of the `t`-level route.  The native registration ledger
`Smult t = N_mult t − 1 − ϑ(t)/π` is integrable on every interval (monotone step count
minus continuous clock), and a **boundary-to-global transfer** theorem shows that
sublinearity of its running integral follows from two LOCAL statements about a
harmonized cell decomposition `c : ℕ → ℝ` of the height axis:

* accumulated residue is sublinear **at cell boundaries** — `∫₀^{c n} Smult = o(c n)`;
* the single-cell absolute mass is sublinear — `∫_{c n}^{c (n+1)} |Smult| = o(c n)`.

This is the precise content of "no residue on a harmonized carrier": residues balance
the clock at carrier scale, so nothing accumulates between boundaries, and the running
integral of the ledger collapses to one boundary value plus one partial cell.

The capstone composes this with the compiled exact criterion
(`globalCoordinateIdentification_iff_integral_sublinear`) and with Littlewood's
classical unconditional bound `∫₀^T S(t) dt = O(log T)` — consumed in its native
decomposition form, since `S = Smult + offLineStripZeroCountMult` at every good height
by the compiled registration law — to conclude the full global coordinate
identification `classicalSContour = Smult` at every good height.

Proven in this file, unconditionally: the monotonicity and interval integrability of
both ledgers, the boundary-to-global transfer, and the complete conditional wiring.
Not proven in this file: the two local cell statements (the harmonized-carrier residue
balance — the thread's remaining mathematics, now localized to one cell) and the
Littlewood input (classical, cited, unconditional in the literature).
-/

open Complex Set MeasureTheory Filter Asymptotics
open intervalIntegral

namespace CriticalLinePhasor.ContourArgument

open CriticalLinePhasor CriticalLinePhasor.CarrierScale CriticalLinePhasor.ResidueJump

/-! ## Integrability of the two ledgers -/

/-- The multiplicity-weighted native count is monotone in the height. -/
theorem zeroEventCountMult_mono {t t' : ℝ} (h : t ≤ t') :
    zeroEventCountMult t ≤ zeroEventCountMult t' := by
  classical
  unfold zeroEventCountMult
  apply Finset.sum_le_sum_of_subset
  intro γ hγ
  rw [Set.Finite.mem_toFinset] at hγ ⊢
  exact ⟨⟨hγ.1.1, hγ.1.2.trans h⟩, hγ.2⟩

/-- The native ledger `Smult` is integrable on every interval: a monotone step count
minus a continuous clock. -/
theorem smult_intervalIntegrable (a b : ℝ) :
    IntervalIntegrable Smult volume a b := by
  have hstep : Smult = fun t =>
      ((zeroEventCountMult t : ℝ)) - (1 + theta t / Real.pi) := by
    funext t
    unfold CriticalLinePhasor.ResidueJump.Smult
    ring
  rw [hstep]
  have hm : Monotone fun t : ℝ => ((zeroEventCountMult t : ℝ)) :=
    fun _ _ htt => Nat.cast_le.mpr (zeroEventCountMult_mono htt)
  have h2 : IntervalIntegrable (fun t : ℝ => 1 + theta t / Real.pi) volume a b :=
    (continuous_const.add (theta_continuous.div_const _)).intervalIntegrable a b
  exact hm.intervalIntegrable.sub h2

/-- The off-line defect ledger is integrable on every interval (monotone). -/
theorem offLine_intervalIntegrable (a b : ℝ) :
    IntervalIntegrable (fun t : ℝ => (offLineStripZeroCountMult t : ℝ)) volume a b := by
  have hm : Monotone fun t : ℝ => ((offLineStripZeroCountMult t : ℝ)) :=
    fun _ _ htt => Nat.cast_le.mpr (offLineStripZeroCountMult_mono htt)
  exact hm.intervalIntegrable

/-! ## The boundary-to-global transfer -/

/-- **Boundary-to-global transfer.**  If a locally integrable function has sublinear
running integral at the boundaries of an unbounded monotone cell decomposition, and
sublinear absolute mass on each single cell, then its running integral is sublinear at
every height: the integral to `T` is one boundary value plus one partial-cell term. -/
theorem integral_sublinear_of_boundary_and_cell
    {f : ℝ → ℝ} (hInt : ∀ a b : ℝ, IntervalIntegrable f volume a b)
    {c : ℕ → ℝ} (hmono : Monotone c) (hc0 : 0 ≤ c 0)
    (htop : Tendsto c atTop atTop)
    (hbd : (fun n => ∫ t in (0:ℝ)..(c n), f t) =o[atTop] fun n => c n)
    (hcell : (fun n => ∫ t in (c n)..(c (n + 1)), |f t|) =o[atTop] fun n => c n) :
    (fun T => ∫ t in (0:ℝ)..T, f t) =o[atTop] fun T : ℝ => T := by
  classical
  rw [isLittleO_iff]
  intro ε hε
  have hbd' := (isLittleO_iff.mp hbd) (show (0:ℝ) < ε / 2 by positivity)
  have hcell' := (isLittleO_iff.mp hcell) (show (0:ℝ) < ε / 2 by positivity)
  rw [eventually_atTop] at hbd' hcell'
  obtain ⟨N₁, hN₁⟩ := hbd'
  obtain ⟨N₂, hN₂⟩ := hcell'
  set N : ℕ := max N₁ N₂ with hNdef
  rw [eventually_atTop]
  refine ⟨max (c N) 0 + 1, fun T hT => ?_⟩
  have hmax : max (c N) 0 ≤ T := by linarith
  have hTN : c N ≤ T := (le_max_left _ _).trans hmax
  have hT0 : (0:ℝ) < T := by
    have h0 : (0:ℝ) ≤ max (c N) 0 := le_max_right _ _
    linarith
  -- the enclosing cell: least `k` with `T < c k`, then `n := k − 1`
  have hex : ∃ k, T < c k := (htop.eventually_gt_atTop T).exists
  set k : ℕ := Nat.find hex with hkdef
  have hk : T < c k := Nat.find_spec hex
  have hNk : N < k := by
    by_contra hle
    push_neg at hle
    exact absurd (le_trans (hmono hle) hTN) (not_le.mpr hk)
  have hkpos : 0 < k := lt_of_le_of_lt (Nat.zero_le N) hNk
  set n : ℕ := k - 1 with hndef
  have hkn : k = n + 1 := (Nat.succ_pred_eq_of_pos hkpos).symm
  have hcnT : c n ≤ T := by
    by_contra hlt
    push_neg at hlt
    exact Nat.find_min hex (show n < Nat.find hex by rw [← hkdef]; omega) hlt
  have hTn1 : T ≤ c (n + 1) := by
    rw [← hkn]
    exact hk.le
  have hnN : N ≤ n := by omega
  have hcn0 : (0:ℝ) ≤ c n := hc0.trans (hmono (Nat.zero_le n))
  -- decompose the running integral at the enclosing boundary
  have hsplit : ∫ t in (0:ℝ)..T, f t
      = (∫ t in (0:ℝ)..(c n), f t) + ∫ t in (c n)..T, f t :=
    (integral_add_adjacent_intervals (hInt 0 (c n)) (hInt (c n) T)).symm
  -- the partial-cell term is bounded by the single-cell absolute mass
  have habs : |∫ t in (c n)..T, f t| ≤ ∫ t in (c n)..T, |f t| :=
    intervalIntegral.abs_integral_le_integral_abs hcnT
  have htail : ∫ t in (c n)..T, |f t| ≤ ∫ t in (c n)..(c (n + 1)), |f t| := by
    have hadj : (∫ t in (c n)..T, |f t|) + ∫ t in T..(c (n + 1)), |f t|
        = ∫ t in (c n)..(c (n + 1)), |f t| :=
      integral_add_adjacent_intervals ((hInt (c n) T).abs) ((hInt T (c (n + 1))).abs)
    have hnn : 0 ≤ ∫ t in T..(c (n + 1)), |f t| :=
      intervalIntegral.integral_nonneg hTn1 (fun t _ => abs_nonneg _)
    linarith
  -- the two sublinear bounds at the enclosing cell index
  have hb := hN₁ n (le_trans (le_max_left N₁ N₂) hnN)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hcn0] at hb
  have hcl := hN₂ n (le_trans (le_max_right N₁ N₂) hnN)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hcn0] at hcl
  have hcell_le : ∫ t in (c n)..(c (n + 1)), |f t| ≤ ε / 2 * c n :=
    (le_abs_self _).trans hcl
  have hpartial : |∫ t in (c n)..T, f t| ≤ ε / 2 * c n :=
    (habs.trans htail).trans hcell_le
  -- assemble
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hT0, hsplit]
  have htri : |(∫ t in (0:ℝ)..(c n), f t) + ∫ t in (c n)..T, f t|
      ≤ |∫ t in (0:ℝ)..(c n), f t| + |∫ t in (c n)..T, f t| := abs_add_le _ _
  have hεT : ε * c n ≤ ε * T := mul_le_mul_of_nonneg_left hcnT hε.le
  linarith

/-! ## The capstone: harmonized cells + Littlewood close the identification -/

/-- **Local residue control closes the S(t) identification.**  Given a harmonized cell
decomposition on which the native ledger's accumulated residue is sublinear at the
boundaries and its single-cell mass is sublinear, and given Littlewood's classical
bound in its native decomposition form (`S = Smult + defect` at good heights by the
registration law), the global coordinate identification holds at every good height —
and with it, via the compiled equivalences, every zero rides the carrier. -/
theorem globalCoordinateIdentification_of_harmonizedCells
    {c : ℕ → ℝ} (hmono : Monotone c) (hc0 : 0 ≤ c 0)
    (htop : Tendsto c atTop atTop)
    (hbd : (fun n => ∫ t in (0:ℝ)..(c n), Smult t) =o[atTop] fun n => c n)
    (hcell : (fun n => ∫ t in (c n)..(c (n + 1)), |Smult t|) =o[atTop] fun n => c n)
    (hLittlewood : (fun T => ∫ t in (0:ℝ)..T,
        (Smult t + (offLineStripZeroCountMult t : ℝ))) =o[atTop] fun T : ℝ => T) :
    ∀ (T : ℝ) (hT : GoodHeight T), classicalSContour hT = Smult T := by
  apply globalCoordinateIdentification_of_integral_sublinear
  have hSm : (fun T => ∫ t in (0:ℝ)..T, Smult t) =o[atTop] fun T : ℝ => T :=
    integral_sublinear_of_boundary_and_cell smult_intervalIntegrable
      hmono hc0 htop hbd hcell
  have hpt : (fun T => ∫ t in (0:ℝ)..T, (offLineStripZeroCountMult t : ℝ))
      = fun T => (∫ t in (0:ℝ)..T,
          (Smult t + (offLineStripZeroCountMult t : ℝ))) - ∫ t in (0:ℝ)..T, Smult t := by
    funext T
    rw [intervalIntegral.integral_add (smult_intervalIntegrable 0 T)
      (offLine_intervalIntegrable 0 T)]
    ring
  rw [hpt]
  exact hLittlewood.sub hSm

/-! ## The unconditional regime dichotomy: residues cannot hide sublinearly -/

/-- **The linear cost of one unabsorbed residue, unconditionally.**  A single
off-carrier event at height `T₀` forces the integrated registration defect to grow at
least linearly from that height on: `∫₀ᵀ defect ≥ T − T₀` for every `T ≥ T₀`.  There
is no sublinear way to hide a residue. -/
theorem integrated_defect_linear_of_ne_zero {T₀ : ℝ}
    (h : offLineStripZeroCountMult T₀ ≠ 0) {T : ℝ} (hT : T₀ ≤ T) :
    T - T₀ ≤ ∫ t in (0:ℝ)..T, (offLineStripZeroCountMult t : ℝ) := by
  have hpos : 0 < T₀ := by
    by_contra hle
    push_neg at hle
    exact h (offLineStripZeroCountMult_eq_zero_of_nonpos hle)
  have hsplit : ∫ t in (0:ℝ)..T, (offLineStripZeroCountMult t : ℝ)
      = (∫ t in (0:ℝ)..T₀, (offLineStripZeroCountMult t : ℝ))
        + ∫ t in T₀..T, (offLineStripZeroCountMult t : ℝ) :=
    (integral_add_adjacent_intervals (offLine_intervalIntegrable 0 T₀)
      (offLine_intervalIntegrable T₀ T)).symm
  have hhead : 0 ≤ ∫ t in (0:ℝ)..T₀, (offLineStripZeroCountMult t : ℝ) :=
    intervalIntegral.integral_nonneg hpos.le (fun t _ => Nat.cast_nonneg _)
  have htail : T - T₀ ≤ ∫ t in T₀..T, (offLineStripZeroCountMult t : ℝ) := by
    have hone : ∫ _t in T₀..T, (1:ℝ) = T - T₀ := by
      rw [intervalIntegral.integral_const, smul_eq_mul, mul_one]
    rw [← hone]
    refine intervalIntegral.integral_mono_on hT intervalIntegrable_const
      (offLine_intervalIntegrable T₀ T) (fun t ht => ?_)
    have h1 : 1 ≤ offLineStripZeroCountMult T₀ := Nat.one_le_iff_ne_zero.mpr h
    exact_mod_cast h1.trans (offLineStripZeroCountMult_mono ht.1)
  linarith

/-- **The unconditional regime dichotomy.**  Either the global coordinate
identification holds at every good height — the registration is faithful, every zero
rides the carrier — or the integrated defect grows at least linearly from some height
on.  The harmonized ledger admits no intermediate regime: sublinear defect is already
zero defect.  This is the unconditional content of "no residue on a harmonized
carrier". -/
theorem identification_or_linear_defect :
    (∀ (T : ℝ) (hT : GoodHeight T), classicalSContour hT = Smult T) ∨
      ∃ T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T →
        T - T₀ ≤ ∫ t in (0:ℝ)..T, (offLineStripZeroCountMult t : ℝ) := by
  by_cases h : ∀ T : ℝ, offLineStripZeroCountMult T = 0
  · left
    intro T hT
    rw [classicalSContour_eq_Smult_add_offLine hT, h T]
    simp
  · right
    push_neg at h
    obtain ⟨T₀, hT₀⟩ := h
    exact ⟨T₀, fun T hT => integrated_defect_linear_of_ne_zero hT₀ hT⟩

end CriticalLinePhasor.ContourArgument

#print axioms CriticalLinePhasor.ContourArgument.integrated_defect_linear_of_ne_zero
#print axioms CriticalLinePhasor.ContourArgument.identification_or_linear_defect
#print axioms CriticalLinePhasor.ContourArgument.zeroEventCountMult_mono
#print axioms CriticalLinePhasor.ContourArgument.smult_intervalIntegrable
#print axioms CriticalLinePhasor.ContourArgument.offLine_intervalIntegrable
#print axioms CriticalLinePhasor.ContourArgument.integral_sublinear_of_boundary_and_cell
#print axioms CriticalLinePhasor.ContourArgument.globalCoordinateIdentification_of_harmonizedCells
