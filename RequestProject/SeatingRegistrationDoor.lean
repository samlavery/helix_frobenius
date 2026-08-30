import RequestProject.SeatingMassRH

/-!
# The registration door: box-mass registration implies RiemannHypothesis

The HP identification slot, compiled as a door.  Per high box, define the
ANALYTIC box mass (sum of point-kernels over the strip census) and the
CENSUS box mass (same sum over the on-line census).  The registration
hypothesis is their equality as functions on the channel.  It forces the
exact Mathlib `RiemannHypothesis` by pole separation: a hypothetical
off-line zero `w` is a member of its box's strip census but not its line
census, so the registration difference contains `w`'s own kernel, which
diverges to `−∞` along the horizontal approach to `w` while the finitely
many remaining kernels stay continuous — contradicting the difference
vanishing identically.

No `sorry`, no `axiom`.
-/

open Complex ComplexConjugate Filter Topology

noncomputable section

namespace CriticalLinePhasor.SeatingLedger

/-- The point kernel of the mass ledger, in real coordinates. -/
def pointMass (ρ s : ℂ) : ℝ :=
  (s.re - ρ.re) / ((s.re - ρ.re)^2 + (s.im - ρ.im)^2) / (s.re - 1/2)

/-- The strip census of a box, as a finset. -/
def stripFinset (T₁ T₂ : ℝ) : Finset ℂ := (stripBox_finite T₁ T₂).toFinset

theorem onLineBox_finite (T₁ T₂ : ℝ) : (onLineBox T₁ T₂).Finite := by
  apply (stripBox_finite T₁ T₂).subset
  intro x hx
  exact hx.1

/-- The on-line census of a box, as a finset. -/
def lineFinset (T₁ T₂ : ℝ) : Finset ℂ := (onLineBox_finite T₁ T₂).toFinset

theorem mem_stripFinset {T₁ T₂ : ℝ} {ρ : ℂ} :
    ρ ∈ stripFinset T₁ T₂ ↔ ρ ∈ stripBox T₁ T₂ :=
  Set.Finite.mem_toFinset _

theorem mem_lineFinset {T₁ T₂ : ℝ} {ρ : ℂ} :
    ρ ∈ lineFinset T₁ T₂ ↔ ρ ∈ onLineBox T₁ T₂ :=
  Set.Finite.mem_toFinset _

theorem lineFinset_subset (T₁ T₂ : ℝ) :
    lineFinset T₁ T₂ ⊆ stripFinset T₁ T₂ := by
  intro x hx
  rw [mem_lineFinset] at hx
  rw [mem_stripFinset]
  exact hx.1

/-- **The registration door**: equality of the analytic and census box
masses, per high box, on the channel, forces Mathlib's
`RiemannHypothesis`. -/
theorem riemannHypothesis_of_box_mass_registration :
    ∃ A : ℝ, 0 < A ∧
      ((∀ T₁ T₂ : ℝ, 1269/2 ≤ T₁ → T₁ < T₂ →
          ∀ s : ℂ, 1269/2 < |s.im| →
            A / (Real.log |s.im|)^9 < s.re → s.re < 1/2 →
            ∑ ρ ∈ stripFinset T₁ T₂, pointMass ρ s
              = ∑ ρ ∈ lineFinset T₁ T₂, pointMass ρ s) →
        RiemannHypothesis) := by
  obtain ⟨A, hA0, _hAle, hdepth⟩ := offline_depth_bound
  refine ⟨A, hA0, fun hreg => RHBridge.no_offline_zeros_implies_rh ?_⟩
  intro ρ₀ hρ₀
  by_contra hre₀
  -- the ladder pushes any violator high
  have hlad₀ : 1269/2 < |ρ₀.im| := by
    by_contra hle
    push_neg at hle
    exact hre₀ (CriticalLinePhasor.DVP.online_below_1269o2 ρ₀ hρ₀ hle)
  -- reflect to positive height
  obtain ⟨ρ₁, hρ₁, hre₁, him₁⟩ :
      ∃ ρ₁, ρ₁ ∈ ZD.NontrivialZeros ∧ ρ₁.re ≠ 1/2 ∧ 1269/2 < ρ₁.im := by
    rcases lt_or_ge ρ₀.im 0 with hneg | hpos
    · refine ⟨conj ρ₀, conj_mem hρ₀, ?_, ?_⟩
      · rw [Complex.conj_re]; exact hre₀
      · rw [Complex.conj_im]
        rw [abs_of_neg hneg] at hlad₀
        linarith
    · refine ⟨ρ₀, hρ₀, hre₀, ?_⟩
      rw [abs_of_nonneg hpos] at hlad₀
      exact hlad₀
  -- reflect left of the line
  obtain ⟨w, hw, hwre, hwim⟩ :
      ∃ w, w ∈ ZD.NontrivialZeros ∧ w.re < 1/2 ∧ 1269/2 < w.im := by
    rcases lt_or_gt_of_ne hre₁ with h | h
    · exact ⟨ρ₁, hρ₁, h, him₁⟩
    · refine ⟨1 - conj ρ₁, mirror_mem hρ₁, ?_, ?_⟩
      · rw [mirror_re]; linarith
      · rw [mirror_im]; exact him₁
  -- the shell floor
  have hwabs : |w.im| = w.im := abs_of_pos (by linarith)
  have hd := hdepth w hw (by rw [hwabs]; linarith)
  have hβpos : A / (Real.log w.im)^9 < w.re := by
    rw [hwabs] at hd
    rw [abs_of_nonpos (by linarith)] at hd
    linarith
  -- the box around the violator
  set T₁ : ℝ := max (1269/2) (w.im - 1) with hT₁
  set T₂ : ℝ := w.im + 1 with hT₂
  have hT₁le : 1269/2 ≤ T₁ := le_max_left _ _
  have hT₁lt : T₁ < w.im := by
    rw [hT₁, max_lt_iff]
    constructor <;> linarith
  have hTlt : T₁ < T₂ := by
    rw [hT₂]; linarith
  have hwbox : w ∈ stripBox T₁ T₂ := ⟨hw, hT₁lt, by rw [hT₂]; linarith⟩
  have hwstrip : w ∈ stripFinset T₁ T₂ := mem_stripFinset.mpr hwbox
  have hwline : w ∉ lineFinset T₁ T₂ := by
    intro hmem
    exact absurd (mem_lineFinset.mp hmem).2 (by linarith)
  have hwoff : w ∈ stripFinset T₁ T₂ \ lineFinset T₁ T₂ :=
    Finset.mem_sdiff.mpr ⟨hwstrip, hwline⟩
  -- the horizontal approach path
  set p : ℝ → ℂ := fun h => (↑(w.re + h) : ℂ) + (w.im : ℂ) * I with hp
  have hpre : ∀ h, (p h).re = w.re + h := by
    intro h; simp [hp]
  have hpim : ∀ h, (p h).im = w.im := by
    intro h; simp [hp]
  -- registration vanishes along the path (eventually)
  have hDzero : ∀ᶠ h : ℝ in nhdsWithin 0 (Set.Ioi 0),
      ∑ ρ ∈ stripFinset T₁ T₂ \ lineFinset T₁ T₂, pointMass ρ (p h) = 0 := by
    have hev : ∀ᶠ h : ℝ in nhdsWithin 0 (Set.Ioi 0), h < 1/2 - w.re := by
      have hid : Tendsto (fun h : ℝ => h)
          (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) :=
        tendsto_id.mono_left nhdsWithin_le_nhds
      exact hid.eventually (eventually_lt_nhds (by linarith))
    filter_upwards [hev, self_mem_nhdsWithin] with h hh hh0
    have hh0' : (0:ℝ) < h := hh0
    have hchan := hreg T₁ T₂ hT₁le hTlt (p h)
      (by rw [hpim, abs_of_pos (by linarith)]; exact hwim)
      (by rw [hpre, hpim, abs_of_pos (by linarith)]; linarith)
      (by rw [hpre]; linarith)
    have hsplit := Finset.sum_sdiff (lineFinset_subset T₁ T₂)
      (f := fun ρ => pointMass ρ (p h))
    linarith [hsplit, hchan]
  -- split off the violator's kernel
  have hDsplit : ∀ h : ℝ,
      ∑ ρ ∈ stripFinset T₁ T₂ \ lineFinset T₁ T₂, pointMass ρ (p h)
        = pointMass w (p h)
          + ∑ ρ ∈ (stripFinset T₁ T₂ \ lineFinset T₁ T₂).erase w,
              pointMass ρ (p h) := by
    intro h
    exact (Finset.add_sum_erase _ _ hwoff).symm
  -- the violator's kernel diverges
  have hviol : Tendsto (fun h : ℝ => pointMass w (p h))
      (nhdsWithin 0 (Set.Ioi 0)) atBot := by
    have hval : ∀ᶠ h : ℝ in nhdsWithin 0 (Set.Ioi 0),
        pointMass w (p h) = h⁻¹ * (w.re + h - 1/2)⁻¹ := by
      filter_upwards [self_mem_nhdsWithin] with h hh0
      have hh0' : (0:ℝ) < h := hh0
      unfold pointMass
      rw [hpre, hpim]
      have e1 : w.re + h - w.re = h := by ring
      have e2 : w.im - w.im = 0 := by ring
      rw [e1, e2]
      have e3 : h^2 + (0:ℝ)^2 = h * h := by ring
      rw [e3]
      rw [div_div]
      rw [show h * h * (w.re + h - 1/2) = h * (h * (w.re + h - 1/2)) by ring]
      rw [div_mul_eq_div_div]
      rw [div_self hh0'.ne', one_div, mul_inv]
    have hbase : Tendsto (fun h : ℝ => h⁻¹ * (w.re + h - 1/2)⁻¹)
        (nhdsWithin 0 (Set.Ioi 0)) atBot := by
      have hf : Tendsto (fun h : ℝ => h⁻¹)
          (nhdsWithin 0 (Set.Ioi 0)) atTop := tendsto_inv_nhdsGT_zero
      have hg : Tendsto (fun h : ℝ => (w.re + h - 1/2)⁻¹)
          (nhdsWithin 0 (Set.Ioi 0)) (nhds (w.re - 1/2)⁻¹) := by
        apply Tendsto.mono_left _ nhdsWithin_le_nhds
        have hcont : ContinuousAt (fun h : ℝ => (w.re + h - 1/2)⁻¹) 0 := by
          apply ContinuousAt.inv₀
          · fun_prop
          · simpa using (by linarith : w.re + (0:ℝ) - 1/2 ≠ 0)
        simpa using hcont.tendsto
      exact hf.atTop_mul_neg (inv_lt_zero.mpr (by linarith)) hg
    have hval' : ∀ᶠ h : ℝ in nhdsWithin 0 (Set.Ioi 0),
        h⁻¹ * (w.re + h - 1/2)⁻¹ = pointMass w (p h) := by
      filter_upwards [hval] with h hh
      exact hh.symm
    exact hbase.congr' hval'
  -- the remaining kernels stay continuous
  set c : ℝ := ∑ ρ ∈ (stripFinset T₁ T₂ \ lineFinset T₁ T₂).erase w,
    pointMass ρ (p 0) with hc
  have hrestT : Tendsto
      (fun h : ℝ => ∑ ρ ∈ (stripFinset T₁ T₂ \ lineFinset T₁ T₂).erase w,
        pointMass ρ (p h))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds c) := by
    rw [hc]
    apply Tendsto.mono_left _ nhdsWithin_le_nhds
    apply tendsto_finset_sum
    intro ρ hmem
    have hρne : ρ ≠ w := Finset.ne_of_mem_erase hmem
    have hden1 : (w.re - ρ.re)^2 + (w.im - ρ.im)^2 ≠ 0 := by
      intro h0
      apply hρne
      have h1 : w.re - ρ.re = 0 := by
        nlinarith [sq_nonneg (w.re - ρ.re), sq_nonneg (w.im - ρ.im)]
      have h2 : w.im - ρ.im = 0 := by
        nlinarith [sq_nonneg (w.re - ρ.re), sq_nonneg (w.im - ρ.im)]
      apply Complex.ext <;> linarith
    have hform : (fun h : ℝ => pointMass ρ (p h))
        = fun h : ℝ => (w.re + h - ρ.re)
          / ((w.re + h - ρ.re)^2 + (w.im - ρ.im)^2) / (w.re + h - 1/2) := by
      funext h
      unfold pointMass
      rw [hpre, hpim]
    rw [hform, show pointMass ρ (p 0) = (w.re + 0 - ρ.re)
        / ((w.re + 0 - ρ.re)^2 + (w.im - ρ.im)^2) / (w.re + 0 - 1/2)
      from congrFun hform 0]
    have hcont : ContinuousAt (fun h : ℝ => (w.re + h - ρ.re)
        / ((w.re + h - ρ.re)^2 + (w.im - ρ.im)^2) / (w.re + h - 1/2)) 0 := by
      apply ContinuousAt.div
      · apply ContinuousAt.div
        · fun_prop
        · fun_prop
        · simpa using hden1
      · fun_prop
      · simpa using (by linarith : w.re + (0:ℝ) - 1/2 ≠ 0)
    simpa using hcont.tendsto
  -- the contradiction
  have hviolev : ∀ᶠ h : ℝ in nhdsWithin 0 (Set.Ioi 0),
      pointMass w (p h) < -(c + 1) :=
    hviol.eventually (eventually_lt_atBot _)
  have hrestev : ∀ᶠ h : ℝ in nhdsWithin 0 (Set.Ioi 0),
      (∑ ρ ∈ (stripFinset T₁ T₂ \ lineFinset T₁ T₂).erase w,
        pointMass ρ (p h)) < c + 1 :=
    hrestT.eventually (eventually_lt_nhds (lt_add_one c))
  obtain ⟨h, hzero, hlt1, hlt2⟩ := (hDzero.and (hviolev.and hrestev)).exists
  rw [hDsplit h] at hzero
  linarith

end CriticalLinePhasor.SeatingLedger

#print axioms CriticalLinePhasor.SeatingLedger.riemannHypothesis_of_box_mass_registration
