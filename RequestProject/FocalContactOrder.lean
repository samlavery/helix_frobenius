import RequestProject.FrobeniusFlowPencil
import Mathlib.LinearAlgebra.Vandermonde

/-!
# The order of focal contact and its direction (ledger 1177)

Along the per-site Frobenius flow (ledger 1175–1176) the resultant of a configuration is
`B(t) = (frob t c).resultant`. Its jets at `t = 0` are the log-moments of the configuration:

* `iteratedDeriv_flowRes_zero`: `B^(j)(0) = (−i)^j · Σ_k log(k+1)^j · c_k` (`moment c j`).
* `exists_moment_ne_zero`: a nonzero configuration has a nonzero log-moment of order `< N`
  (`N` sites): the frequencies `log(k+1)` are distinct (`node_injective`), so the Vandermonde
  matrix is invertible.
* `IsContactOrder c m`: `B^(m)(0) ≠ 0` and all lower jets vanish. `isContactOrder_unique`.
* `exists_isContactOrder`: a cancelling configuration of positive mass has a contact order
  `1 ≤ m < N`. `contactJet_ne_zero`: its contact jet `B^(m)(0)` is nonzero, so its direction
  `arg B^(m)(0)` is defined.
* J: `moment_J` (the moments are conjugated), `isContactOrder_J` (same order),
  `contactJet_J` (`B_J^(m)(0) = (−1)^m · conj B^(m)(0)`).
* The event: `event_finite_contact` (every focal event has a finite contact order `1 ≤ m < N` with
  nonzero contact jet, and all lower derivatives of the flow vanish there);
  `contactJet_one_eq_crossingVelocity` (order 1 recovers ledger 1176's crossing velocity).

Not claimed: that the order is 1 (a simple crossing).
-/

open Complex Matrix

noncomputable section

namespace CriticalLinePhasor.FocalContact

open CriticalLinePhasor CriticalLinePhasor.FocalEventProjection CriticalLinePhasor.CancellationEigenstatePair
open CriticalLinePhasor.FocalFeet CriticalLinePhasor.FocalFeet.PhasorConfig CriticalLinePhasor.FocalQuotient
open CriticalLinePhasor.UnconditionalFrobenius CriticalLinePhasor.FrobeniusFlow

/-! ## Log-moments and the jets of the flow -/

/-- The Frobenius frequency of site `k + 1`: `log (k + 1)`. -/
def node (c : PhasorConfig) (k : Fin c.size) : ℂ := (Real.log (((k : ℕ) : ℝ) + 1) : ℂ)

/-- The `j`-th log-moment of the configuration. -/
def moment (c : PhasorConfig) (j : ℕ) : ℂ := ∑ k, node c k ^ j * c.phasor k

theorem moment_zero (c : PhasorConfig) : moment c 0 = c.resultant := by
  simp [moment, PhasorConfig.resultant]

/-- The flow resultant of a configuration. -/
def flowRes (c : PhasorConfig) (t : ℝ) : ℂ := (frob t c).resultant

theorem flowB_eq_flowRes (e : FocalEvent) : flowB e = flowRes (eventConfig e) := rfl

/-- The `j`-th derivative of the flow resultant, as a function of `t`. -/
def jetFun (c : PhasorConfig) (j : ℕ) (t : ℝ) : ℂ :=
  ∑ k, (-I * node c k) ^ j * c.phasor k * spectralWave (-Real.log (((k : ℕ) : ℝ) + 1)) t

theorem jetFun_zero (c : PhasorConfig) : jetFun c 0 = flowRes c := by
  funext t
  simp only [jetFun, pow_zero, one_mul, flowRes, frob_resultant]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [mellinSpin_eq_wave, Nat.cast_add, Nat.cast_one, mul_comm]

theorem hasDerivAt_jetFun (c : PhasorConfig) (j : ℕ) (t : ℝ) :
    HasDerivAt (jetFun c j) (jetFun c (j + 1) t) t := by
  unfold jetFun
  have hk : ∀ k ∈ (Finset.univ : Finset (Fin c.size)),
      HasDerivAt (fun t => (-I * node c k) ^ j * c.phasor k *
          spectralWave (-Real.log (((k : ℕ) : ℝ) + 1)) t)
        ((-I * node c k) ^ j * c.phasor k *
          (((-Real.log (((k : ℕ) : ℝ) + 1) : ℝ) : ℂ) * I *
            spectralWave (-Real.log (((k : ℕ) : ℝ) + 1)) t)) t :=
    fun k _ => (spectralWave_hasDerivAt _ t).const_mul _
  convert HasDerivAt.fun_sum hk using 1
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [node]
  push_cast
  ring

theorem iteratedDeriv_flowRes (c : PhasorConfig) (j : ℕ) : iteratedDeriv j (flowRes c) = jetFun c j := by
  induction j with
  | zero => rw [iteratedDeriv_zero, jetFun_zero]
  | succ j ih =>
    rw [iteratedDeriv_succ, ih]
    funext t
    exact (hasDerivAt_jetFun c j t).deriv

/-- **The jets of the flow at the event are the log-moments.** -/
theorem iteratedDeriv_flowRes_zero (c : PhasorConfig) (j : ℕ) :
    iteratedDeriv j (flowRes c) 0 = (-I) ^ j * moment c j := by
  rw [iteratedDeriv_flowRes, jetFun, moment, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [spectralWave, Complex.ofReal_zero, mul_zero, zero_mul, Complex.exp_zero, mul_one]
  rw [mul_pow]
  ring

/-! ## A nonzero configuration has a nonzero log-moment of order `< N` -/

theorem node_injective (c : PhasorConfig) : Function.Injective (node c) := by
  intro a b h
  simp only [node, Complex.ofReal_inj] at h
  have ha : (0 : ℝ) < ((a : ℕ) : ℝ) + 1 := by positivity
  have hb : (0 : ℝ) < ((b : ℕ) : ℝ) + 1 := by positivity
  have h2 := Real.log_injOn_pos (Set.mem_Ioi.mpr ha) (Set.mem_Ioi.mpr hb) h
  have h3 : ((a : ℕ) : ℝ) = ((b : ℕ) : ℝ) := by linarith
  exact Fin.ext (by exact_mod_cast h3)

theorem moment_eq_vecMul (c : PhasorConfig) (j : Fin c.size) :
    moment c j = (c.phasor ᵥ* vandermonde (node c)) j := by
  simp only [moment, Matrix.vecMul, dotProduct, Matrix.vandermonde_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

/-- **A nonzero configuration has a nonzero log-moment of order `< N`.** -/
theorem exists_moment_ne_zero (c : PhasorConfig) (hc : c.phasor ≠ 0) :
    ∃ j < c.size, moment c j ≠ 0 := by
  by_contra h
  simp only [not_exists, not_and, not_not] at h
  apply hc
  refine Matrix.eq_zero_of_vecMul_eq_zero
    (det_vandermonde_ne_zero_iff.mpr (node_injective c)) ?_
  funext j
  rw [← moment_eq_vecMul]
  exact h j j.2

theorem phasor_ne_zero_of_mass_pos {c : PhasorConfig} (hm : 0 < c.mass) : c.phasor ≠ 0 := by
  intro h
  simp [PhasorConfig.mass, h] at hm

/-! ## The order of contact -/

/-- `m` is the order of contact: the `m`-th jet is nonzero and all lower jets vanish. -/
def IsContactOrder (c : PhasorConfig) (m : ℕ) : Prop :=
  moment c m ≠ 0 ∧ ∀ i < m, moment c i = 0

theorem isContactOrder_unique {c : PhasorConfig} {m m' : ℕ} (h : IsContactOrder c m)
    (h' : IsContactOrder c m') : m = m' := by
  rcases lt_trichotomy m m' with hlt | heq | hgt
  · exact absurd (h'.2 m hlt) h.1
  · exact heq
  · exact absurd (h.2 m' hgt) h'.1

/-- **A cancelling configuration of positive mass has a contact order `1 ≤ m < N`.** -/
theorem exists_isContactOrder {c : PhasorConfig} (hc : c.Cancels) (hm : 0 < c.mass) :
    ∃ m, 1 ≤ m ∧ m < c.size ∧ IsContactOrder c m := by
  classical
  obtain ⟨j, hj, hjne⟩ := exists_moment_ne_zero c (phasor_ne_zero_of_mass_pos hm)
  have hex : ∃ i, moment c i ≠ 0 := ⟨j, hjne⟩
  refine ⟨Nat.find hex, ?_, lt_of_le_of_lt (Nat.find_min' hex hjne) hj,
    Nat.find_spec hex, fun i hi => ?_⟩
  · by_contra h0
    have h00 : Nat.find hex = 0 := by omega
    have := Nat.find_spec hex
    rw [h00, moment_zero] at this
    exact this hc
  · by_contra hne
    exact Nat.find_min hex hi hne

/-- The contact jet `B^(m)(0) = (−i)^m · moment c m`. -/
def contactJet (c : PhasorConfig) (m : ℕ) : ℂ := (-I) ^ m * moment c m

theorem contactJet_eq_iteratedDeriv (c : PhasorConfig) (m : ℕ) :
    iteratedDeriv m (flowRes c) 0 = contactJet c m :=
  iteratedDeriv_flowRes_zero c m

theorem contactJet_ne_zero {c : PhasorConfig} {m : ℕ} (h : IsContactOrder c m) :
    contactJet c m ≠ 0 :=
  mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr Complex.I_ne_zero)) h.1

/-- The direction of the contact: `arg B^(m)(0)`. -/
def contactDirection (c : PhasorConfig) (m : ℕ) : Real.Angle := (Complex.arg (contactJet c m) : Real.Angle)

/-! ## The anti-helix -/

theorem moment_J (c : PhasorConfig) (j : ℕ) :
    moment (PhasorConfig.J c) j = (starRingEnd ℂ) (moment c j) := by
  show ∑ k : Fin c.size, node c k ^ j * (starRingEnd ℂ) (c.phasor k) = _
  rw [moment, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_mul, map_pow, node, Complex.conj_ofReal]

/-- **The anti-helix has the same contact order.** -/
theorem isContactOrder_J (c : PhasorConfig) (m : ℕ) :
    IsContactOrder (PhasorConfig.J c) m ↔ IsContactOrder c m := by
  simp only [IsContactOrder, moment_J, ne_eq, map_eq_zero]

/-- **The anti-helix contact jet is `(−1)^m · conj` of the helix contact jet.** -/
theorem contactJet_J (c : PhasorConfig) (m : ℕ) :
    contactJet (PhasorConfig.J c) m = (-1) ^ m * (starRingEnd ℂ) (contactJet c m) := by
  rw [contactJet, contactJet, moment_J, map_mul, map_pow, map_neg, Complex.conj_I, neg_neg,
    neg_eq_neg_one_mul I, mul_pow]
  ring

/-! ## The event -/

/-- **Every focal event has a finite order of contact.** There is `m` with `1 ≤ m < N` such that the
`m`-th derivative of the Frobenius flow resultant at the event is nonzero and all lower derivatives
vanish. -/
theorem event_finite_contact (e : FocalEvent) :
    ∃ m, 1 ≤ m ∧ m < ⌈CarrierHeadFiniteFiber.physicalHead e.y⌉₊ ∧
      iteratedDeriv m (flowB e) 0 ≠ 0 ∧ ∀ i < m, iteratedDeriv i (flowB e) 0 = 0 := by
  have hm : 0 < (eventConfig e).mass := by rw [mass_eventConfig]; exact eigenMass_pos e
  obtain ⟨m, h1, hlt, hc⟩ := exists_isContactOrder (eventConfig_cancels e) hm
  refine ⟨m, h1, hlt, ?_, fun i hi => ?_⟩
  · rw [flowB_eq_flowRes, contactJet_eq_iteratedDeriv]
    exact contactJet_ne_zero hc
  · rw [flowB_eq_flowRes, iteratedDeriv_flowRes_zero, hc.2 i hi, mul_zero]

/-- Order 1 recovers ledger 1176's crossing velocity. -/
theorem contactJet_one_eq_crossingVelocity (e : FocalEvent) :
    contactJet (eventConfig e) 1 = crossingVelocity e := by
  rw [← contactJet_eq_iteratedDeriv, ← flowB_eq_flowRes, iteratedDeriv_one]
  exact (flowB_hasDerivAt_zero e).deriv

end CriticalLinePhasor.FocalContact

#print axioms CriticalLinePhasor.FocalContact.iteratedDeriv_flowRes_zero
#print axioms CriticalLinePhasor.FocalContact.node_injective
#print axioms CriticalLinePhasor.FocalContact.exists_moment_ne_zero
#print axioms CriticalLinePhasor.FocalContact.isContactOrder_unique
#print axioms CriticalLinePhasor.FocalContact.exists_isContactOrder
#print axioms CriticalLinePhasor.FocalContact.contactJet_ne_zero
#print axioms CriticalLinePhasor.FocalContact.moment_J
#print axioms CriticalLinePhasor.FocalContact.isContactOrder_J
#print axioms CriticalLinePhasor.FocalContact.contactJet_J
#print axioms CriticalLinePhasor.FocalContact.event_finite_contact
#print axioms CriticalLinePhasor.FocalContact.contactJet_one_eq_crossingVelocity
