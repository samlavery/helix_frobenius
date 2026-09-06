import RequestProject.StationRegistrationIntertwining
import RequestProject.OnePerGap

/-!
# Positive-height registration with analytic multiplicity

Unfolded target: enumerate pairs (rho,j), where rho is a nontrivial zero of
positive height and 0 <= j < xiOrderNat rho. Disjoint station neighborhoods
give injectivity of height on these pairs. Reflection then fixes rho, and
the pairs (rho,0), (rho,1) exclude multiplicity greater than one.

This corrects the signed-height scope of StationRegistration without changing
that existing record. The arithmetic construction of this registration is
not provided here.

Expectation-free strategy A: `obtain ⟨n, rfl⟩ := R.surj a`, then use the two
shadow inequalities. Strategy B: use the multiplicity-weighted band census;
that independent route is compiled in OnePerGap and RegistrationResidualSupport.

Searches: `rg -n 'simplic|multiplic|occurrence|StationRegistration|slot'
RequestProject -g '*Registration*.lean' -g '*Gap*.lean' -g '*Shadow*.lean`;
`rg -n 'xiOrderNat.*conj|conj.*xiOrderNat' RequestProject --glob '*.lean'`;
Mathlib: `rg -n 'exists_fin|card_fin|Fin.*subsingleton|subsingleton.*Fin|le_one_iff_subsingleton'
.lake/packages/mathlib/Mathlib/Data/Fin .lake/packages/mathlib/Mathlib/Data/Fintype`.
-/

open Complex

namespace CriticalLinePhasor.XiChannel

/-- Each analytic multiplicity has a separate occurrence. -/
structure PositiveZeroOccurrence where
  zero : XiZeroIndex
  positive : 0 < zero.val.im
  slot : Fin (ZD.xiOrderNat zero.val)

/-- Register positive occurrences; recover the other side by conjugation. -/
structure PositiveStationRegistration (t : ℕ → ℝ) where
  mono : StrictMono t
  e : ℕ → PositiveZeroOccurrence
  surj : Function.Surjective e
  shadowR : ∀ n, |t n - (e n).zero.val.im| < (t (n + 1) - t n) / 2
  shadowL : ∀ n, 0 < n →
    |t n - (e n).zero.val.im| < (t n - t (n - 1)) / 2

variable {t : ℕ → ℝ}

theorem PositiveStationRegistration.no_shared_ordinate (R : PositiveStationRegistration t)
    {n m : ℕ} (hnm : n < m)
    (h : (R.e n).zero.val.im = (R.e m).zero.val.im) : False := by
  have hR := R.shadowR n
  have hL := R.shadowL m (by omega)
  rw [← h] at hL
  set γ := (R.e n).zero.val.im
  have h1 : t (n + 1) ≤ t m := R.mono.monotone (by omega)
  have h2 : t n ≤ t (m - 1) := R.mono.monotone (by omega)
  have h3 : t m - t n ≤ |t n - γ| + |t m - γ| := by
    calc
      t m - t n = |t m - t n| :=
        (abs_of_nonneg (by linarith [R.mono.monotone hnm.le])).symm
      _ = |(t m - γ) - (t n - γ)| := by ring_nf
      _ ≤ |t m - γ| + |t n - γ| := abs_sub _ _
      _ = |t n - γ| + |t m - γ| := add_comm _ _
  linarith

theorem PositiveStationRegistration.ordinate_injective (R : PositiveStationRegistration t) :
    Function.Injective (fun q : PositiveZeroOccurrence => q.zero.val.im) := by
  intro a b hab
  obtain ⟨n, rfl⟩ := R.surj a
  obtain ⟨m, rfl⟩ := R.surj b
  have hnm : n = m := by
    rcases lt_trichotomy n m with h | h | h
    · exact (R.no_shared_ordinate h hab).elim
    · exact h
    · exact (R.no_shared_ordinate h hab.symm).elim
  rw [hnm]

/-- Geometric height separation transfers to analytic order via occurrence coverage. -/
theorem PositiveStationRegistration.online_simple (R : PositiveStationRegistration t)
    (ρ : XiZeroIndex) (hpos : 0 < ρ.val.im) :
    ρ.val.re = 1 / 2 ∧ ZD.xiOrderNat ρ.val = 1 := by
  have hm := ZD.xiOrderNat_pos_of_mem_NontrivialZeros ρ.property
  let q : PositiveZeroOccurrence := ⟨ρ, hpos, ⟨0, hm⟩⟩
  let qr : PositiveZeroOccurrence := ⟨xiZeroReflection ρ,
    by simpa only [xiZeroReflection_im] using hpos,
    ⟨0, ZD.xiOrderNat_pos_of_mem_NontrivialZeros (xiZeroReflection ρ).property⟩⟩
  have hfix : q = qr := R.ordinate_injective (by simp [q, qr, xiZeroReflection_im])
  constructor
  · have hre := congrArg (fun a : PositiveZeroOccurrence => a.zero.val.re) hfix
    simp only [q, qr, xiZeroReflection_re] at hre
    linarith
  · by_contra hne
    have htwo : 1 < ZD.xiOrderNat ρ.val := by omega
    let q1 : PositiveZeroOccurrence := ⟨ρ, hpos, ⟨1, htwo⟩⟩
    have heq : q = q1 := R.ordinate_injective rfl
    have hslot := congrArg (fun a : PositiveZeroOccurrence => a.slot.val) heq
    norm_num [q, q1] at hslot

/-- Conjugation transports both the real part and the analytic order. -/
theorem PositiveStationRegistration.all_online_simple (R : PositiveStationRegistration t)
    (ρ : XiZeroIndex) : ρ.val.re = 1 / 2 ∧ ZD.xiOrderNat ρ.val = 1 := by
  rcases lt_trichotomy 0 ρ.val.im with hp | hz | hn
  · exact R.online_simple ρ hp
  · exact (DVP.NontrivialZeros_im_ne_zero ρ.property hz.symm).elim
  · have hc := ContourArgument.conj_mem_nontrivialZeros ρ.property
    have hcp : 0 < ((starRingEnd ℂ) ρ.val).im := by simp; linarith
    have h := R.online_simple ⟨(starRingEnd ℂ) ρ.val, hc⟩ hcp
    simpa only [Complex.conj_re, FoliatedGlobalPolarization.xiOrderNat_conj] using h

theorem PositiveStationRegistration.semiconj (R : PositiveStationRegistration t) :
    Function.Semiconj zeroHeightCorrespondence xiZeroLedgerOperator
      (ThreeDFocal.carrierThreeDOperator 1 1) :=
  semiconj_of_online (fun ρ => (R.all_online_simple ρ).1)

end CriticalLinePhasor.XiChannel

#print axioms CriticalLinePhasor.XiChannel.PositiveStationRegistration.ordinate_injective
#print axioms CriticalLinePhasor.XiChannel.PositiveStationRegistration.online_simple
#print axioms CriticalLinePhasor.XiChannel.PositiveStationRegistration.all_online_simple
#print axioms CriticalLinePhasor.XiChannel.PositiveStationRegistration.semiconj
