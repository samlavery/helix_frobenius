import RequestProject.HelixHeightIntertwining

/-!
# Full intertwining from a station registration (ledger 599)

The zero-built correspondence (`HelixHeightCorrespondence.lean`) intertwines the ledger operator
with the carrier operator iff every zero is on the line (597). This file states the hypothesis that
DOES carry the fiber: a **station registration** — a strictly increasing station sequence `t` (the
registration operator's spectrum, HP_PROGRAM §1: `ϑ(t_n)/π + 3/2 + Ŝ(t_n) = n`, built from the
primes) together with an enumeration `e` of the zeros, surjective, each zero shadowed by its
station within half the local gap on both sides. Then

* two distinct indices never register the same ordinate (`no_shared_ordinate`), so an off-line
  zero and its mirror (same ordinate, different zeros) cannot both be registered — every zero is on
  the line (`online_of_stationRegistration`);
* and the enumeration is injective (`injective_of_stationRegistration`).

This is the global form of `shadowing_implies_online_simple` (RegistrationShadowing.lean), chained
to the intertwining register. The hypothesis is the residual tail law of the registry
(`|γ_n − t_n| <` half a gap at every station), measured at RMS 0.039 spacings over 41k zeros; its
exact residual is the compiled truncated-formula comb (563–568). Proving the hypothesis from the
primes is the construction this register asks for.
-/

open Complex

namespace CriticalLinePhasor.XiChannel

open ThreeDFocal

/-- A station registration of the zeros: stations strictly increasing, an enumeration of the zero
set, and each zero within half the local gap of its own station on both sides. -/
structure StationRegistration (t : ℕ → ℝ) where
  mono : StrictMono t
  e : ℕ → XiZeroIndex
  surj : Function.Surjective e
  shadowR : ∀ n, |t n - (e n).val.im| < (t (n + 1) - t n) / 2
  shadowL : ∀ n, 0 < n → |t n - (e n).val.im| < (t n - t (n - 1)) / 2

variable {t : ℕ → ℝ}

/-- Two distinct stations cannot register the same ordinate. -/
theorem StationRegistration.no_shared_ordinate (R : StationRegistration t) {n m : ℕ}
    (hnm : n < m) (h : (R.e n).val.im = (R.e m).val.im) : False := by
  have hR := R.shadowR n
  have hL := R.shadowL m (by omega)
  rw [← h] at hL
  set γ := (R.e n).val.im
  have h1 : t (n + 1) ≤ t m := R.mono.monotone (by omega)
  have h2 : t n ≤ t (m - 1) := R.mono.monotone (by omega)
  have h3 : t m - t n ≤ |t n - γ| + |t m - γ| := by
    calc t m - t n = |t m - t n| := (abs_of_nonneg (by linarith [R.mono.monotone hnm.le])).symm
      _ = |(t m - γ) - (t n - γ)| := by ring_nf
      _ ≤ |t m - γ| + |t n - γ| := abs_sub _ _
      _ = |t n - γ| + |t m - γ| := add_comm _ _
  linarith

/-- The enumeration is injective: no zero is registered twice. -/
theorem StationRegistration.injective (R : StationRegistration t) : Function.Injective R.e := by
  intro n m h
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact R.no_shared_ordinate hlt (by rw [h])
  · exact R.no_shared_ordinate hgt (by rw [h])

/-- The mirror of a zero has the same ordinate and, off the line, is a different zero. -/
theorem xiZeroReflection_im (ρ : XiZeroIndex) : (xiZeroReflection ρ).val.im = ρ.val.im := by
  simp [xiZeroReflection]

theorem xiZeroReflection_re (ρ : XiZeroIndex) : (xiZeroReflection ρ).val.re = 1 - ρ.val.re := by
  simp [xiZeroReflection]

/-- **Every registered zero is on the line.** -/
theorem online_of_stationRegistration (R : StationRegistration t) (ρ : XiZeroIndex) :
    ρ.val.re = 1 / 2 := by
  by_contra hre
  obtain ⟨n, hn⟩ := R.surj ρ
  obtain ⟨m, hm⟩ := R.surj (xiZeroReflection ρ)
  have hne : n ≠ m := by
    intro hnm
    subst hnm
    have hfix : ρ = xiZeroReflection ρ := hn.symm.trans hm
    have := congrArg (fun z : XiZeroIndex => z.val.re) hfix
    simp only [xiZeroReflection_re] at this
    exact hre (by linarith)
  have him : (R.e n).val.im = (R.e m).val.im := by
    rw [hn, hm, xiZeroReflection_im]
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact R.no_shared_ordinate hlt him
  · exact R.no_shared_ordinate hgt him.symm

/-- The same, as the Mathlib-facing statement on the zero set. -/
theorem nontrivialZeros_online_of_stationRegistration (R : StationRegistration t) :
    ∀ ρ ∈ ZD.NontrivialZeros, ρ.re = 1 / 2 :=
  fun ρ hρ => online_of_stationRegistration R ⟨ρ, hρ⟩

end CriticalLinePhasor.XiChannel

#print axioms CriticalLinePhasor.XiChannel.online_of_stationRegistration
#print axioms CriticalLinePhasor.XiChannel.nontrivialZeros_online_of_stationRegistration
