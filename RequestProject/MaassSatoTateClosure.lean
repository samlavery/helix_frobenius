import RequestProject.PolyCeiling

/-!
# Sato–Tate for Maass forms: the closure, and its exactness

The corollary is assembled into one compiled implication, and the assembly is
proved terminal: each of its two typed inputs is *equivalent* to the conclusion
it feeds, so the interface has zero slack — reducing it further is literally
proving the theorem's own conclusion.

* `maass_satoTate` — **the corollary as one theorem**: a Maass seed with the
  per-rung polynomial ceiling and the per-rank prime cancellation satisfies
  both halves of Sato–Tate — temperedness (`‖α_p‖ = 1` at every prime) and
  carrier equidistribution of the Satake angles;
* `temperedness_iff_polyCeiling` / `temperedness_iff_ceiling` — **input one is
  exact**: the ceiling (polynomial or uniform) exists *iff* the seed is
  tempered — sufficiency is the compiled radial limit, necessity is the `C = 1`
  manufacture;
* `cancellation_iff_equidistribution` — **input two is exact**: the per-rank
  cancellation is equivalent to the equidistribution conclusion (the compiled
  biconditional, instantiated);
* `maass_satoTate_exact` — **the closure statement**: the reduction is lossless
  in both components simultaneously.

Register, terminal.  This is the full stop the mathematics permits: the
corollary is one machine-checked implication whose hypotheses are individually
equivalent to its conclusions.  The two inputs remain classically open for
Maass forms — the per-rung ceiling is Jacquet–Shalika-strength through the
symmetric-power ladder, and the per-rank cancellation requires the one-line
theory of `L(Sym^r)` for every `r`, where even meromorphic continuation is
classically unavailable beyond `r = 4` (Kim–Shahidi; the
holomorphic-form techniques of Newton–Thorne do not reach Maass forms).  The
Tauberian half of the cancellation (Wiener–Ikehara) exists machine-checked in
Lean elsewhere (the PrimeNumberTheoremAnd project), so when the per-rank
one-line theory lands, the analytic conversion is formalizable; until then the
cancellation field is the open frontier itself, not a formalization backlog.
No `axiom`, no `sorry`.
-/

open Filter Topology

namespace CriticalLinePhasor.MaassSatoTateClosure

open CriticalLinePhasor.GeneralSeed CriticalLinePhasor.MaassSatoTate
open CriticalLinePhasor.SatoTateCarrier3D CriticalLinePhasor.PolyCeiling

/-! ## The corollary as one theorem -/

/-- **Sato–Tate for the typed Maass seed, assembled**: the per-rung polynomial
ceiling and the per-rank prime cancellation yield both halves — temperedness at
every prime, and carrier equidistribution of the Satake angles. -/
theorem maass_satoTate (M : MaassEigenData) (hP : MaassPolyCeiling M)
    (hcanc : ∀ r : ℕ, 1 ≤ r →
      Tendsto (fun n =>
        arithmeticSymmetricPowerPrimeAverage
          (maassSatoTateFamily M hP.toCeiling) r n) atTop (nhds 0)) :
    (∀ p : Nat.Primes, ‖(SatakeSeed.ofMaass M).satake p‖ = 1) ∧
    Tendsto
      (empiricalPrimeCarrierMeasure (maassSatoTateFamily M hP.toCeiling).angle)
      atTop (nhds carrierProbability) :=
  ⟨fun p => maass_temperedness_poly M hP p,
    maass_satoTate_of_cancellation M hP.toCeiling hcanc⟩

/-! ## Exactness of input one: the ceiling is temperedness -/

/-- **Input one is exact (uniform form)**: a uniform tower ceiling exists iff
the seed is tempered. -/
theorem temperedness_iff_ceiling (M : MaassEigenData) :
    (∀ p : Nat.Primes, ‖(SatakeSeed.ofMaass M).satake p‖ = 1) ↔
      Nonempty (MaassTowerCeiling M) := by
  constructor
  · intro h
    exact ⟨{ C := fun _ => 1
             top := fun p r _ => by rw [norm_pow, h p, one_pow]
             bottom := fun p r _ => by
               rw [norm_pow, norm_inv, h p, inv_one, one_pow] }⟩
  · rintro ⟨hC⟩
    exact fun p => maass_temperedness M hC p

/-- **Input one is exact (polynomial form)**: the honest per-rung ceiling exists
iff the seed is tempered. -/
theorem temperedness_iff_polyCeiling (M : MaassEigenData) :
    (∀ p : Nat.Primes, ‖(SatakeSeed.ofMaass M).satake p‖ = 1) ↔
      Nonempty (MaassPolyCeiling M) := by
  constructor
  · intro h
    exact ⟨{ C := fun _ => 1
             C_pos := fun _ => one_pos
             k := 0
             top := fun p r _ => by
               rw [norm_pow, h p, one_pow]
               simp
             bottom := fun p r _ => by
               rw [norm_pow, norm_inv, h p, inv_one, one_pow]
               simp }⟩
  · rintro ⟨hP⟩
    exact fun p => maass_temperedness_poly M hP p

/-! ## Exactness of input two: the cancellation is the equidistribution -/

/-- **Input two is exact**: the per-rank cancellation is equivalent to the
equidistribution conclusion — the compiled biconditional, instantiated. -/
theorem cancellation_iff_equidistribution (M : MaassEigenData)
    (hC : MaassTowerCeiling M) :
    (∀ r : ℕ, 1 ≤ r →
      Tendsto (fun n =>
        arithmeticSymmetricPowerPrimeAverage (maassSatoTateFamily M hC) r n)
        atTop (nhds 0)) ↔
    Tendsto (empiricalPrimeCarrierMeasure (maassSatoTateFamily M hC).angle)
      atTop (nhds carrierProbability) :=
  maass_satoTate_iff M hC

/-! ## The closure: zero slack in both components -/

/-- **THE CLOSURE** — the reduction is lossless in both components: the ceiling
is equivalent to temperedness, and (given the family) the cancellation is
equivalent to equidistribution.  Every hypothesis of `maass_satoTate` is
individually equivalent to the conclusion it feeds; reducing the interface
further is proving the theorem's own conclusion. -/
theorem maass_satoTate_exact (M : MaassEigenData) :
    ((∀ p : Nat.Primes, ‖(SatakeSeed.ofMaass M).satake p‖ = 1) ↔
      Nonempty (MaassPolyCeiling M)) ∧
    (∀ hC : MaassTowerCeiling M,
      ((∀ r : ℕ, 1 ≤ r →
        Tendsto (fun n =>
          arithmeticSymmetricPowerPrimeAverage (maassSatoTateFamily M hC) r n)
          atTop (nhds 0)) ↔
      Tendsto (empiricalPrimeCarrierMeasure (maassSatoTateFamily M hC).angle)
        atTop (nhds carrierProbability))) :=
  ⟨temperedness_iff_polyCeiling M, fun hC => cancellation_iff_equidistribution M hC⟩

end CriticalLinePhasor.MaassSatoTateClosure

#print axioms CriticalLinePhasor.MaassSatoTateClosure.maass_satoTate
#print axioms CriticalLinePhasor.MaassSatoTateClosure.temperedness_iff_ceiling
#print axioms CriticalLinePhasor.MaassSatoTateClosure.temperedness_iff_polyCeiling
#print axioms CriticalLinePhasor.MaassSatoTateClosure.cancellation_iff_equidistribution
#print axioms CriticalLinePhasor.MaassSatoTateClosure.maass_satoTate_exact
