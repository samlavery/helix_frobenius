import RequestProject.MaassSatoTate
import RequestProject.StrandLatticeFreeze

/-!
# The Hodge fork at the seed: freeze or drift

The Langlands–Hodge junction (`StrandLatticeFreeze`) proved temperedness is a
freeze law: a lattice strand under the tower ceiling is a sixth root of unity.
This file lands the junction at the campaign's typed seed — the same object, the
same ceiling field, that carries the packages, the converse, the wave-form
identification, and the Sato–Tate family:

* `LatticeCertificate` — the Hodge-type (rational) certificate at a prime: the
  seed's Satake datum is a nonzero `ℤ[ζ₆]`-integer;
* `seed_freeze` — **the freeze half**: under the tower ceiling the certified
  strand has sixth power one — the rational datum cannot drift;
* `sixth_root_angle_mem` / `seed_freeze_angle` — **the μ₆-cell pinning**: the
  frozen Satake angle lies in `{0, π/3, 2π/3, π}` — the boundary set of the
  house π/3-cell structure.  The Sato–Tate family's angle at a certified prime is
  pinned to four values;
* the fork register — the drift half is the compiled Sato–Tate chain
  (`maass_satoTate_iff`): the cancellation input equidistributes the angles
  against the absolutely continuous carrier measure.  A seed frozen at every
  prime is pinned to a four-point angle set, the shape incompatible with that
  limit; the compiled completion of the incompatibility (the nondegeneracy of the
  four-point Chebyshev moment matrix, closing "fully frozen ⟹ cancellation
  fails") is the named next brick.

In the harmonic Hodge frame: the certificate is the rational constant-mode datum,
the freeze is its rigidity, and the drift alternative is equidistribution — the
fork is Sato–Tate's own non-Galois-type hypothesis, typed at the seed.  No
`axiom`, no `sorry`.
-/

open Complex

namespace CriticalLinePhasor.HodgeSeedFork

open CriticalLinePhasor.GeneralSeed CriticalLinePhasor.MaassSatoTate
open CriticalLinePhasor.StrandLatticeFreeze CriticalLinePhasor.SatoTateCarrier3D
open ZetaSixClosure

/-- **The Hodge-type certificate at a prime**: the seed's Satake datum is a nonzero
`ℤ[ζ₆]`-integer — the rational constant-mode datum of the harmonic Hodge frame. -/
structure LatticeCertificate (M : MaassEigenData) (p : Nat.Primes) where
  x : Zz6
  x_ne : x ≠ ⟨0, 0⟩
  satake_eq : (SatakeSeed.ofMaass M).satake p = latticeToC x

/-- **The freeze half of the fork**: under the tower ceiling, a certified strand
has sixth power one — the rational datum cannot drift. -/
theorem seed_freeze (M : MaassEigenData) (hC : MaassTowerCeiling M) (p : Nat.Primes)
    (cert : LatticeCertificate M p) :
    (SatakeSeed.ofMaass M).satake p ^ 6 = 1 := by
  rw [cert.satake_eq]
  refine strand_pow6_one_of_tower_ceiling cert.x_ne (C := hC.C p) ?_ ?_
  · intro r hr
    have := hC.top p r hr
    rwa [cert.satake_eq] at this
  · intro r hr
    have := hC.bottom p r hr
    rwa [cert.satake_eq] at this

/-- **The μ₆-cell pinning**: a unit-modulus sixth root of unity has its absolute
argument in `{0, π/3, 2π/3, π}` — the boundary set of the house π/3 cells. -/
theorem sixth_root_angle_mem {α : ℂ} (hα : ‖α‖ = 1) (h6 : α ^ 6 = 1) :
    |Complex.arg α| ∈ ({0, Real.pi / 3, 2 * Real.pi / 3, Real.pi} : Set ℝ) := by
  have hαe : α = Complex.exp ((Complex.arg α : ℂ) * Complex.I) := by
    conv_lhs => rw [← Complex.norm_mul_exp_arg_mul_I α]
    rw [hα]
    simp
  have h6' : Complex.exp ((6 : ℂ) * ((Complex.arg α : ℂ) * Complex.I)) = 1 := by
    have h1 : α ^ 6 = Complex.exp ((Complex.arg α : ℂ) * Complex.I) ^ 6 := by
      rw [← hαe]
    rw [h6] at h1
    rw [← Complex.exp_nat_mul] at h1
    have h2 : ((6 : ℕ) : ℂ) = (6 : ℂ) := by norm_num
    rw [h2] at h1
    exact h1.symm
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp h6'
  have hre : (6 : ℝ) * Complex.arg α = (n : ℝ) * (2 * Real.pi) := by
    have h2 : ((6 * Complex.arg α : ℝ) : ℂ) * Complex.I
        = (((n : ℝ) * (2 * Real.pi) : ℝ) : ℂ) * Complex.I := by
      push_cast
      linear_combination hn
    have h3 := mul_right_cancel₀ Complex.I_ne_zero h2
    exact_mod_cast h3
  have hπ := Real.pi_pos
  have hval : Complex.arg α = (n : ℝ) * Real.pi / 3 := by
    have hre' : 6 * Complex.arg α = 2 * ((n : ℝ) * Real.pi) := by
      ring_nf
      ring_nf at hre
      linarith
    linarith
  have harg1 : Complex.arg α ≤ Real.pi := Complex.arg_le_pi α
  have harg2 : -Real.pi < Complex.arg α := Complex.neg_pi_lt_arg α
  have hn3 : (n : ℝ) ≤ 3 := by nlinarith [hval, harg1]
  have hn2 : (-3 : ℝ) < (n : ℝ) := by nlinarith [hval, harg2]
  have hn3' : n ≤ 3 := by exact_mod_cast hn3
  have hn2' : -3 < n := by exact_mod_cast hn2
  have habs : |(n : ℝ) * Real.pi / 3| = |(n : ℝ)| * Real.pi / 3 := by
    rw [abs_div, abs_mul, abs_of_pos hπ]
    norm_num
  interval_cases n
  · rw [hval, habs]
    norm_num [Set.mem_insert_iff]
  · rw [hval, habs]
    norm_num [Set.mem_insert_iff]
  · rw [hval, habs]
    norm_num [Set.mem_insert_iff]
  · rw [hval, habs]
    norm_num [Set.mem_insert_iff]
  · rw [hval, habs]
    norm_num [Set.mem_insert_iff]
  · rw [hval, habs]
    norm_num [Set.mem_insert_iff]

/-- **The fork at the Sato–Tate family**: at a certified prime the family's angle
is pinned to the four-point μ₆ boundary set — the shape incompatible with the
absolutely continuous equidistribution limit of the drift branch. -/
theorem seed_freeze_angle (M : MaassEigenData) (hC : MaassTowerCeiling M)
    (p : Nat.Primes) (cert : LatticeCertificate M p) :
    (maassSatoTateFamily M hC).angle p
      ∈ ({0, Real.pi / 3, 2 * Real.pi / 3, Real.pi} : Set ℝ) := by
  show |Complex.arg ((SatakeSeed.ofMaass M).satake p)| ∈ _
  exact sixth_root_angle_mem (maass_temperedness M hC p) (seed_freeze M hC p cert)

end CriticalLinePhasor.HodgeSeedFork

#print axioms CriticalLinePhasor.HodgeSeedFork.seed_freeze
#print axioms CriticalLinePhasor.HodgeSeedFork.sixth_root_angle_mem
#print axioms CriticalLinePhasor.HodgeSeedFork.seed_freeze_angle
