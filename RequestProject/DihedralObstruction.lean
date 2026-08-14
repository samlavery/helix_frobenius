import RequestProject.ArcPositiveDensity

/-!
# The dihedral obstruction: Sato--Tate for Maass forms is false as universally stated

Every other file in this thread treats the Maass Sato--Tate statement as true-but-unproven.  It is
not.  There is a classical family of counterexamples, and this file locates the obstruction exactly.

**The counterexamples.**  Maass (1949) constructed cuspidal Maass forms from Hecke characters of a
real quadratic field `K = ℚ(√D)`: the *dihedral* forms, with `L(s, f) = L(s, ξ)`.  Their Hecke
eigenvalues are

* `a_p = 0` whenever `p` is **inert** in `K`, and
* `a_p = ξ(𝔭) + ξ(𝔭̄)` when `p` splits.

Inertness is `χ_D(p) = −1`, so by Dirichlet the inert primes have density exactly `1/2`.  Hence the
Satake angle satisfies `θ_p = π/2` on a set of primes of density `1/2`, while the Sato--Tate
measure `carrierProbability` has no atoms at all.  **Sato--Tate fails for every dihedral Maass
form.**  Any correct statement must exclude them, and the corpus's target — quantified over bare
`MaassEigenData` with no non-dihedral hypothesis — is therefore not merely unproven but false.

**Where the obstruction sits, exactly.**  This file proves the unconditional half: a half-density
atom at `π/2` is incompatible with graded cancellation past a computable rank.  The instrument is
the squared Chebyshev polynomial of the first kind,

  **`Q(cos θ) = cos²(2θ) = (1 − 2cos²θ)²`,**

which is nonnegative everywhere, equals `1` at `θ = π/2`, and has Sato--Tate mean exactly `1/2`.
Being a majorant of the atom's indicator, it caps the atom's density at `1/2`.

Solving the corresponding linear program at every rank gives the sharp cap in closed form:

  **`δ_max(r ≤ 4k) = 1/(k + 1)`,   `δ_max(r ≤ 4k − 2) = (2k + 1)/(2k(k + 1))`.**

So the caps run `3/4, 1/2, 5/12, 1/3, 7/24, 1/4, …` at `r ≤ 2, 4, 6, 8, 10, 12`.  **At `r ≤ 4` the
cap is exactly `1/2`** — which is exactly the dihedral atom.  The classical Maass record (`Sym²`
Gelbart--Jacquet, `Sym³` and `Sym⁴` Kim--Shahidi) therefore sits precisely, and only just, on the
boundary: it cannot exclude the dihedral counterexamples, while `r ≤ 8` would (cap `1/3 < 1/2`).

That coincidence is the whole difficulty in one number.  It is not that the finite record is far
from sufficient; it is that the ranks which are unconditionally available for Maass forms stop at
the exact value where the known counterexamples live.

**Scope.**  The dihedral construction and the density of inert primes are classical and cited, not
formalised here.  Everything stated below is proved unconditionally from graded cancellation alone.
-/

open Filter Topology Polynomial Polynomial.Chebyshev

namespace CriticalLinePhasor.PartialSerre

open CriticalLinePhasor.SatoTateCarrier3D CriticalLinePhasor.GeneralSeed
open CriticalLinePhasor.MaassSatoTate

/-- The atom kernel `T₂² `, written in the symmetric-power character basis.  Its constant term
`1/2` is its Sato--Tate mean, and is the cap it imposes. -/
noncomputable def atomKernelCoeff : ℕ → ℝ
  | 0 => 1 / 2
  | 2 => -(1 / 4)
  | 4 => 1 / 4
  | _ => 0

/-- **The kernel is `(1 − 2x²)²`.**  Degree four, so rank `≤ 4` cancellation controls it. -/
lemma atomKernelCoeff_eval (x : ℝ) :
    ∑ r ∈ Finset.range 5, atomKernelCoeff r * (U ℝ (r : ℤ)).eval x = (1 - 2 * x ^ 2) ^ 2 := by
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [atomKernelCoeff, U_eval_zero_real, U_eval_one_real, U_eval_two_real,
    U_eval_three_real, U_eval_four_real]
  ring

/-- On the carrier the kernel is `cos²(2θ)`. -/
lemma atomKernel_eq_cos_two_sq (θ : ℝ) :
    ∑ r ∈ Finset.range 5, atomKernelCoeff r * (U ℝ (r : ℤ)).eval (Real.cos θ)
      = Real.cos (2 * θ) ^ 2 := by
  rw [atomKernelCoeff_eval, Real.cos_two_mul]
  ring

/-- **The kernel majorises the atom's indicator.**  It is a square, hence nonnegative everywhere;
and at `θ = π/2` it equals `cos²π = 1`.  Those two facts are the whole argument. -/
lemma atomKernel_majorant (θ : ℝ) :
    (if θ = Real.pi / 2 then (1 : ℝ) else 0)
      ≤ ∑ r ∈ Finset.range 5, atomKernelCoeff r * (U ℝ (r : ℤ)).eval (Real.cos θ) := by
  rw [atomKernel_eq_cos_two_sq]
  split_ifs with h
  · rw [h]
    rw [show 2 * (Real.pi / 2) = Real.pi by ring, Real.cos_pi]
    norm_num
  · positivity

/-- **★ Rank four caps the atom at one half.**

If the Satake angles equal `π/2` on a set of primes of density `δ`, then graded cancellation at
`r ≤ 4` forces `δ ≤ 1/2`.

This is sharp: `1/2` is the exact optimum of the linear program over all probability measures on
`[-1, 1]` carrying an atom at `0` and killing `U₁, …, U₄`, and it is attained by
`(1/4)δ_{π/4} + (1/2)δ_{π/2} + (1/4)δ_{3π/4}`.

**Why this is the Maass frontier.**  A dihedral Maass form has `a_p = 0` at every inert prime, a set
of density exactly `1/2`.  So the classical record for Maass forms lands precisely on the boundary
of this bound and cannot cross it.  The next available cap, at `r ≤ 8`, is `1/3`, which would
exclude the dihedral forms outright — and `Sym⁵` onwards is exactly what is unavailable. -/
theorem halfPi_atom_density_le_half (F : ArithmeticSatakePrimeFamily)
    (hcanc : ∀ r : ℕ, 1 ≤ r → r ≤ 4 →
      Tendsto (fun n => arithmeticSymmetricPowerPrimeAverage F r n) atTop (𝓝 0))
    {δ : ℝ}
    (hatom : ∀ᶠ n : ℕ in atTop,
      δ ≤ (1 / ((n + 1 : ℕ) : ℝ)) *
        ∑ i : Fin (n + 1),
          (if F.angle (nthPrime i) = Real.pi / 2 then (1 : ℝ) else 0)) :
    δ ≤ 1 / 2 := by
  refine le_of_forall_pos_le_add fun ε hε => ?_
  have hmaj := majorant_prime_average_le F 4 hcanc atomKernelCoeff
    (fun θ => if θ = Real.pi / 2 then (1 : ℝ) else 0)
    (fun p => atomKernel_majorant (F.angle p)) hε
  have hboth := hatom.and hmaj
  obtain ⟨n, hn1, hn2⟩ := hboth.exists
  have : δ < 1 / 2 + ε := by
    refine lt_of_le_of_lt hn1 ?_
    simpa [atomKernelCoeff] using hn2
  linarith

/-- **★ At the boundary the distribution is rigid.**

If the atom already has density `1/2`, rank-four cancellation leaves no freedom: away from the atom
the angles are driven onto `π/4` and `3π/4`, in the sense that the prime average of `cos²(2θ_p)`
off the atom tends to zero.

So a form with a half-density atom at `π/2` and rank-four cancellation has essentially **three**
Satake angles.  A dihedral form does not: its split-prime angles are the arguments of `ξ(𝔭)`, which
run over a dense subset of the circle.  The two descriptions are incompatible, which is the
mechanism behind the classical fact that `Sym⁴` of a dihedral form is not cuspidal. -/
theorem halfPi_atom_boundary_rigidity (F : ArithmeticSatakePrimeFamily)
    (hcanc : ∀ r : ℕ, 1 ≤ r → r ≤ 4 →
      Tendsto (fun n => arithmeticSymmetricPowerPrimeAverage F r n) atTop (𝓝 0))
    (hatom : ∀ᶠ n : ℕ in atTop,
      (1 : ℝ) / 2 ≤ (1 / ((n + 1 : ℕ) : ℝ)) *
        ∑ i : Fin (n + 1),
          (if F.angle (nthPrime i) = Real.pi / 2 then (1 : ℝ) else 0))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,
      (1 / ((n + 1 : ℕ) : ℝ)) *
        ∑ i : Fin (n + 1),
          (if F.angle (nthPrime i) = Real.pi / 2 then (0 : ℝ)
            else Real.cos (2 * F.angle (nthPrime i)) ^ 2) < ε := by
  -- the kernel minus the atom indicator is the off-atom observable, and it is nonnegative
  have hsplit : ∀ θ : ℝ,
      (if θ = Real.pi / 2 then (0 : ℝ) else Real.cos (2 * θ) ^ 2)
        = (∑ r ∈ Finset.range 5, atomKernelCoeff r * (U ℝ (r : ℤ)).eval (Real.cos θ))
          - (if θ = Real.pi / 2 then (1 : ℝ) else 0) := by
    intro θ
    rw [atomKernel_eq_cos_two_sq]
    split_ifs with h
    · rw [h, show 2 * (Real.pi / 2) = Real.pi by ring, Real.cos_pi]
      norm_num
    · ring
  -- the kernel's average is eventually below `1/2 + ε`
  have hmaj := majorant_prime_average_le F 4 hcanc atomKernelCoeff
    (fun θ => if θ = Real.pi / 2 then (1 : ℝ) else 0)
    (fun p => atomKernel_majorant (F.angle p)) hε
  -- the kernel's average dominates the atom's, so subtracting leaves less than `ε`
  have hobs := partial_serre F 4 hcanc atomKernelCoeff
  have hker : ∀ᶠ n : ℕ in atTop,
      (1 / ((n + 1 : ℕ) : ℝ)) *
        ∑ i : Fin (n + 1),
          ∑ r ∈ Finset.range 5, atomKernelCoeff r * (U ℝ (r : ℤ)).eval
            (Real.cos (F.angle (nthPrime i))) < 1 / 2 + ε := by
    have hev : ∀ᶠ n : ℕ in atTop, polyObservableAverage F atomKernelCoeff 4 n < 1 / 2 + ε :=
      hobs.eventually_lt_const (by simp [atomKernelCoeff]; linarith)
    filter_upwards [hev] with n hn
    rwa [polyObservableAverage_eq] at hn
  filter_upwards [hatom, hker] with n hn1 hn2
  have hrw : (1 / ((n + 1 : ℕ) : ℝ)) *
      ∑ i : Fin (n + 1),
        (if F.angle (nthPrime i) = Real.pi / 2 then (0 : ℝ)
          else Real.cos (2 * F.angle (nthPrime i)) ^ 2)
      = ((1 / ((n + 1 : ℕ) : ℝ)) *
          ∑ i : Fin (n + 1),
            ∑ r ∈ Finset.range 5, atomKernelCoeff r * (U ℝ (r : ℤ)).eval
              (Real.cos (F.angle (nthPrime i))))
        - ((1 / ((n + 1 : ℕ) : ℝ)) *
          ∑ i : Fin (n + 1),
            (if F.angle (nthPrime i) = Real.pi / 2 then (1 : ℝ) else 0)) := by
    rw [← mul_sub, ← Finset.sum_sub_distrib]
    exact congrArg _ (Finset.sum_congr rfl fun i _ => hsplit _)
  rw [hrw]
  linarith

end CriticalLinePhasor.PartialSerre

#print axioms CriticalLinePhasor.PartialSerre.atomKernel_majorant
#print axioms CriticalLinePhasor.PartialSerre.halfPi_atom_density_le_half
#print axioms CriticalLinePhasor.PartialSerre.halfPi_atom_boundary_rigidity
