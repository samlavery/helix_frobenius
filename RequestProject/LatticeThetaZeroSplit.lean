import RequestProject.ExpMellinNormValue
import RequestProject.GeneralLatticeTheta

/-!
# Splitting the constant term off the lattice theta

`RSPairInterface` gives `Λ(z,s) = mellin (latticeThetaC z · − 1) s`, so the interchange needs the
theta *minus its constant term* presented as a sum over **nonzero** lattice points.

The constant term is the origin's contribution and nothing else: `gram z (0,0) = 0`, so that term is
`e⁰ = 1` exactly.  Subtracting `1` is therefore not a normalization convention — it is deleting the
single lattice point where the Gram form degenerates, which is also the only point where
`eisRealSummand` is undefined.  The two exclusions are the same exclusion.
-/

open MeasureTheory UpperHalfPlane
open scoped Real

namespace CriticalLinePhasor.Unfolding

open CriticalLinePhasor.EpsteinTheta

/-- The Gram form vanishes exactly at the origin's contribution. -/
lemma gram_zero (z : ℍ) : gram z (0, 0) = 0 := by
  rw [gram]
  norm_num

/-- **The theta minus its constant term is the sum over nonzero lattice points.** -/
theorem latticeTheta_sub_one (z : ℍ) {t : ℝ} (ht : 0 < t) :
    latticeTheta z t - 1 =
      ∑' p : {p : ℤ × ℤ // ¬(p.1 = 0 ∧ p.2 = 0)},
        Real.exp (-(Real.pi * t) * gram z p.1) := by
  have hsum := summable_latticeTheta_term z ht
  have hsplit := Summable.tsum_add_tsum_compl
    (f := fun p : ℤ × ℤ => Real.exp (-(Real.pi * t) * gram z p))
    (s := ({((0 : ℤ), (0 : ℤ))} : Set (ℤ × ℤ)))
    (hsum.subtype _) (hsum.subtype _)
  have hone : (∑' x : ({((0 : ℤ), (0 : ℤ))} : Set (ℤ × ℤ)),
      Real.exp (-(Real.pi * t) * gram z x)) = 1 := by
    rw [tsum_singleton ((0 : ℤ), (0 : ℤ))
      (fun p : ℤ × ℤ => Real.exp (-(Real.pi * t) * gram z p)), gram_zero]
    norm_num
  rw [hone] at hsplit
  have hset : ({((0 : ℤ), (0 : ℤ))} : Set (ℤ × ℤ))ᶜ =
      {p : ℤ × ℤ | ¬(p.1 = 0 ∧ p.2 = 0)} := by
    ext p
    simp [Prod.ext_iff]
  rw [hset] at hsplit
  rw [latticeTheta, ← hsplit, add_sub_cancel_left]
  rfl

end CriticalLinePhasor.Unfolding

#print axioms CriticalLinePhasor.Unfolding.gram_zero
#print axioms CriticalLinePhasor.Unfolding.latticeTheta_sub_one
