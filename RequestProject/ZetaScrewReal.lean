import RequestProject.ZetaScrewHelix
import RequestProject.FoliatedGlobalPolarization
import RequestProject.ZetaContourXiReceiverIdentification3D

/-!
# The zero-side screw function is real, and nonnegative on the line (Track E)

`zetaScrew t = Σ_ρ m_ρ (1 − e^{i t_ρ t})/t_ρ²` pairs each zero with its conjugate: the
spectral coordinate of `ρ̄` is `−t̄_ρ` (`spectralCoord_conj`), the multiplicity is invariant
(`xiOrderNat_conj`, compiled), and the term goes to its conjugate (`screwTerm_conjZero`).
Reindexing the sum by the conjugation involution on the compiled zero subtype gives

* `zetaScrew_conj`, `zetaScrew_im` — **Ψ is real** at every `t`;
* `zetaScrew_re_nonneg_of_online` — if every zero is on the line, `Ψ(t) ≥ 0` (each term is
  `m_ρ(1 − cos t_ρ t)/t_ρ² ≥ 0`): the forward half of Suzuki's pointwise criterion.

The converse (Ψ ≥ 0 ∀t ⟹ RH) is Suzuki [13, Thm 1.7/11.1], not compiled.
No `sorry`, no `axiom`.
-/

open Complex Filter Topology

noncomputable section

namespace CriticalLinePhasor.HilbertPolya

open CriticalLinePhasor.StBridge

/-- Conjugation as an involution of the compiled zero subtype. -/
def conjZero : Zeros ≃ Zeros where
  toFun ρ := ⟨(starRingEnd ℂ) ρ.val,
    CriticalLinePhasor.ContourArgument.conj_mem_nontrivialZeros ρ.2⟩
  invFun ρ := ⟨(starRingEnd ℂ) ρ.val,
    CriticalLinePhasor.ContourArgument.conj_mem_nontrivialZeros ρ.2⟩
  left_inv ρ := by
    apply Subtype.ext
    simp
  right_inv ρ := by
    apply Subtype.ext
    simp

@[simp] theorem conjZero_val (ρ : Zeros) : (conjZero ρ).val = (starRingEnd ℂ) ρ.val := rfl

/-- The spectral coordinate of the conjugate zero is minus the conjugate coordinate. -/
theorem spectralCoord_conj (ρ : ℂ) :
    spectralCoord ((starRingEnd ℂ) ρ) = -((starRingEnd ℂ) (spectralCoord ρ)) := by
  unfold spectralCoord
  simp only [map_mul, map_neg, map_sub, Complex.conj_I, map_one, map_ofNat, map_div₀]
  ring

/-- The screw term of the conjugate zero is the conjugate term. -/
theorem screwTerm_conjZero (t : ℝ) (ρ : Zeros) :
    screwTerm t (conjZero ρ) = (starRingEnd ℂ) (screwTerm t ρ) := by
  unfold screwTerm
  rw [conjZero_val, CriticalLinePhasor.FoliatedGlobalPolarization.xiOrderNat_conj,
    spectralCoord_conj]
  have hexp : Complex.exp (Complex.I * (-((starRingEnd ℂ) (spectralCoord ρ.val))) * (t : ℂ))
      = (starRingEnd ℂ) (Complex.exp (Complex.I * spectralCoord ρ.val * (t : ℂ))) := by
    rw [← Complex.exp_conj]
    congr 1
    rw [map_mul, map_mul, Complex.conj_I, Complex.conj_ofReal]
    ring
  rw [hexp, neg_sq, map_div₀, map_mul, map_natCast, map_sub, map_one, map_pow]

/-- **Ψ is real**: conjugation fixes the zero-side screw function. -/
theorem zetaScrew_conj (t : ℝ) : (starRingEnd ℂ) (zetaScrew t) = zetaScrew t := by
  unfold zetaScrew
  calc (starRingEnd ℂ) (∑' ρ : Zeros, screwTerm t ρ)
      = ∑' ρ : Zeros, (starRingEnd ℂ) (screwTerm t ρ) := by
        rw [← Complex.conjCLE_apply, Complex.conjCLE.map_tsum]
        simp only [Complex.conjCLE_apply]
    _ = ∑' ρ : Zeros, screwTerm t (conjZero ρ) :=
        tsum_congr (fun ρ => (screwTerm_conjZero t ρ).symm)
    _ = ∑' ρ : Zeros, screwTerm t ρ := conjZero.tsum_eq (screwTerm t)

theorem zetaScrew_im (t : ℝ) : (zetaScrew t).im = 0 :=
  Complex.conj_eq_iff_im.mp (zetaScrew_conj t)

/-- On-line zeros have nonnegative screw terms: `m(1 − cos(t_ρ t))/t_ρ² ≥ 0`. -/
theorem screwTerm_re_nonneg_of_online {ρ : Zeros} (hre : ρ.val.re = 1 / 2) (t : ℝ) :
    0 ≤ (screwTerm t ρ).re := by
  have h := helix_chordal_term_online hre t 0
  have h0 : (0 : ℝ) ≤ Complex.normSq (helixVec t ρ - helixVec 0 ρ) := Complex.normSq_nonneg _
  rw [h, sub_zero] at h0
  linarith

/-- **Ψ ≥ 0 when every zero is on the line** — the forward half of the pointwise criterion. -/
theorem zetaScrew_re_nonneg_of_online (hRH : ∀ ρ ∈ ZD.NontrivialZeros, ρ.re = 1 / 2) (t : ℝ) :
    0 ≤ (zetaScrew t).re := by
  unfold zetaScrew
  rw [Complex.re_tsum (screwTerm_summable t)]
  exact tsum_nonneg (fun ρ => screwTerm_re_nonneg_of_online (hRH ρ.val ρ.2) t)

end CriticalLinePhasor.HilbertPolya

#print axioms CriticalLinePhasor.HilbertPolya.screwTerm_conjZero
#print axioms CriticalLinePhasor.HilbertPolya.zetaScrew_im
#print axioms CriticalLinePhasor.HilbertPolya.zetaScrew_re_nonneg_of_online
