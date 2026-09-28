import RequestProject.JPairMellinBridge

/-!
# What the J-pair identification `hpair` is, for the actual spectral fiber (ledger 910)

`JPairMellinBridge.j_pair_forces_midpoint` derives `Re s = ½` from `hpair`: the fiber phasor at
`(s, n)` and the fiber phasor at `(1 − s, n)` are a physical J-pair.  This file computes what that
hypothesis is for the actual spectral fiber.  No zero premise is used and `Re s = ½` is never assumed.

* `actual_jPair` — the physical J-image of the fiber phasor at `(s, n)` is the fiber phasor at
  `(conj s, n)`, at every `s`, on a charged site: the construction's J pairs `s` with `conj s`.
* `actual_jPair_balance` — the two members of that actual pair have the same length `n^{-Re s}`,
  at every `s`: applied to the actual pair, the midpoint argument extracts nothing.
* `jPairAt_iff_re_half` — at a charged site `n > 1` of a real character,
  `JPairAt χ s n ↔ Re s = ½` for every `s`: pairing `s` with `1 − s` is a J-pair exactly when
  `1 − s = conj s`.
* `jPairAt_congr_re` — the pair hypothesis at `s` depends only on `Re s`; whether `L(s) = 0` plays
  no part.

So a composition `L(s) = 0 → JPairAt χ s n → Re s = ½` needs the step `L(s) = 0 → JPairAt χ s n`,
which by `jPairAt_iff_re_half` is the step `L(s) = 0 → Re s = ½`.

No `sorry`, no `axiom`.
-/

noncomputable section
open Complex ConeProjection

namespace CriticalLinePhasor.GlobalHelix

open Phasor3D SpectralFiber

variable {q : ℕ} [NeZero q]

/-- The pair hypothesis `hpair` of `j_pair_forces_midpoint`, named. -/
def JPairAt (χ : DirichletCharacter ℂ q) (s : ℂ) (n : ℕ) : Prop :=
  ∃ f : Fiber,
    realize f = ((spectralFiber (fun k => χ k) s n).1.re,
      (spectralFiber (fun k => χ k) s n).1.im, (spectralFiber (fun k => χ k) s n).2) ∧
    realize (globalHelixInvolution f) = ((spectralFiber (fun k => χ k) (1 - s) n).1.re,
      (spectralFiber (fun k => χ k) (1 - s) n).1.im, (spectralFiber (fun k => χ k) (1 - s) n).2)

omit [NeZero q] in
/-- **The actual physical J-pair**: the J-image of the fiber phasor at `(s, n)` is the fiber phasor
at `(conj s, n)`, at every `s`, on a charged site of the character. -/
theorem actual_jPair (χ : DirichletCharacter ℂ q) (s : ℂ) (n : ℕ)
    (hcharged : χ n = 1 ∨ χ n = -1) :
    ∃ f : Fiber,
      realize f = ((spectralFiber (fun k => χ k) s n).1.re,
        (spectralFiber (fun k => χ k) s n).1.im, (spectralFiber (fun k => χ k) s n).2) ∧
      realize (globalHelixInvolution f) =
        ((spectralFiber (fun k => χ k) ((starRingEnd ℂ) s) n).1.re,
          (spectralFiber (fun k => χ k) ((starRingEnd ℂ) s) n).1.im,
          (spectralFiber (fun k => χ k) ((starRingEnd ℂ) s) n).2) := by
  refine ⟨(‖(spectralFiber (fun k => χ k) s n).1‖,
    Complex.arg (spectralFiber (fun k => χ k) s n).1,
    (spectralFiber (fun k => χ k) s n).2), realize_phasor_polar _, ?_⟩
  rw [realize_j_phasor_polar, spectralFiber_conj_charged (fun k => χ k) s n hcharged]

/-- The two members of the actual J-pair have the same length at every `s`. -/
theorem actual_jPair_balance (χ : DirichletCharacter ℂ q) (hq : χ.IsQuadratic) (s : ℂ) (n : ℕ)
    (hn : 0 < n) :
    mag3 (spectralFiber (fun k => χ k) s n) =
      mag3 (spectralFiber (fun k => χ k) ((starRingEnd ℂ) s) n) := by
  unfold spectralFiber
  rw [phasor3D_mag3 χ hq _ _ n hn, phasor3D_mag3 χ hq _ _ n hn, Complex.conj_re]

/-- **The identification, computed.**  At a charged site `n > 1` of a real character, the fiber
phasors at `s` and at `1 − s` form a physical J-pair exactly when `Re s = ½`, for every `s`. -/
theorem jPairAt_iff_re_half (χ : DirichletCharacter ℂ q) (hq : χ.IsQuadratic) (s : ℂ) (n : ℕ)
    (hn : 1 < n) (hcharged : χ n = 1 ∨ χ n = -1) :
    JPairAt χ s n ↔ s.re = 1 / 2 := by
  constructor
  · intro h
    exact j_pair_forces_midpoint χ hq s n hn h
  · intro h
    have hs : 1 - s = (starRingEnd ℂ) s := by
      apply Complex.ext
      · rw [Complex.sub_re, Complex.one_re, Complex.conj_re, h]
        norm_num
      · rw [Complex.sub_im, Complex.one_im, Complex.conj_im]
        ring
    unfold JPairAt
    rw [hs]
    exact actual_jPair χ s n hcharged

/-- The pair hypothesis depends only on `Re s`: two chart points with the same real part have the
same pair status, whether or not either is a zero. -/
theorem jPairAt_congr_re (χ : DirichletCharacter ℂ q) (hq : χ.IsQuadratic) {s s' : ℂ} (n : ℕ)
    (hn : 1 < n) (hcharged : χ n = 1 ∨ χ n = -1) (h : s.re = s'.re) :
    JPairAt χ s n ↔ JPairAt χ s' n := by
  rw [jPairAt_iff_re_half χ hq s n hn hcharged, jPairAt_iff_re_half χ hq s' n hn hcharged, h]

end CriticalLinePhasor.GlobalHelix

#print axioms CriticalLinePhasor.GlobalHelix.actual_jPair
#print axioms CriticalLinePhasor.GlobalHelix.actual_jPair_balance
#print axioms CriticalLinePhasor.GlobalHelix.jPairAt_iff_re_half
#print axioms CriticalLinePhasor.GlobalHelix.jPairAt_congr_re
