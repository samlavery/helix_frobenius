
## 682 — SAM: "can you retry the unconditional proof, correctly?" — the retry in the right objects (2026-09-08)
- **Objects (canonical statement, 518/carrier-geometry).** Unit-gauge fiber: phasors w(n/W)·n^{−½}e^{−it log n} on the
  carrier at head W(t) (556), the gauge ½ forced by the area law (`scaleBalanced_iff`, MP1); readout on the axis
  Re s = ½ where J is conjugation (FE = end swap, `reflection_fixes_iff`); vanishing = focal cancellation R_P = R_M of
  the two banks; 3D coupling exists iff the point is a zero AND on the axis (`nonempty_coupling_iff_zero_and_noRadialDrift`,
  `noRadialDrift_iff_carrierAbscissa`: n^{σ−½} = 1 ↔ σ = ½). Off-axis abscissae have no native support.
- **Vanishing as octave self-similarity (exact algebra, from the bank identity 680).** R_P = R_M ⟺ F̃_W(s) = 2^{1−s}F̃_{W/2}(s):
  the unsigned bank equals 2^{1−s} times itself one carrier octave down. The unsigned bank's DC (END term W^{1−s}𝒲(1−s))
  has octave ratio EXACTLY 2^{1−s} for every head — the DC is always at the vanishing condition and cancels; the
  condition falls entirely on the AC, which is ζ(s) + O(W^{−2}) for every large head. **Encountered fact: no finite head
  decides a vanishing; the fiber's finite structure (banks, octaves, head, warp) fixes the gauge and the registration and
  leaves the vanishing to the limit readout.**
- **The chain, in these objects.** (1) 3D coupling ⟺ zero on the axis [compiled, coordinate]. (2) Every zero of the
  continuation of the readout is a 3D event ⟺ RH — the transfer hypothesis, named once: EveryZeroHasSource ≡
  OneVanishingPerHeight(flowCascade) (664/674) ≡ RegisterIdentity (676) ≡ SmultIntegralSublinear (677) ≡ band
  inequality at the carrier's head (680/681a). (3) RH from any of them [compiled].
- **Attempt at (2) with 3D inputs.** The representation supplies three inputs: the gauge ½ (area law), the reflection J
  (FE), the Euler product (through the warp's closed form 554c and the sign law 652–653). The sign law is the one
  compiled inequality that goes beyond coordinates, and it speaks only about on-line zeros (it needs ζ′(ρ) = −χ conj ζ′(ρ),
  true only on the axis). No 3D quantity in the record separates an off-line pair from on-line events with a margin
  uniform in the head — the octave identity says why: the finite head sees only the AC = the limit readout.
- **Instrument statement (rule 10 form).** "Finite-head observables of the unit-gauge bank decide the axis only height by
  height (DVP), never uniformly" — property of the instrument. Refutation would be a bank-computable functional at finite
  head whose sign at an off-line pair differs from its sign at on-line events by a margin independent of the head; the
  octave identity predicts none exists since every such functional is a function of ζ(s) + O(W^{−2}). Not a claim about
  the problem: the proof needs an infinitary input (a positivity for the limit readout), and the only door with a partial
  unconditional result in these objects is the flow warp (real-rooted for λ ≥ 0.22, Polymath, on paper).
- Verdict: lateral. The retry is correct in its objects and lands on the clause by its compiled name.

## 682a — SAM (repeated verbatim): "can you retry the unconditional proof, correctly?" — the attempt run to its refusal
## (2026-09-08)
- Attempt executed as a proof skeleton from the last line backwards, in the fiber's objects, each node with status:
  N0 RH ⟸ N1 [compiled, `rh_of_oneVanishingPerHeight_flow` / `rh_of_registerIdentity` / `rh_of_smultIntegralSublinear`].
  N1 every zero of the readout's continuation is an axis vanishing ⟸ N2 [Hurwitz + faithfulness below the head:
  |F_W − η| ≤ 0.13(t/2π)^{½−σ} at W ≥ t; proof: Mellin DC of the window, no zeros needed].
  N2 for every W, the polynomial F_W has no zero in ½+ε ≤ Re s ≤ 1−ε, 0 < Im s < W, except within o(1) of Re s = 1.
  N2 is a statement about an explicit sequence of polynomials, each instance decidable by finite computation (atom census
  with the Littlewood balance, 679–681), and RH ⟺ N2 for all W.
- **The refusal, encountered while trying to prove N2 for all W:** every finite tool (Rouché against η on cells, the
  bank identity, the octave self-similarity, the sign law) reduces N2 at head W to a lower bound for |η| on the band
  below W, because F_W = η + (explicit small DC) there. Unconditional lower bounds for |ζ| inside the strip exist only in
  the classical zero-free region 1 − c/log t < σ < 1 (Vinogradov–Korobov), so N2 is PROVED unconditionally for that
  sliver of the band and for no wider band. The proof refuses at the "for all W" of a finite-checkable property — the
  same place every route has refused (424: "every road's second node IS the theorem").
- Sam's structural argument (one fiber, one phasor at a time, one focal cancellation per height) is, in these objects,
  N2 itself: below its head the fiber's only right-of-axis atoms are the alternation atoms. Measured true in every
  instance; not derivable from the finite bank's algebra, whose DC is neutral (682) and whose AC is the limit readout.
- What would discharge N2: a positivity for the limit readout with the Euler product and the reflection as its inputs —
  Weil's functional on the anchored class (534), the Toeplitz anchor ladder (624–646, leaf = von Koch), or the flow warp
  (real-rooted for λ ≥ 0.22, target λ ↓ 0). None is a restatement-free inequality in the record.
- Verdict: lateral; the attempt was made in the correct objects and refused at N2's quantifier.
