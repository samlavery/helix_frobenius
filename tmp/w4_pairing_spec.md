# W4 pairing theory — the KS twist law and the corrected obstruction calibration

**Date 2026-07-20. Instruments: tmp/w11_kstwist.sage, tmp/w12_intrinsic.sage
(both load the w10 chain; exact arithmetic over K6 throughout).**

## The contradiction that opened the session

Deformation geometry forces: the AP-cycle *deforms* along the 9-dim Weil
family, so for v tangent to the family the full obstruction vanishes —
ob(v) = q(v|_Z) = 0, i.e. v|_Z ∈ ker q = im δ. Not just π∘ob = 0: ob = 0.

But w10 measured the Bloch pairing B at **full rank 9 on the naive-symmetric
mixed rows** (labelled "Weil directions"), while B provably kills im δ
(descent certified). Both cannot hold. Verdict: the naive rows are not the
Weil rows — the KS embedding H¹(O_X)⊗W → H¹(O_Z)⊗W carries an AP scalar on
the **U-side** (restriction H¹(O_X) → H¹(O_C̃)) that w10 omitted, twin of the
W-side scalars (1−ζ^{-j}) that fixed descent in w10.

## The twist law (w11)

Scan the relative twist r in the two-line span per mixed pair:
v_mn(r) = θ_{4+m}⊗w_n + r·θ_{4+n}⊗w_m, (m,n) ∈ grade-1 × grade-2.
Candidates: ±ζ^k × {1, c₁/c₂, c₂/c₁, c₁c₂, 1/(c₁c₂), c₁², c₂²} → 6 distinct.

**Geometry selects r = 3 uniquely**: all 9 rows v_mn(3) ∈ im δ; every other
candidate (incl. naive r = 1) fails. Containment is 9 rows × 33 codim in
exact arithmetic — an algebraic identity, not a numerical pass.

**r = 3 = (1−ζ)(1−ζ̄) = Nm(1−ζ₃)**: the norm of the AP scalar. Exactly the
U-side × W-side provenance predicted — the two AP twists compose to the
rational norm.

## The intrinsic upgrade (w12)

- dim(im δ ∩ mixed-span₁₈) = **9** — with the 9-dim r=3 space contained in
  it, equality. **The Weil tangent = im δ ∩ (mixed block)**, an intrinsic,
  convention-free characterization; r = 3 is merely its coordinates.
- dim(im δ ∩ naive-Sym₂₁) = **0** — the definitive autopsy: the naive frame
  contained NO obstruction-free direction at all. The w10 "rank 9 on Weil
  rows" was the anti-twisted component masquerading under a wrong label.

## The corrected obstruction calibration (the real W4 numbers)

Transverse space (21-dim polarized KS modulo the Weil tangent — here
realized as anti-twisted mixed 9 ⊕ Sym²W₁ 6 ⊕ Sym²W₂ 6):

| block | dim | outside im δ (= obstructed) | B-rank (constant-column detection) |
|---|---|---|---|
| twisted-sym mixed (r=3) = Weil | 9 | 0 of 9 — **obstruction-free** | 0 (forced: ⊂ im δ) |
| anti-twisted mixed | 9 | 9 of 9 | **9 — fully detected** |
| Sym²W₁ | 6 | 6 of 6 | 0 — blind |
| Sym²W₂ | 6 | 6 of 6 | 0 — blind |

Every transverse direction is genuinely obstructed (outside im δ): **the
first-order Hodge/deformation locus of the AP-cycle is EXACTLY the Weil
family** — measured, exact, no convention. The constant-column (Λ⁴W*)
semiregularity slice detects the anti-twisted 9 in full and is blind to the
pure-grade 12; grade bookkeeping says those obstructions register in the
grade-shifted Λ⁴U column slices (non-constant forms).

## Consequences

1. The Bloch-pairing instrument is now fully consistent with deformation
   geometry — the contradiction is dissolved, by a measured law rather than
   a patched convention.
2. New exact law: **KS-twist r = Nm(1−ζ₃) = 3**; new intrinsic law: **Weil
   tangent = im δ ∩ mixed**.
3. First-order rigidity statement (family-level): outside the Weil tangent
   the cycle does not deform — 21 of 21 transverse directions obstructed.
4. W4 remaining: build the grade-shifted column slices (Λ⁴U-parts of
   unbalanced grade) and verify the 12 pure-block obstructions register
   there at full rank — the completion of the semiregularity detection.

Engine note: the candidate set collapsed 84 → 6 under K6 dedup; the
containment test is rank(IMD.stack(rows)) == rank(IMD) — cheap and exact.


## W13 addendum — the λΘ³ closure (same day; SUPERSEDES §Consequences pt 4)

The "grade-shifted column" pointer was REFUTED within the day: the 225
constant-form columns already exhaust the Serre-dual target H²(X,Ω⁴).
Reinterpretation forced by the twist law: the TRUE polarized KS-image =
twisted-mixed(r=3) ⊕ pure-sym (21-dim); the anti-twisted mixed rows are
POLARIZATION-BREAKING, not polarized.

w13_thetacube.sage, both predictions exact:
- rank(B on true-polarized 21) = 0   (λΘ³ demands the class-variation
  freeze on the polarized locus: Θ stays (1,1))
- rank(B on polarization-breaking 15) = 15  (Θ moves everywhere there)
- pure-anti 6/6 outside im δ (all breaking directions obstructed too)

Cross-instrument validation: the universal rigidity law ([Z] = λΘ³,
abel_prym_rigidity, Lean) PREDICTS the full block structure of a pairing
built from independent Macdonald/syzygy combinatorics. Perfect agreement.

FINAL W4 LANDING:
1. First-order deformation locus in polarized moduli = Weil family exactly
   (12/12 transverse obstructed, direct coker-δ certificate — STRONGER
   than any pairing detection).
2. Bloch semiregularity is structurally blind to all 12 — a THEOREM of
   λΘ³, not a defect; the pairing is exactly the class-variation detector.
3. The 12 obstructions are cohomologically invisible = the
   deformation-theoretic shadow of Griffiths-group content (class survives
   via theta intersections off the family; cycle cannot follow).
4. W4-as-specced (semiregular rank 12) FALSIFIED as specced; goal achieved
   by the direct route. Refuted pointer kept in the record (paper too).
