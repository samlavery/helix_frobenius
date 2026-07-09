# Beyond Endoscopy — first numerical instrument, read through house optics

`tmp/be_instrument.py`, results `tmp/be_instrument_results.txt`. Built on house machinery
(owner directive): L(1,χ) = `obstruction_general.py` character fiber; elliptic kernel = the
two-clock object of `RequestProject/TwoClockWeightLaw.lean`; Phase-2 as two-lane balance
(`lane_balance.py`); Phase-3 as DC-clock detection (`dc_split`/`sym2_dc_offset`). Never-clip
throughout; every claim random-controlled; tiered.

**PHASE 1 — ANCHOR [anchor], PASS.** The full level-1 Eichler–Selberg geometric side
reproduces Tr T(pᵏ) on S_k(SL₂ℤ) to exact machine-integer precision: τ(p) for k=12, all
primes; τ(pʳ) via exact Hecke recursion; genuine eigenvalues for k=16–26 (certified by exact
multiplicativity a_p a_q=a_pq, a_{p²}=a_p²−p^{k−1}); Tr T(1)=dim S_k. The house character
fiber lands **28/28** class numbers (17 imaginary + 11 real, regulator in the BSD slot), and
`hw(D)` read off `L1_chi_fiber` matches from-scratch form counts; the elliptic term via the
house L(1,χ) fiber matches exact Hurwitz to 1e-11. **The elliptic kernel is verified to be the
two-clock character exactly: P_k(t,n) = n^{(k−2)/2}·symTrace(k−2, θ) = n^{(k−2)/2}·U_{k−2}(cos θ)**,
θ the Satake angle of each conjugacy class.

**PHASE 2 — Problem-VI cancellation [measured].** Read as a two-lane balance. At k=12: lane E
(elliptic) → +1/(k−1), lane H (hyp+unip) → −1/(k−1), both **full amplitude**; readout E+H(+id)
→ 2e-4 (readout² = 4.5e-8 vs lane energy 0.017). **VERDICT: BALANCED DOUBLET** — neither lane
vanishes; the cancellation lives in the readout only, the same shape as the ζ-zero lane
balance. Confirmed universal at k=16 (amplitude 1/15). Random control: structural (1000×
better than sign-scrambled). Mechanism anatomy: the cancellation is **exponent-local** — within
each max-prime-power-exponent class E and H are near-mirror-images (|sum|/|E| ≈ 0.03); the
primes-only control gives 0 for each lane (Altuğ eq. 3), confirming the funding comes from
high prime-power n.

**PHASE 3 — Sym^r productivity as DC-clock detection [measured/interpretation].** DC census:
Sym² carries a genuine +1 DC clock (sym2_dc_offset; DC/(DC+MOV)=0.41), Sym¹/Sym³ carry none —
matching Sarnak's "std & Sym² productive." **Honest complication (falsifiability register):**
the DC clock recurs for all even r (Sym⁴ too), so the k=1 census gives an even/odd split, not a
clean Sym³ wall — the boundary needs the full n-sum Poisson step, not just the prime comb.
Control-verified signal: the arithmetic Sym²/Sym⁴ DC assembly is *suppressed* vs
equidistributed angles (−1.42 vs +8.3), Sato-Tate damping the DC line.

**Falsification hits: zero.** No non-collapsing readout, no vanishing lane, no two-clock kernel
break.
