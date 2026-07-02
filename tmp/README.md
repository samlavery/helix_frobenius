# tmp/ — experiment scripts and what each one established

Session record 2026-07-01/02. Full narrative with tagged claims: `../FIBER_DYNAMICS.md`.
Result tables from background agents: `gl2_longspan_results.txt`, `pi_clock_results.txt`.
Cached data: `reverb_data.npz` (1517 zeros/rates/bumps to t=2000), `amp_S*.npz` (amplitude
samples), `gl2long_*_lambda.npy` (exact Δ/E11 coefficient banks).

## Verification & the locator

| script | does | established |
|---|---|---|
| `independent_verify.py` | independent battery vs the repo's Python (own Hurwitz/quadrature/mpmath, never the repo's pipeline) | all 35 reference zeros genuine (Newton dist ≤ 5e-15); repo math correct & Lean-faithful; envelope constant is character-dependent (0.667 χ₃ / 0.500 η) |
| `focal_growth_scan.py` | focal-closure growth locator: head-coupled readout ω = log Z, self-similar growth window, lane-balance closure | the fiber locates its own zeros with **no L, no seeds** (η + 4 characters; ζ₁ at Z = 1.376M to 1.1e-12); true closures 5+ orders below spurious dips; closure sharpens with height |
| `ab_magnitude_pi3.py` | A/B: growth laws; π/3 arrow scale | growth-from-zero is **load-bearing** (no growth displaces zeros ~1e-2); ramp shape immaterial; π/3 in the arrows is **pure gauge** |
| `grand_rh_scan.py` | grand-RH families: complex χ (lane polygon), Δ (exact η²⁴ via limb-split FFT), E11 (η²η(q¹¹)²) | mechanism universal: all zeros found & independently certified (Δ's 2nd zero to 3.9e-12) |

## Reverb (amplitude side)

| script | does | established |
|---|---|---|
| `residue_dissipation.py` | rates/arches at ζ zeros 1–60 + the classic Lehmer pair | residues exist (all vanishings simple); unfolded rates gap-uncorrelated; Lehmer pair in the quadratic regime (tent fails 25×); lanes collapse jointly across the pair |
| `reverb_clusters.py` | 1517 zeros to t=2000 (grid extraction = RvM count exactly); crossover, product law, CUE | product law R̂ ∝ S^1.01; bump exponents 2.01→0.55 by gap; Keating–Snaith N ≈ 6 (N=60 spurious); cluster-corrected KS(CUE, fiber) = 0.066 |
| `reverb_targets.py` | Sam's 66678/71733 candidates, both readings, t ≈ 52–72k | product law R̂/g = O(1) at all 12 tightest pairs; tightest 55713.385/.462 (g = 0.112, 7.5× suppression) |
| `reverb_profiles.py` | arch geometry at 4 tightest triples + Lehmer + 55713 | symmetric arch φ ≈ 0.5 in tight gaps; triple peak ratios match the parameter-free product model to 2–6% |
| `gourdon_pair_test.py` | Gourdon ultra-pair t ≈ 1.085e10 (R-S main sum + mpmath base phases; ordinates as strings) | product law at g = 8.2e-5 (R̂/g = 2.93); arch φ = 0.500; tent fails 8300× |
| `reverb_window_units.py`, `reverb_clock_hight.py` | clock-discrimination fits (bands; high-t) | **superseded**: fed the growth-clock case later retracted (see below) |
| `horizon_sweep.py` | φ-skew horizon at 5 heights + 2 characters (parts A–D) | **no horizon** — full product wins monotonically to 5–8 spacings; eta-fiber φ-noise floor found via method bridge; conductor axis verified (χ₂₉@1875 ≡ ζ@60k) |
| `amp_cross.py` | amplitude crossover, 7 de-modulated samples (ζ ×4 heights + χ₂₉, χ₅ᶜ, χ₁₀₁) | curves collapse in **unfolded** units (score 0.137 vs 1.850 raw); one universal curve b ≈ 1.35·g^2.3; growth-clock reading retired; eta prefactor must always be de-modulated |
| `offaxis_bounds.py` | per-zero off-axis displacement bounds from the vanishing floors (1517 zeros, t ≤ 2000) | every vanishing collapses to the taper floor (median 1.8e-4) ⇒ δ ≤ 4.5e-3 median / 1.3e-2 worst — the register's collapse channel quantified, zero hits |

## The medium (spectroscopy)

| script | does | established |
|---|---|---|
| `ambient_spectrum.py` | prime-clock spectroscopy of log\|L\| (ζ, χ₅ᶜ, χ₂₉) | Euler lines at ln p^k (ζ ln2: 2.5e6×); composite nulls; **conductor holes** (χ₅ᶜ ln5 = 0.7 vs ζ 648k; χ₂₉ ln29 = 2.6 vs ζ 66k) |
| `gl2_explore.py` | GL(2) spectroscopy + universal curve (Δ, E11) | Satake weight ordering incl. Δ's ln4 > pattern (8.5× GL(1)); E11 ln4 silence; universal curve extends to degree 2 |
| `cm_comb.py` | 32.a CM comb (ℤ[i]) | ln9 = brightest line while ln3/7/11 dead — two-clock (conjugate Satake pair) medium confirmed; its "ln4 ghost" later dissolved as skirt artifact |
| `eisenstein_comb.py` | 27.a mirror comb (ℤ[ζ₆] — the carrier's own field) | perfect role swap (ln9 dead/bad-prime, ln4 bright); **alternating 2-tower** dead-alive-dead-alive; "ln8 ghost" = ln7 skirt |
| `zeta_control.py` | ζ at the same span/height as the Δ run | weak lines sink below short-span floors generically — resolved the "ln13 anomaly" as a floor effect |
| `ghost_locate.py`, `ghost27.py` | local-maximum enumeration of the ghost windows | both "forbidden lines" were Hann skirts of giant Euler lines (only maxima: ln5 ±0.0008; ln7 ±0.0001) — **method law: peak enumeration, never window-max ratios** |
| `scale_check.py` | gauge identity F_s = s^{-1/2}e^{-iy ln s}F₁ numerically | exact to 1e-13 for s ∈ {1, π/6, π/3, π/2, 2π/3}: amplitude/spectroscopy results scale-invariant |
| `sym2_spectroscopy.py` | Sym²Δ (GL(3), Gelbart–Jacquet) medium from exact τ via the (λ²−1) ladder; matched ζ control; span 2200, N=800k | **functoriality as measurement**: weight law 0.82±0.13 over 18 clean lines (0.82 = additive degree-3 floor, → 1 with span); **two-sided kill-shot: p=43,73 (λ≈0) silent-in-base/loud-in-lift measured LOUD; p=11,19 (λ²≈1, θ=π/3) loud-in-base/silent-in-lift measured DEAD** — every decisive prime follows the lift; composite nulls hold |
| `strand_phase.py` | complex spectrum of log F: line PHASES (ζ calibration, χ₈, χ₅ ord 4, Δ, E11) | **the medium is strand-aware**: line phase = arg χ(p^k) (χ₅ ln2 = +0.491π for χ(2)=i; all quadrants correct, span-locked) and sign λ_p for GL(2) (Δ/E11 all 8 lines); ramified holes wander = correctly no line |
| `st_cells.py` | fiber-native counting statistic S(t) = N_fiber − θ/π − 1 at t≤2000 + t≈51k; number variance vs GUE | **Σ²(L) tracks GUE (exact) in the rigid regime, saturates at Berry's outer scale log(t/2π)/π, saturation moves outward with height (2.4 → 3.4 sp)** — counting and rate observables share one clock; Selberg C ≈ 1.43 stable; sawtooth caveat stated |
| `ambient_memory.py` | Euler-line census → notch → residual spectrum/autocorrelation vs surrogates (ζ, χ₅ᶜ, t ∈ [1000,3000]) | **the ambient spectrum is supported on log ℚ₊^×**: 81+79 lines all ln p^k; every residual peak = intermodulation ln p ± ln q (forced mixing, lock-and-grow verified); nothing off the lattice; π-multiples ≤ 6.5e-5× ln2 power — **register NO HIT** |
| `acf_surrogates.py` | χ₅ ACF loose end: surrogate decomposition (IAAFT + AAFT-white + IID bootstrap, 2 clip levels) | **resolved, zero memory excess**: IAAFT circular for ACF stats (real = own spectrum band to 1e-4); marginal explains ~nothing (0.009 vs 0.34 — dip-clipping suspicion refuted); colored residual spectrum (Euler skirts + intermods + clip ripple) explains all; χ₅-vs-ζ split = spectrum-shape noise in max-over-lags; lag profile = sub-spacing **reverb arch**, nothing multi-spacing — register stays clean |

## The weld and BSD (rank ladder)

| script | does | established |
|---|---|---|
| `bsd_weld.py` | 37.a (rank 1, ε=−1) + 11.a control: point-counted coefficients, completed line, pinning, hinge photograph | forced central zero at taper floor; **hinge reverb rate 0.295615 vs (√37/2π)·L′(1) = 0.296239 — 99.79%** (Gross–Zagier as dissipation rate); pinning determines a₃₇ = −1 and reads ε = −1 (ray 0.5000π, spread 4e-7); E1-series references hit LMFDB values to 10 digits |
| `bsd_rank_ladder.py` | ranks 0–3 (11.a, 37.a, 389.a, 5077.a): hinge jet towers, exact double-ended incomplete-Γ kernel vs single-strand fiber | **first live jet = BSD leading datum, agreement 1.00000/1.00000/0.99998/0.99974**; parity jets dead at 1e-16, rank-forced jets at 4e-7/8e-5; a₃₈₉ = +1 read from the line; **antihelix load-bearing at the hinge** — single-strand bank floors at ~1e-2 by N=5077 |
| `dimension_census.py` | per-vanishing dimension d(γ) = jet depth over the rank ladder (hinge + 31 non-central zeros) | **d(γ≠0) = 1 everywhere** (flagged 5077.a pair adjudicated exactly: floors 1e-15/1e-18), **d(0) = rank** — dimensions live at all vanishings, arithmetic deposits extra ones only at the pinned midpoint of the two endings |
| `rank4_weld.py` | rank 4: 234446.a (Elkies), composite conductor 2·117223, general-Weierstrass point count, exact kernel | **agree 0.99999** (c₄ = 689.225 vs 689.233); four dead layers (parity 1e-13, rank 2e-7/1e-4); a₂ = −1 two independent ways (mod-2 nonsingular count + dead-layer test); series produces the three forced zeros AND the reference L⁗(1)/4! = 8.943848 |
| `rank5_weld.py` | rank 5: Brumer–McGuinness curve, prime conductor 19,047,851; hybrid exact kernel (mpmath ≤300 + vectorized Gauss–Laguerre for 26k terms) | **agree 1.00000** (c₅ = 21036.8420 vs 21036.8422); five dead layers (weld 1e-14/1e-12/1e-10, rank 6e-9/4e-6); kernel validated 7.5e-13/term + rank-4 regression 1.000000; series forced zeros L′, L‴/3! at 1e-7; reference L⁽⁵⁾(1)/5! = 30.285687 |
| `satake_variance.py` | the ±4% Satake variability decomposed: split-span residual test, ζ, 16 lines, t ∈ [1000,3000], windowed-projection amplitudes | **structure, not noise: cross-span residual correlation +0.969**; with clean methodology the law holds to ~1% (old ±4% was mostly span/floor method); beneath it a reproducible systematic deficit — all-negative, ≈ −0.9% halving with each k (ln2: −0.90/−0.45/−0.21%), growing slowly with ln p (−0.90 → −1.40% over p=2→37) — the medium's second-order self-interaction (intermod power taken from primaries / log-nonlinearity); NEXT: compute the second-order prediction and falsify against this table |
| `castelnuovo_test.py` | the helix Castelnuovo inequality measured: Frobenius-similitude transport on 30 vanishing classes + 30 random heights, cup norm, k ≤ 4, m = 2,3 | **C_k ≤ 1 for every class — the inequality holds with C = 1 as an identity of the carrier metric** (|v_n| is γ-independent: purity structure is the carrier's, not the vanishings'); dilation eigen-structure clean for m=3 (η 0.23, |λ| 0.92 = taper mass), m=2 shows the known eta-sign artifact (de-modulate!); zeros ≡ random — the open mathematics is completion membership (de Branges territory), not the growth bound |
| `strand_topology.py` | Sam's opposite-topology claim: single-strand hinge error vs bank, χ mod 10009 (n* = 56) vs 5077.a (n* = 11) | **degree statement confirmed**: character error decays 5.7e-4 → 5.2e-7 (hinge-outward strand convergent, degree 1); elliptic saturates at ~0.3 (hinge exists only as the two endings-inward strands); conductor hypothesis refuted (5× bigger n* yet convergent); kernel self-check 5e-12 |

## Phase quantization (the fiber's own clock)

| script | does | established |
|---|---|---|
| `phase_cells.py` | raw phase odometer at vanishings (5 characters) | sign flip = 0.98–0.99π at every vanishing; winding ≈ −π per cell; first vanishing ≈ 0.55π from the hinge |
| `phase_norm.py` | fixed carrier scales vs the phase quanta | no fixed scale (π/3, π/6, …) sharpens the quanta at low heights |
| `s_removal.py` | fluctuation-vs-gap correlation; optimal fixed scale | corr(D, gap) = −0.69…−0.84: S(T) fluctuations are largely gap bookkeeping; fixed scale removes 27–45% |
| `s_running.py` | **the running carrier gauge** θ′(t) = ln(local bank radius) = ½ln(qt/2π) | **99.2–99.5% of S(T) removed — every cell exactly π (sd 0.001–0.002π)**, ζ + 4 characters; the theta clock IS the carrier radius (pure √n exactly in the π/3 unit gauge) |
| `oscillator.py` | fiber as its own harmonic: analytic-signal envelope+phase, even extension across the hinge | **exact quantization: first crossing 0.499–0.500π (quarter cycle from the conjugate-midpoint turning point), cells 0.999–1.000π** — deterministic counting N = ⌊φ/π + ½⌋ |
| `cont_growth.py`, `growth_phase.py` | two hinge constructions (cell-integral fiber; growth-path odometer) | **dead ends, kept for the record**: cell-integral loses vanishing-fidelity; growth-path gauge undefined below qt/2π = 1 |
| `root_hinge.py` | weld-ray pinning: exact Γ-phase gauge + Gauss-sum ground truth (χ₃, χ₅ ord 4, χ₇ ord 6 + conjugates) | **the root number is read from the line phase**: gauged phase constant ≡ arg(ε)/2 mod π to 4 decimals, zero circular spread, conjugates mirrored, oracle concurs; hinge first-cell offset = the same constant (Lean anchor: `HingeKernel.weld_pins_half_phase`) |
| `gl2_helix.py` | the GL(2) helix built literally: per-prime SU(2) rotors (Satake classes), Chebyshev ladder, trace readout | Ramanujan = reality of the clock angle; λ(p^k) = U_k(cos θ_p) exact (2e-15); Euler factor = 1/det(I − M_p x) (1e-16); **all λ(n) rebuilt from angles alone; Δ's zeros located from pure rotor geometry** (9.2224, 13.9075) |
| `gl2_cells.py` | phase-cell law at GL(2): exact-Γ gauged cells for Δ and E11 | **π-quantization survives the doubled winding exactly**: cells 1.0000π (Δ sd < 1e-4, E11 sd 0.0012), pinned ray 0 (ε=+1) at ≤1e-4π — the doubled winding lives entirely in the doubled Γ-gauge |
