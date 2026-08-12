export const meta = {
  name: 'symr-standing-wave-attack',
  description: 'Attack the Sym^r standing wave: r=2 identification bricks in Lean, the route-(b) channel separator theorem, and the novel Sym^r-pullback weld probe — all adversarially verified',
  phases: [
    { title: 'Recon', detail: 'registration scout + two numerics probes + two Lean bricks in parallel' },
    { title: 'Bricks', detail: 'repair pass + the r=2 registration composition brick' },
    { title: 'Verify', detail: 'adversarial verification of every landed brick' },
    { title: 'Close', detail: 'full tree build + honest synthesis ledger' },
  ],
}

const CTX = `
REPO: /Users/samuellavery/work/helix_frobenius — Lean 4 + Mathlib v4.32.0 (lakefile lean_lib 'RequestProject' globs 'RequestProject.+', so a new file RequestProject/<Name>.lean is picked up automatically; build one module with: lake build RequestProject.<Name>; the tree is cached, ~9000 jobs). Python numerics live in tmp/ (python3, mpmath available).
READ FIRST: /Users/samuellavery/work/helix_frobenius/CLAUDE.md — the ground rules there are non-negotiable.
HARD RULES for this task:
- Unconditional proofs only. If a step needs an unproven input, type it as an explicit named hypothesis of a structure/theorem, or stop and name the gap precisely in the docstring. Never paper over.
- Lean sources are edited ONLY with Write/Edit tools, never via scripts. Concurrent editors exist: re-read any file immediately before editing it.
- Axiom footprint of every declaration must be exactly {propext, Classical.choice, Quot.sound}. No sorry, no axiom, no native_decide. End your file with '#print axioms <FullyQualifiedName>' lines for every named declaration (house pattern).
- Docstrings: NEVER write 'does not assume or prove RH/GRH' or any similar disclaimer. State exactly what is proven, at exactly its strength; for scoped gaps write 'not proven in this file' and nothing broader.
- Do NOT modify existing Lean files; put everything in your ONE new file. If you need a small helper about an existing definition, prove it inside your file.
COMPILED ASSETS you may import (all verified present 2026-07-29; read the actual files for exact signatures before use):
- RequestProject/RankLadderParity.lean (namespace CriticalLinePhasor.RankLadderParity): chebU (house Chebyshev-U recurrence), dualIntegral, chebU_neg, dualIntegral_neg, latticeSum_eq_zero_odd.
- RequestProject/BesselOrderLadder.lean (namespace CriticalLinePhasor.BesselOrderLadder): chebU_cos_sin, cosKernel (order channel: integral over theta in [0,pi] of cos(n*theta)*cexp(-i*z*cos theta) — READ THE FILE for the exact definition), semicircleTransform_eq_orderLadder (semicircle transform of U_r = (cosKernel r z - cosKernel (r+2) z)/2), cosKernel_neg, dualIntegral_semicircle.
- RequestProject/CarrierLatticeWeld.lean (CriticalLinePhasor.CarrierLatticeWeld): strandTheta, matrixTheta, matrixTheta_inv, bankGauss_eq_pow, matrixTheta_eq_pow.
- RequestProject/ZetaPeelSkeleton.lean (CriticalLinePhasor.ZetaPeel): mellin_dilation, moebiusSeq, zetaPeel_hasMellin, zetaPeel_mellin (mellin (theta moebiusSeq g) s = (riemannZeta s)⁻¹ * mellin g s for 1 < s.re given MellinConvergent g s), where 'theta b F x = ∑' n, b n * F((n+1)x)' is CriticalLinePhasor.CarrierTheta.theta.
- RequestProject/RSMaster.lean: rs_master (f : CuspForm 𝒮ℒ k) (hk : 0 ≤ k) {s : ℂ} (hs : 2 < s.re) — the Petersson-weighted Epstein integral equals the Gamma-zeta-completed sum of ‖a_n‖²/(4πn)^(s+k-1) on Re s > 2.
- RequestProject/RSAveragedThetaProfile3D.lean: averagedTheta_inv (θ̄_f(1/t) = t·θ̄_f(t), Petersson-averaged lattice bank), averagedTheta_tail_bound, rsAveragedWeakFEPair (Mathlib WeakFEPair: weight 1, root number 1, constant terms = Petersson mass). Also RequestProject/RSAveragedContinuity.lean.
- RequestProject/CPSWeakProfileCoupling3D.lean (GlobalHelix): WeakBankThetaProfileCoupling3D, rsAveragedProfileCoupling, toWeakFEPair, toWeakFEPair_functional_equation.
- RequestProject/RankUniformReduction.lean (CriticalLinePhasor.RankUniformReduction): RungData, RungData.standingWave, symr_reduction, WeldCoupling, weldCoupling_iff_standingWave.
- RequestProject/ThetaGateInterface.lean (CriticalLinePhasor.GateInterface): TransferGate, transferStrip, TransferGate.fe_of_standingWave.
- RequestProject/SchwarzAxisReality.lean: TransferContinuation.abelContinuation, abelContinuation_conj, AxisReality.fe_of_axisReality, BankThetaProfileCoupling3D.ofAxisReality.
HOUSE LEAN LESSONS (hard-won; do not re-trip):
- conj through tsum: tsum_star; Complex.cpow_conj; HasDerivAt.conj_conj / DifferentiableAt.conj_conj exist in Mathlib.
- cexp arguments are atoms: unify arguments before 'ring'.
- Over ℂ there is no LinearOrder: get a = 0 from 2*a = 0 via linear_combination or mul_eq_zero.
- rw [Equiv.tsum_eq] can time out: give f explicitly and bump maxHeartbeats; 'set_option ... in' goes BEFORE the docstring.
- Summable.tsum_prod' needs per-fiber summability pre-typed at the exact stated type.
- simp [Complex.ext_iff] chokes on conj (z/2): rewrite k/2 as a single real cast first.
- Strong-induction + linear_combination is the proven house pattern for Chebyshev-style recurrences (see chebU_cos_sin in BesselOrderLadder.lean and RankLadderParity.lean).
WORKFLOW: load Lean tools with ToolSearch 'select:mcp__lean-lsp__lean_diagnostic_messages,mcp__lean-lsp__lean_goal,mcp__lean-lsp__lean_multi_attempt,mcp__lean-lsp__lean_local_search,mcp__lean-lsp__lean_leansearch,mcp__lean-lsp__lean_loogle,mcp__lean-lsp__lean_run_code'. Iterate with LSP diagnostics; run 'lake build RequestProject.<YourModule>' only when diagnostics are clean; if lake reports another running instance or a lock, sleep 60s and retry.
`

const BRICK = { type: 'object', properties: {
  file: { type: 'string' }, status: { type: 'string', enum: ['landed', 'partial', 'failed'] },
  theorems: { type: 'array', items: { type: 'string' } },
  remaining_gaps: { type: 'array', items: { type: 'string' } },
  build_clean: { type: 'boolean' }, notes: { type: 'string' } },
  required: ['file', 'status', 'theorems', 'remaining_gaps', 'build_clean', 'notes'] }

const PROBE = { type: 'object', properties: {
  script: { type: 'string' }, verdict: { type: 'string' },
  key_numbers: { type: 'array', items: { type: 'string' } },
  discovery: { type: 'boolean' }, notes: { type: 'string' } },
  required: ['script', 'verdict', 'key_numbers', 'discovery', 'notes'] }

const SCOUTMAP = { type: 'object', properties: {
  available: { type: 'array', items: { type: 'string' } },
  missing: { type: 'array', items: { type: 'string' } },
  feasibility: { type: 'string', enum: ['high', 'medium', 'low'] },
  plan: { type: 'string' } },
  required: ['available', 'missing', 'feasibility', 'plan'] }

const VERDICT = { type: 'object', properties: {
  brick: { type: 'string' }, vacuous: { type: 'boolean' }, circular: { type: 'boolean' },
  axiom_clean: { type: 'boolean' }, overclaims: { type: 'array', items: { type: 'string' } },
  verdict: { type: 'string', enum: ['CONFIRMED', 'NEEDS_FIX', 'REJECTED'] },
  details: { type: 'string' } },
  required: ['brick', 'vacuous', 'circular', 'axiom_clean', 'overclaims', 'verdict', 'details'] }

log('Phase 1: scout + 2 probes + 2 Lean bricks, all independent')
phase('Recon')

// Probes run long; hold their promise and only await at synthesis.
const probesPromise = parallel([
  () => agent(`${CTX}
YOUR TASK — numerics probe A: the detuned-rung separation control (arithmetic-sensitivity of route (b)'s separation step).
Background: the program has proven termwise lattice reality (Im(dual_xi + dual_{-xi}) = 0 on Kloosterman-weighted master-formula terms) and an exact Bessel-order ladder (rank r enters the dual side only through cosine-kernel orders r and r+2). The open bridge is SEPARATION: reality of an aggregate over rungs does not automatically descend to one rung. This probe tests whether separation is arithmetically sensitive (good — a mechanism can exist) or blind (bad — would extend the degree barrier to the seed side).
READ FIRST: tmp/eps_from_parity.py and tmp/eps_from_parity_results.txt (the working master-formula term construction, kill-tests A0/A1/B/D — reuse its machinery), and tmp/rank_ladder_closure.py if present. Known instrument traps recorded there: normalize per-rank by the max over the z-grid, never per-(r,z) by |rhs| (Bessel zeros); aggregate controls use MAX over xi, not min; the nu_J = nu_clock/2 factor-2 trap.
WRITE tmp/detuned_rung_separation.py (python3 + mpmath) implementing, with PRE-REGISTERED pass/fail criteria stated in the script header BEFORE results:
- P1 baseline: build an aggregate over odd rungs r in {1,3,5} of paired (+xi/-xi) dual kernel terms on real master-formula weights (elliptic p=2 channel as in eps_from_parity.py), each rung weighted by its measured epsilon-ladder phase. Verify aggregate pair-reality: max_xi |Im(agg)|/max_xi |agg| <= 1e-10.
- P2 detune: shift ONE rung's channel (replace its U_r by U_{r+1}, i.e. an order-shift inside that rung only). Criterion: the reality violation rises by >= 6 orders of magnitude over P1.
- P3 localization: extract per-order jet coefficients of the aggregate at small argument (the dual kernel of rung r vanishes to order r at z=0; orders r and r+2 form a triangular band). Criterion: the extracted coefficients flag the detuned rung and ONLY that rung (other rungs stay within 1e-6 relative of their P1 values).
- P4 control (must NOT flag): a reality-preserving perturbation — one global unimodular phase applied symmetrically to every +xi/-xi pair — leaves all rungs at baseline.
Save results to tmp/detuned_rung_separation_results.txt. Report measured numbers exactly; if a criterion fails, report the failure at full prominence — a failed P2/P3 is a finding (separation arithmetic-blind), not an error to hide.`,
    { label: 'probe:detuned-separation', phase: 'Recon', schema: PROBE, effort: 'high' }),
  () => agent(`${CTX}
YOUR TASK — numerics probe B: the Sym^r-pullback weld (the novel degree-r coupling candidate for certifier (a)). This is the discovery probe: a rank-uniform candidate mechanism for injecting degree-r Hecke data into a Poisson-self-dual frame.
CONSTRUCTION (test this, exactly): for g in SL_2(R) acting on the upper half plane, let rho_r(g) = Sym^r(g) acting on R^{r+1} in the basis that makes Sym^r of SO(2) orthogonal (basis x^(r-i) y^i scaled by sqrt(binom(r,i))). For z = x + i y in H let g_z be the standard matrix mapping i to z ([[y^(1/2), x y^(-1/2)],[0, y^(-1/2)]]). Define the rank-(r+1) Gram Q_r(z) = rho_r(g_z) rho_r(g_z)^T (det 1 since det g_z = 1 and det rho_r = det^{r(r+1)/2}). KEY FACTS to verify numerically first (instrument validation, report both):
(V1) SL_2(Z)-invariance: for gamma in SL_2(Z), rho_r(gamma) is an integer matrix of det ±1, so the Epstein zeta E_r(z, s) = sum over nonzero v in Z^{r+1} of (v^T Q_r(z) v)^(-s) satisfies E_r(gamma z, s) = E_r(z, s). Check numerically at r=2,3 for gamma = S, T at a few z, s.
(V2) Poisson self-duality of the associated theta in t (Gram det 1) — rank-uniform, classical.
MAIN RUN: define I_r(s) = integral over the standard fundamental domain F of P(z) * E_r(z, s) dmu, with P(z) = y^12 |Delta(z)|^2 (Delta from the q-expansion, precomputed tau(n) for n up to ~50, y-truncation of F at y <= 6 with the exponential decay making the tail negligible; lattice sums truncated by Gaussian/norm radius with verified truncation error).
- r=1 SANITY: I_1 must reproduce the classical Rankin-Selberg unfolding (proportional to the completed sum of |a_n|^2 n^(-s-11) — compare against direct evaluation of that Dirichlet series; ratio constant in s to 1e-6 over >= 5 values of s with Re s in [3, 6]).
- r=2 CALIBRATION: compare I_2(s) against candidate identifications built from known objects: L(Sym^2 Delta, matched arguments) times elementary factors (zeta factors, Gamma factors, and lower rungs). Compute L(Sym^2 Delta, w) from the Satake angles (Euler product over p <= 10000 at Re w >= 2.5). Try ratios I_2(s) / candidate(s) over >= 5 s-values; PRE-REGISTER: an identification counts only if the ratio is constant in s to 1e-5.
- r=3 DISCOVERY: same protocol against candidates assembled from L(Sym^3 Delta), L(Delta), zeta at shifted arguments. If a constant ratio appears — that is a rank-3 integral representation candidate carrying degree-3 Satake data through a quadratic (Poisson) frame: report it as DISCOVERY-GRADE with the exact identification. If no candidate matches, report the measured s-dependence (log-derivative of I_3 vs candidates) — a clean null is also a finding.
Write tmp/symr_pullback_weld.py, results to tmp/symr_pullback_weld_results.txt. Numerical honesty: verify truncation stability (double the lattice radius and the p-cutoff, results must move < 1e-7 relative); report every criterion's measured value. Do not curve-fit identifications post hoc beyond the pre-registered candidate list; list any post-hoc observation separately labeled POST-HOC.`,
    { label: 'probe:symr-pullback-weld', phase: 'Recon', schema: PROBE, effort: 'high' }),
])

// Scout + two independent Lean bricks (disjoint new files).
const [scoutRes, b1, b3] = await parallel([
  () => agent(`${CTX}
YOUR TASK — read-only scout for the r=2 registration composition (no edits anywhere).
Goal: map exactly which compiled lemmas exist for composing: rsAveragedWeakFEPair / averagedTheta_inv (weight-1 FE of the Petersson-averaged profile) + rs_master (its completed-Mellin identification on Re s > 2) + the zeta-peel engine (ZetaPeelSkeleton) into a functional equation for the PEELED (Sym^2-bank) object in the prescribed Gamma-chart.
Inventory precisely (grep/read the repo + search Mathlib with lean_local_search / lean_leansearch / lean_loogle):
1. What RSAveragedThetaProfile3D + RSAveragedContinuity + CPSWeakProfileCoupling3D already prove about the Mellin transform of the averaged profile (entire part, poles, FE via Mathlib WeakFEPair API — list the exact declaration names and signatures, including WeakFEPair.functional_equation / Lambda / residue APIs in Mathlib).
2. What Mathlib has for: riemannZeta functional equation (completedRiemannZeta, riemannZeta_one_sub), Gamma duplication (Complex.Gamma_mul_Gamma_add_half), Mellin machinery (MellinConvergent, mellin_comp_mul_left etc.), and division of WeakFEPair-type FEs by zeta's FE.
3. The exact axis bookkeeping: rs_master lives at axis s -> 1-s in the profile chart with the zeta(2s) factor; the peel target is the Sym^2 completed FE at its own axis. Write out the substitution chain (which shifts, where Gamma-duplication enters) as a concrete plan with the available lemma names at each step, and name what is MISSING (exact statement of any lemma that would have to be proven from scratch).
Return: available (exact names), missing (exact statements), feasibility for a single-session Lean landing of the peeled FE, and a step-by-step plan an implementation agent can follow.`,
    { label: 'scout:registration-algebra', phase: 'Recon', schema: SCOUTMAP }),
  () => agent(`${CTX}
YOUR TASK — Lean brick 1: RequestProject/Sym2CoefficientIdentification.lean (namespace CriticalLinePhasor.Sym2Identification). This closes the LOCAL (prime-power) layer of the r=2 coefficient identification — one of the two named remaining inputs of the r=2 rung.
THE MATH (verify these on paper first; they are classical symmetric-function identities at unit-determinant Satake):
Fix alpha : ℂ, halpha : alpha ≠ 0. Define (zpow for negative exponents):
  seedCoeff alpha k := ∑ i in Finset.range (k+1), alpha ^ ((k : ℤ) - 2*i)        -- trace Sym^k of diag(alpha, alpha⁻¹); U_k
  sym2Coeff alpha k := ∑ a in Finset.range (k+1), ∑ c in Finset.range (k+1-a), alpha ^ (2*((a:ℤ) - c))   -- h_k(alpha², 1, alpha⁻²); trace Sym^k of the Sym²-Satake
TARGETS (all unconditional, exact):
  T0 recurrences: seedCoeff alpha (k+2) = (alpha + alpha⁻¹) * seedCoeff alpha (k+1) - seedCoeff alpha k;  and the 3-variable complete-homogeneous recurrence sym2Coeff alpha (k+3) = e1*(sym2Coeff (k+2)) - e2*(sym2Coeff (k+1)) + sym2Coeff k, where e1 = e2 = alpha^2 + 1 + alpha^(-2) and e3 = 1 (compute and simplify — with these weights e1 = e2). Prove by finite-sum telescoping (the house did this pattern twice: chebU recurrence, chebU_cos_sin).
  T1 (square law): seedCoeff alpha k ^ 2 = sym2Coeff alpha k + sym2Coeff alpha (k-1) for 1 ≤ k, and seedCoeff alpha 0 ^ 2 = sym2Coeff alpha 0. Route: strong induction on k using T0 for both sides + linear_combination (house pattern); base cases k = 0, 1, 2 by direct expansion (field_simp; ring with halpha).
  T2 (the peel + square-redilation form): define peeled alpha k := seedCoeff alpha k ^ 2 - seedCoeff alpha (k-1) ^ 2 for 1 ≤ k, peeled alpha 0 := 1. Prove: sym2Coeff alpha k = ∑ m in Finset.range (k/2 + 1), peeled alpha (k - 2*m). (From T1 by induction: h_k = U_k² - h_(k-1) telescopes to h_k = peeled k + h_(k-2).)
  T3 (interpretation, docstring + wrapper theorem): T2 says exactly — the Sym² local bank coefficients ARE the squares-dilation of the Möbius-peel of the squared seed coefficients, at every prime power, unit-det Satake, identity-class. This is the local layer of the r=2 coefficient identification: the Möbius peel at prime-power level is the first difference (peeled), and the squares-redilation is the m-sum. State a wrapper theorem making the μ/ζ(2s) reading explicit at the level of formal local Dirichlet polynomials if it is clean; otherwise the k-indexed T2 with a precise docstring is the deliverable.
  OPTIONAL T4 (only if the interface is clean): use lean_local_search to find the repo's literal CPS/radial local Euler coefficient function for a rank-3 bank at weights (alpha^2, 1, alpha^(-2)) and identify sym2Coeff with it.
Docstring the file honestly: this file proves the local (prime-power) identification; the global assembly under Hecke multiplicativity and the analytic (Mellin-layer) wiring are not proven in this file.
Iterate to zero diagnostics, then run: lake build RequestProject.Sym2CoefficientIdentification. Report the exact theorem names landed.`,
    { label: 'brick1:sym2-coeff-id', phase: 'Recon', schema: BRICK, effort: 'high' }),
  () => agent(`${CTX}
YOUR TASK — Lean brick 3: RequestProject/ChannelSeparation.lean (namespace CriticalLinePhasor.ChannelSeparation). This converts route (b)'s separation gap from an unnamed obstruction into a compiled theorem plus ONE named input.
THE MATH: the order channels cosKernel n (from BesselOrderLadder — read its exact definition first) vanish at z = 0 to order exactly n, hence finitely many distinct orders are linearly independent, hence rung data is jet-extractable from an aggregate. Chain of targets:
  S0 (orthogonality core): for m < n: ∫ θ in (0)..π, Real.cos (n*θ) * (Real.cos θ)^m = 0. Route: (cos θ)^m expands over cos(j*θ) with j ≤ m via product-to-sum induction (cos A * cos B = (cos(A+B) + cos(A-B))/2 from Real.cos_add/cos_sub), and ∫_0^π cos(n θ) cos(j θ) dθ = 0 for j ≠ n (direct computation via product-to-sum and intervalIntegral.integral_cos; sin(kπ) = 0). Also compute the m = n case: ∫_0^π cos(nθ) (cos θ)^n dθ = π / 2^n for n ≥ 1 (and π for n = 0) — nonzero.
  S1 (series form): cosKernel n z = ∑' m, ((-I*z)^m / m!) * (∫ θ in (0)..π, Real.cos (n*θ) * (Real.cos θ)^m : ℂ) — interchange sum and interval integral (integrand dominated by |z|^m/m! on the compact interval; use the house Fubini/tsum-integral interchange or Mathlib's intervalIntegral tsum interchange with a summable bound). Conclude the vanishing-order statement in whatever form is most tractable — acceptable forms: (a) cosKernel n z = z^n * g n z with g n analytic near 0 and g n 0 ≠ 0; or (b) explicit Taylor-coefficient extraction: the m-th coefficient functional of the series vanishes for m < n and is nonzero at m = n. Choose the form you can compile; do not fight for the strongest.
  S2 (THE SEPARATOR): for a finite s : Finset ℕ and c : ℕ → ℂ, if ∑ n in s, c n * cosKernel n z = 0 for all z in a neighborhood of 0 (or for all z : ℂ — choose the hypothesis you can consume), then ∀ n in s, c n = 0. Proof by strong induction on the minimal order via S1's coefficient extraction.
  S3 (the ladder band form): via semicircleTransform_eq_orderLadder, rung r contributes orders {r, r+2} with leading (order-r) coefficient 1/2 * (its weight): for a finite SAME-PARITY set of rungs, the rung-coefficients-to-aggregate map is triangular with nonzero diagonal, so aggregate vanishing forces every rung coefficient to vanish. State and prove this as the separation theorem for the compiled ladder.
  S4 (the named input, typed): state as a structure or explicit hypothesis-shaped definition what certifier (b) must now supply — aggregate reality with rung-resolved coefficients — and prove the conditional: given that input plus S3, per-rung channel identities follow. This is gap-naming as a type, the house pattern (compare TransferGate).
Docstring honestly: S0-S3 unconditional; S4 is the named remaining input, not proven in this file.
Iterate to zero diagnostics, then: lake build RequestProject.ChannelSeparation. Report exact theorem names.`,
    { label: 'brick3:channel-separation', phase: 'Recon', schema: BRICK, effort: 'high' }),
])

log(`Recon done: brick1=${b1 ? b1.status : 'null'}, brick3=${b3 ? b3.status : 'null'}, scout feasibility=${scoutRes ? scoutRes.feasibility : 'null'}`)

phase('Bricks')
// Repair pass for any brick that wrote a file but is not build-clean.
async function repair(b, moduleName) {
  if (!b || b.status === 'failed' || b.build_clean) return b
  const fixed = await agent(`${CTX}
YOUR TASK — repair the Lean file ${b.file} until it compiles cleanly (module ${moduleName}).
Current state per its author: status=${b.status}; notes: ${b.notes}; remaining gaps: ${JSON.stringify(b.remaining_gaps)}.
Constraints: no sorry, no axiom, axiom footprint exactly {propext, Classical.choice, Quot.sound}; you may WEAKEN a theorem statement to what is provable (and adjust the docstring to exact strength) but never fake it; keep '#print axioms' lines current. Iterate with lean-lsp diagnostics; finish with: lake build ${moduleName} (retry on lake lock after sleep 60).`,
    { label: `repair:${moduleName}`, phase: 'Bricks', schema: BRICK, agentType: 'lean4:proof-repair', effort: 'high' })
  return fixed || b
}
let b1f = await repair(b1, 'RequestProject.Sym2CoefficientIdentification')
let b3f = await repair(b3, 'RequestProject.ChannelSeparation')

// Brick 2 depends on brick 1 names + scout map.
let b2f = null
if (b1f && b1f.status !== 'failed' && scoutRes) {
  b2f = await agent(`${CTX}
YOUR TASK — Lean brick 2: RequestProject/Sym2RegistrationLanding.lean (namespace CriticalLinePhasor.Sym2Registration). Compose the compiled r=2 assets toward the r=2 standing wave (the prescribed-chart FE of the Sym^2 bank) — land the MAXIMAL unconditional composition; a partial landing with the remainder named exactly (as ONE typed hypothesis or clearly-stated missing lemma) is a valid and expected outcome.
SCOUT MAP (from a read-only survey of the repo + Mathlib — verify each name before use):
available: ${JSON.stringify(scoutRes.available)}
missing (per scout): ${JSON.stringify(scoutRes.missing)}
plan: ${scoutRes.plan}
BRICK 1 (already landed, import it): file ${b1f.file}, theorems: ${JSON.stringify(b1f.theorems)} — the local (prime-power) identification: sym2Coeff = squares-redilation of the peel of the squared seed coefficients.
COMPOSITION TARGET, in order of value (stop at the furthest unconditional point):
1. Identify the Mellin transform of the Möbius-dilated averaged profile: apply ZetaPeel.zetaPeel_mellin to the averaged profile θ̄_f (its MellinConvergent hypothesis comes from the compiled tail bound averagedTheta_tail_bound / RSAveragedContinuity — check what is compiled) on 1 < Re s: mellin(theta moebiusSeq θ̄_f) s = ζ(s)⁻¹ · mellin(θ̄_f) s.
2. Combine with rs_master (Re s > 2 identification of mellin θ̄_f with the completed ‖a_n‖² series) to get the peeled object's initial-domain identification — the ζ-peeled Rankin square, i.e. the Sym²-bank readout modulo the ζ(2s) redilation, whose local coefficient law is brick 1.
3. FE transport: from the WeakFEPair FE of the unpeeled object (rsAveragedWeakFEPair via Mathlib's WeakFEPair.functional_equation) and Mathlib's riemannZeta FE, derive the reflected identity for the peeled object — the registration algebra (axis shifts + Gamma-duplication where needed, per the scout plan).
4. If (3) fully lands: state the r=2 standing-wave/FE theorem in a form consumable by the reduction layer (RankUniformReduction.RungData / WeldCoupling shapes, or BankThetaProfileCoupling3D.ofAxisReality inputs) — read those signatures and match if clean.
At each step: if an input is genuinely missing, TYPE it (one named hypothesis, exact statement) and continue conditionally within a structure, or stop and record it — per ground rule 1 the named gap is the honest output. Do not claim the standing wave landed unless every input is discharged.
Docstring: exact strength; 'not proven in this file' for the remainder; no disclaimers.
Iterate to zero diagnostics; finish with: lake build RequestProject.Sym2RegistrationLanding (retry on lock).`,
    { label: 'brick2:sym2-registration', phase: 'Bricks', schema: BRICK, effort: 'high' })
  b2f = await repair(b2f, 'RequestProject.Sym2RegistrationLanding')
}

phase('Verify')
// Adversarial verification of every landed/partial brick.
const bricks = [
  { b: b1f, name: 'Sym2CoefficientIdentification' },
  { b: b3f, name: 'ChannelSeparation' },
  { b: b2f, name: 'Sym2RegistrationLanding' },
].filter(x => x.b && x.b.status !== 'failed')

const verdicts = await parallel(bricks.map(({ b, name }) => () => agent(`${CTX}
YOUR TASK — ADVERSARIAL verification of the new Lean brick ${b.file} (read-only on all files except none — you edit nothing; report only). The author claims: status=${b.status}, theorems=${JSON.stringify(b.theorems)}, gaps=${JSON.stringify(b.remaining_gaps)}, notes=${b.notes}.
Your job is to REFUTE it. Checks, all mandatory:
1. VACUITY: read every theorem statement. Could it be satisfied degenerately (empty Finset, zero function, trivial instance)? Instantiate suspicious cases with mcp__lean-lsp__lean_run_code (e.g. prove the statement's hypothesis is UNsatisfiable, or that a zero/degenerate witness inhabits a structure) — the house has been burned by DC-mode vacuity before (a strong coupling type was uninhabitable on genuine data; a wired instance was vacuous-for-nonzero-f). Any structure introduced must be shown non-degenerately inhabitable or explicitly flagged.
2. CIRCULARITY: does any hypothesis smuggle the conclusion? For the r=2 bricks: SEED Hecke multiplicativity / classical zeta facts are admissible typed inputs; anything equivalent to Sym^2 automorphy, the Sym^2 FE itself, or the standing wave being certified is NOT. Trace each hypothesis to its source.
3. AXIOMS: run mcp__lean-lsp__lean_verify (or lake env + #print axioms via lean_run_code) on every declared theorem; footprint must be exactly {propext, Classical.choice, Quot.sound}; confirm no sorry/axiom in the source.
4. CLAIM CALIBRATION: compare the docstrings and the author's claimed theorem list against the literal statements — flag every overclaim (including any 'RH/GRH' disclaimer language, which is banned) and any claim of 'standing wave landed' not backed by a fully discharged statement.
5. MATH SPOT-CHECK: verify the central identity numerically (lean_run_code with #eval on rationalized instances, or quick python via Bash) at 2-3 concrete parameter values.
Default to skepticism: if uncertain on any check, verdict NEEDS_FIX with the exact issue. CONFIRMED only if all five checks pass.`,
  { label: `verify:${name}`, phase: 'Verify', schema: VERDICT, effort: 'high' })))

// One fix pass for NEEDS_FIX verdicts.
const fixed = []
for (let i = 0; i < bricks.length; i++) {
  const v = verdicts[i]
  if (v && v.verdict === 'NEEDS_FIX') {
    const fx = await agent(`${CTX}
YOUR TASK — fix the Lean brick ${bricks[i].b.file} per an adversarial review, then rebuild.
Review findings: ${v.details}. Overclaims to correct: ${JSON.stringify(v.overclaims)}. Vacuity flagged: ${v.vacuous}. Circularity flagged: ${v.circular}.
Rules: weaken statements/docstrings to exact provable strength rather than deleting content; if a structure was flagged vacuous, add a non-degenerate inhabitation lemma or re-type it; no sorry/axiom; keep #print axioms lines; finish with lake build of the module (retry on lock).`,
      { label: `fix:${bricks[i].name}`, phase: 'Verify', schema: BRICK, effort: 'high' })
    fixed.push({ name: bricks[i].name, result: fx })
  }
}

phase('Close')
const buildRes = await agent(`Repo: /Users/samuellavery/work/helix_frobenius. Run a full 'lake build' (retry once after sleep 60 on lock). Report: did it finish green; if not, list exactly which modules fail and the first error of each. Also grep the new files RequestProject/Sym2CoefficientIdentification.lean, RequestProject/ChannelSeparation.lean, RequestProject/Sym2RegistrationLanding.lean (those that exist) for 'sorry' and 'axiom ' and report counts (must be zero). Return a concise factual report.`,
  { label: 'full-build-audit', phase: 'Close', effort: 'low' })

const probes = await probesPromise

const ledger = await agent(`You are writing the honest results ledger of a multi-agent proof campaign on the repo /Users/samuellavery/work/helix_frobenius (the Sym^r standing-wave program). Calibration rule of the house: claims must equal exactly the proof's strength — under- and over-claiming are both lies; falsified pre-registered criteria are published at the same prominence as confirmations.
RAW RESULTS (verbatim structured outputs of the agents):
- Brick 1 (r=2 local coefficient identification): ${JSON.stringify(b1f)}
- Brick 3 (channel separator): ${JSON.stringify(b3f)}
- Brick 2 (r=2 registration composition): ${JSON.stringify(b2f)}
- Adversarial verdicts: ${JSON.stringify(verdicts)}
- Post-review fixes: ${JSON.stringify(fixed)}
- Full build audit: ${JSON.stringify(buildRes)}
- Probe A (detuned-rung separation control): ${JSON.stringify(probes && probes[0])}
- Probe B (Sym^r-pullback weld, the novel degree-r coupling candidate): ${JSON.stringify(probes && probes[1])}
Cross-check what you can cheaply (read the new files' theorem statements yourself before trusting the claimed lists; the files are in RequestProject/). Then write the ledger in markdown:
1. PROVEN (Lean, build-clean, verified): each theorem with file and one-line content; note the adversarial verdict.
2. MEASURED (probes): pre-registered criteria vs measured outcomes; flag any DISCOVERY-grade or falsification-grade result at full prominence.
3. THE REMAINING GAP, restated exactly as of now: what the standing wave still needs per rung after this campaign — named inputs only, no vagueness.
4. CORRECTIONS: anything an agent claimed that verification rejected or weakened.
Be terse and exact. This ledger goes to the project owner who knows the mathematics deeply.`,
  { label: 'synthesis-ledger', phase: 'Close' })

return { ledger, bricks: { b1: b1f, b2: b2f, b3: b3f }, verdicts, probes, build: buildRes }