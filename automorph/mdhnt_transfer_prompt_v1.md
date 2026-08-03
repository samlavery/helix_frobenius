# MDHNT TRANSFER PROTOCOL — v1.0 (August 2026)

You are participating in a standardized transfer experiment for an unpublished
mathematical framework: Multi-Dimensional Harmonic Number Theory (MDHNT). Your
report will be compared, under identical protocol, against reports from other
models and from human readers. Fill in: MODEL = [____], DATE = [____],
TASK = [A / B / C1 / C2, assigned or chosen].

## MATERIALS
Attached/pasted below this prompt: (1) the methods guide "Multi-Dimensional
Harmonic Number Theory, for Dummies"; (2) optionally, the Level-1 Benchmark
sheet. These are your ONLY sources about the framework — do not search for it
(it is unpublished; you will find nothing genuine). General mathematics from
your training is allowed and expected. If you recognize classical mathematics
inside the framework under nonstandard names, SAY SO explicitly — terminology
mapping is high-value data, not rudeness.

## RULES OF THE REGISTER (non-negotiable)
1. Three registers, never blended: PROVEN (you can write the complete proof),
   COMPUTED (you derived/ran it, precision stated), GUESSED (heuristic, labeled).
2. No flattery, no deference. The documents' claims are targets, not authority.
   "This is wrong / ill-posed / trivial in disguise" is a top-value outcome if
   you can back it.
3. BUILD LOG: record every definition, convention, or formula you needed that
   the materials failed to supply, with the repair you chose. Primary data.
4. Literature facts must be cited precisely enough to check.
5. Nothing you produce is trusted without independent verification. Show
   derivations; make numbers reproducible.

## TASKS — exactly one
**TASK A — AUDIT ("find what we missed").** Read the guide adversarially.
Deliver: (A1) your three strongest objections, each with the specific passage
and what would repair it; (A2) any law in the guide you can strengthen,
generalize, or simplify — with proof; (A3) one connection to established
mathematics the text appears unaware of; (A4) one experiment the framework
should run and (per the text) has not — with pre-registered outcome and failure
condition.

**TASK B — BENCHMARK.** Pick ONE question from the benchmark sheet and deliver
per its grading spec. (If no sheet attached: derive the general k-event
clock-cell residue law from the guide and exhibit one exact invariant it
implies; verify numerically.)

**TASK C — OPEN PROBLEM ATTACK.** Self-contained statements; both verified open
as of August 2026:

- **C1 (Erdős \#377, EGRS 1975).** Let f(n) = Σ 1/p over primes p ≤ n with
  p ∤ C(2n,n). Is there an absolute constant C with f(n) ≤ C for all n?
  [Kummer: p ∤ C(2n,n) ⟺ adding n+n in base p carries nowhere ⟺ every base-p
  digit of n is < p/2.] Known (all EGRS 1975, nothing since): the mean of f
  tends to γ₀ = Σ_{k≥2} (log k)/2^k; f(n) = γ₀ + o(1) for almost all n;
  f(n) ≤ c·loglog n with c < 1.
- **C2 (binary digits of squares — the last two cases).** With s(·) the binary
  digit sum: are there infinitely many ODD n with s(n) = s(n²) = k, for k = 14?
  for k = 15? All other k are settled (explicit infinite families where
  infinitude holds; finiteness proven for k ∈ {9,10,11} — Aloui–Jamet–Kaneko–
  Kopecki–Popoli–Stoll 2022, closing Hare–Laishram–Stoll 2011). Squaring is a
  carry process; an infinitude proof is typically a self-replicating binary
  pattern plus induction.

Attack with the guide's methods where they help and any methods where they do
not — but state which did the work. Acceptable outcomes, ranked: full proof >
partial result with the residual named > sharp reduction to one clean statement
> refutation of a sub-claim > structured failure report with the obstruction
precisely identified. A fake proof is the only failing outcome.

## REPORT FORMAT (fixed)
§1 Task + one-paragraph verdict.
§2 Results, registers labeled.
§3 Derivations/proofs, complete.
§4 Numerics: code inline, parameters, outputs, precision.
§5 Build log, ranked by time cost.
§6 Frank assessment: what the materials taught you, where they lost you, what
   a next edition needs. Do not flatter; your report is experimental data.
§7 Declaration: model, date, materials received, any tool/web use.
