import Mathlib

/-!
# Erdős problem 377: central-binomial nondivisors as carry-free rails

The target unfolds to the following plain finite statement.  For each `n`, retain each prime
`p ≤ n` exactly when `p ∤ (2n).choose n`, attach weight `1 / p`, and ask whether the total weight
is bounded by one real constant independent of `n`.

Kummer's theorem turns the retention test into an exact clock ledger.  At level `i`, the carry bit
is one precisely when `p^i ≤ 2 * (n % p^i)`.  Thus a retained prime is a rail whose carry ledger is
zero at every level through `Nat.log p (2 * n) + 1`.

Search audit used before construction:

```
rg -n -i "erdos.?377|erdős.?377|balanced.?prime|balanced.?rail|no.?carry|carry.?free|central.?binom|prime.*not.*dvd.*choose|not.*divid.*binom" . --glob '*.lean' --glob '*.md' --glob '*.tex' --glob '*.py'
rg -n -i "balanced.?prime|balanced.?rail|no.?carry|carry.?free|central.?binom|prime.*not.*dvd.*choose|not.*divid.*binom|kummer" .lake/packages/mathlib/Mathlib --glob '*.lean'
rg -n "padicValNat|factorization.*choose|choose.*factorization|Nat\\.choose|Nat\\.digits|ofDigits|digitsAppend|sumPrimeReciprocals" .lake/packages/mathlib/Mathlib --glob '*.lean'
rg -n "factorization.*eq_zero.*not_dvd|not_dvd.*factorization|factorization_eq_zero_iff|dvd_iff.*factorization" .lake/packages/mathlib/Mathlib --glob '*.lean'
rg -n "fieldMarkers_drift_zero|structure .*Rail|def .*Rail|Adapter|adapter|drift_zero|bounded.*rail|rail.*bounded|weighted.*ledger|ledger.*bound|MultiRail" RequestProject --glob '*.lean'
rg -n "sum_fiberwise|sum_image.*filter|log_eq_one_iff|mod_add_div|one_le.*div|div_lt_iff" .lake/packages/mathlib/Mathlib --glob '*.lean'
rg -n "UniformRailContraction|uniform.*rail.*contract|depthBand_harmonic|primeHarmonicMass|carryFree_carryCutoff|railBand" . RequestProject --glob '*.lean' --glob '*.md' --glob '*.tex' --glob '*.py'
rg -n -i "tendsto.*pow.*zero.*lt_one|pow.*tendsto.*zero|exists.*pow.*lt|geom.*decay|norm.*lt_one.*pow" .lake/packages/mathlib/Mathlib --glob '*.lean'
rg -n "log_pow|log_eq.*pow|Nat\\.log.*pow|pow_lt_pow|Prime.*eq_two_or_odd|prime.*lt.*three|prime.*le.*three" .lake/packages/mathlib/Mathlib/Data/Nat .lake/packages/mathlib/Mathlib/NumberTheory --glob '*.lean'
rg -n "pow_le_pow_iff_(left|right)|pow_le_pow_left" .lake/packages/mathlib/Mathlib --glob '*.lean'
rg -n "Prime.*two_le|prime.*eq_two.*lt|eq_two_of_prime|Prime.*not_lt" .lake/packages/mathlib/Mathlib --glob '*.lean'
rg -n -i "mod_pow_succ|mod.*pow.*add|mod_add_div.*pow|digits.*get|digit.*mod|div_pow.*mod|mod_mul.*div" .lake/packages/mathlib/Mathlib/Data/Nat .lake/packages/mathlib/Mathlib --glob '*.lean'
rg -n "harmonizedRail|harmonized.*coordinate|closedCell|railDigit|p \\* Real.pi / 3|pi / 3" RequestProject . --glob '*.lean' --glob '*.md' --glob '*.tex' --glob '*.py'
rg -n "mod_mul_(left|right)_div|mod.*mul.*div_self|mod_eq.*mod.*add" .lake/packages/mathlib/Mathlib/Data/Nat --glob '*.lean'
rg -n -i "channelAverage|channel_average|channelDiscrepancy|channel_discrepancy|dynamicHarmonicDiscrepancy|two_thirds|2 / 3.*energy|transfer.*gate" RequestProject . --glob '*.lean' --glob '*.md' --glob '*.tex' --glob '*.py'
rg -n "sum_filter|prod_eq_one|card_filter|filter_range|sum_ite|div_le_iff₀|Nat.*div.*two|add_sub_of_le" .lake/packages/mathlib/Mathlib --glob '*.lean'
rg -n -i "triangularPrimitive|triangular_wave|squareSign|square_wave|quotientWarp|warpDensity|warpAmplitude|fixedQuotientPhase|contour.*warp" RequestProject . --glob '*.lean' --glob '*.md' --glob '*.tex' --glob '*.py'
rg -n "HasDerivAt.*(if|ite)|\.if.*HasDerivAt|congr_of_eventuallyEq.*HasDerivAt|eventually.*lt.*nhds|hasDerivAt_const.*div|hasDerivAt_div" .lake/packages/mathlib/Mathlib/Analysis --glob '*.lean'
rg -n -i "sum.*prime.*(recip|inverse)|prime.*harmonic|reciprocal.*prime|Mertens.*prime|sum.*1 /.*prime|prime.*interval" RequestProject . --glob '*.lean' --glob '*.md' --glob '*.tex'
rg -n -i "sum.*prime.*(recip|inverse)|prime.*harmonic|reciprocal.*prime|Mertens.*prime|sum.*1 /.*prime|prime.*interval" .lake/packages/mathlib/Mathlib --glob '*.lean'
rg -n -i "Var_warped|warped.*variation|variation.*warp|Sigma.*n.*r|boundedVariation|BoundedVariation|VariationOn|eVariationOn|Stieltjes|intervalIntegrable.*deriv|summation.*parts|Abel.*summation" RequestProject . --glob '*.lean' --glob '*.md' --glob '*.tex' --glob '*.py'
rg -n -i "BoundedVariation|VariationOn|eVariationOn|Jordan.*variation|Stieltjes|RiemannStieltjes|summationByParts|sum_by_parts|Abel.*summation|partial.*summation" .lake/packages/mathlib/Mathlib --glob '*.lean'
rg -n "abs_sub.*sum|sum.*abs.*sub|Monotone.*variation|variation.*monotone|sum_range.*sub.*telescop|sum.*sub.*range" .lake/packages/mathlib/Mathlib --glob '*.lean'
rg -n "eVariationOn.*(Monotone|Antitone)|MonotoneOn.*eVariationOn|AntitoneOn.*eVariationOn" .lake/packages/mathlib/Mathlib --glob '*.lean'
rg -n "def .*Variation|meshVariation|totalVariation|sum_range_by_parts" RequestProject . --glob '*.lean'
rg -n "sum_range_by_parts" .lake/packages/mathlib/Mathlib --glob '*.lean'
rg -n "not_summable.*(inv|one_div)|harmonic.*not.*summable|summable.*nat.*inv|notSummable|tendsto.*harmonic|harmonic.*atTop|sum_range.*one_div" .lake/packages/mathlib/Mathlib --glob '*.lean'
rg -n -i "primeContourDiscrepancy|prime.*packet.*discrep|Mertens.*reciprocal|sumPrimeReciprocals|primeHarmonic.*interval|prime.*partial.*summation|Chebyshev.*theta|vonMangoldt.*partial" RequestProject . --glob '*.lean' --glob '*.md' --glob '*.tex' --glob '*.py'
rg -n -i "sum.*prime.*recip|prime.*recip.*sum|Mertens|Chebyshev.*theta|vonMangoldt.*sum|primeCounting|Nat\\.primeCounting|PrimeCounting|prime.*interval" .lake/packages/mathlib/Mathlib --glob '*.lean'
rg -n "theta.*isAsymptotic|primeCounting.*isAsymptotic|primeNumberTheorem|tendsto.*theta.*div|theta_div.*tendsto|psi.*isAsymptotic" .lake/packages/mathlib/Mathlib/NumberTheory --glob '*.lean'
rg -n "sum_Ico.*prime|sum_filter.*Prime|sum_primesLE|primesLE.*sum|sum.*primesLE" .lake/packages/mathlib/Mathlib/NumberTheory --glob '*.lean'
rg -n "add_mul_div_(left|right)|add_mul_div|mul_add_div|div_add_div_same|add_div_of_dvd|Even.*add_one|even_add_one|not_even.*add_one|even_add|two_mul.*Even" .lake/packages/mathlib/Mathlib --glob '*.lean'
rg -n "div_eq_one_iff|div_eq_of_lt_le|div_eq_iff.*mul_le|le_div_iff_mul_le|div_lt_iff_lt_mul" .lake/packages/mathlib/Mathlib --glob '*.lean'
rg -n -i "mellinClock|mellin.*carrier|normalizedBankPrime|harmonic.*normaliz|logarithmic.*carrier|terminalMellin|mellin.*drift|log.*rail.*coordinate" RequestProject . --glob '*.lean' --glob '*.md' --glob '*.tex' --glob '*.py'
rg -n -i "mellin|logarithmic.*coordinate|harmonic.*normaliz|normalized.*cumulative|prime.*harmonic.*normaliz" .lake/packages/mathlib/Mathlib --glob '*.lean'
rg -n "log_lt_iff|log_lt_sub|sub_pos.*log|log_pow|Real\.log_pow|strictMono.*log|log_lt_iff_lt_exp|log_mul|log_natCast|Nat\.cast_pow" .lake/packages/mathlib/Mathlib/Analysis .lake/packages/mathlib/Mathlib/NumberTheory --glob '*.lean'
rg -n "three_pow_dynamicSurvivalWeight_eq_one|three_pow_carryFree|dynamicSquareSign.*three|dynamicClosureWeight.*three|DynamicClosedOrbit.*three" RequestProject/Erdos377CarryRails.lean
rg -n -i "AtomicRailBudget|IsHarmonicAtomicRailBand|harmonicAtomicDepthBand|atomic.*budget|concentrat.*harmonic|harmonic.*atom|terminalMellinDrift|root.*threshold|boundary.*mass" RequestProject . --glob '*.lean' --glob '*.md' --glob '*.tex' --glob '*.py'
rg -n -i "sum.*log.*prime|prime.*log.*sum|prime.*reciprocal|harmonic.*finset|sum_le.*card|exists.*sum.*le|Finset.*max|sup.*Finset|card.*average|pigeonhole" .lake/packages/mathlib/Mathlib --glob '*.lean'
rg -n "(:|→) Erdos377Bound|Erdos377Bound :=|AtomicRailBudget|harmonicAtomicDepthBand" . --glob '*.lean'
lean_leansearch "finite sum over natural r of r times (1/2)^r is at most 2"
lean_leanfinder "summability and exact sum of n multiplied by a geometric sequence x^n when |x| < 1"
rg -n -i "dynamicBankEnergy.*succ.*le|terminal.*preterminal|preterminal|closure.*energy.*monot|energy.*monot|stop.*recurrence|range.*sub.*one" RequestProject . --glob '*.lean'
rg -n -i "sum_le_sum.*mul_le_mul|Finset.*sum.*monotone|Antitone.*sum|Nat.*sub_add_cancel|range.*pred|range.*sub_one" .lake/packages/mathlib/Mathlib --glob '*.lean'
rg -n "dynamicClosureWeight_succ_le|dynamicBankEnergy_eq_vanishingDwell|dynamicBankEnergy_harmonicDiffuse_terminal_eq_mass|harmonicDiffuse_nonterminal_dwell" RequestProject/Erdos377CarryRails.lean
lean_leansearch "a finite weighted sum is monotone if every summand is monotone"
lean_leanfinder "rewrite positive natural r as r minus one plus one and unroll a recurrence to the predecessor"
rg -n -i "preterminalEntrance|entrance.*uniform|dynamicBankEnergy.*railBand.*zero|sum.*occupiedDepths.*dynamicBankEnergy|primeHarmonicMass.*railBand|prime.*reciprocal.*band|Mertens|Chebyshev|Abel|partial.*summation|summation.*parts|dyadic.*prime" RequestProject . --glob '*.lean' --glob '*.md' --glob '*.tex'
rg -n -i "sum.*primesLE.*(1|inv|recip)|primesLE.*sum|primeCounting|pi_le|theta_le|AbelSummation|sum_by_parts|summationByParts|partialSummation|dyadic|Ioc.*Prime|filter.*Prime.*sum" .lake/packages/mathlib/Mathlib/NumberTheory .lake/packages/mathlib/Mathlib/Algebra/BigOperators .lake/packages/mathlib/Mathlib/Analysis --glob '*.lean'
rg -n -i "sum.*log.*p.*\\/.*p|sum.*log.*prime.*div|log.*div.*prime|theta.*div|vonMangoldt.*div|sum.*vonMangoldt.*\\/|mangoldt.*reciprocal|log.*prime.*reciprocal|primeReciprocal" .lake/packages/mathlib/Mathlib/NumberTheory --glob '*.lean'
rg -n "integral.*(log.*log|one_div.*log|inv.*log)|HasDerivAt.*log.*log|hasDerivAt_log.*div|integral.*rpow|integral.*pow.*neg|integral_inv|integral.*sqrt" .lake/packages/mathlib/Mathlib/Analysis --glob '*.lean'
rg -n "primeCounting.*le.*self|primeCounting_le|card_primesLE_le|primesLE.*card.*le|floor.*le.*self|natFloor_le" .lake/packages/mathlib/Mathlib/NumberTheory .lake/packages/mathlib/Mathlib/Data/Real --glob '*.lean'
rg -n "integral_inv|integral_one_div|integral.*log.*sub|log.*sub.*integral" .lake/packages/mathlib/Mathlib --glob '*.lean'
rg -n "def.*root|floorRoot|nthRoot|root.*pow|pow.*root" .lake/packages/mathlib/Mathlib/Data/Nat .lake/packages/mathlib/Mathlib/NumberTheory --glob '*.lean'
rg -n -i "sameRailBand_mellin|same.*rail.*log|crossed.*power.*log|preterminalEntrance_uniform|entrance.*uniform|railBand.*uniform|primeHarmonicMass.*railBand.*le|Mellin.*window" RequestProject . --glob '*.lean' --glob '*.md' --glob '*.tex'
rg -n "strictMonoOn_log|log_pow|log_mul|log_div|integral_inv_div_log|integral_rpow|pi_le_log4_mul_div|sqrt.*div.*pow|rpow.*neg.*three|sum_le_tsum.*one_div|tsum.*one_div.*pow" .lake/packages/mathlib/Mathlib/Analysis .lake/packages/mathlib/Mathlib/NumberTheory --glob '*.lean'
rg -n "log_le_sqrt|log.*le.*sqrt|sqrt.*ge.*log|log_div_sqrt|abs_log_mul_self_rpow_lt|log_le_sub_one_of_pos|log_lt_sub_one_of_pos" .lake/packages/mathlib/Mathlib/Analysis --glob '*.lean'
rg -n "min'_mem|max'_mem|min'_le|max'_ge|sum_erase_add|erase_subset|mem_erase|card_filter_le" .lake/packages/mathlib/Mathlib/Data/Finset --glob '*.lean'
rg -n "tsum_geometric|hasSum_geometric|summable_geometric|sum_le_tsum" .lake/packages/mathlib/Mathlib/Topology/Algebra/InfiniteSum .lake/packages/mathlib/Mathlib/Analysis --glob '*.lean'
lean_leansearch "upper bound sum of reciprocals of primes in an interval using the prime counting function"
lean_leanfinder "Mertens upper bound for sum of reciprocal primes between x and y or partial summation with prime counting"
lean_leansearch "If positive real powers satisfy q^r < p^(r+1), then r * log q < (r+1) * log p"
lean_leanfinder "bound the sum of reciprocal primes in a logarithmic interval by Abel summation and integrate 1/(t log t), with a square-root tail"
rg -n "def reciprocalCell(Low|Mid|High)|def reciprocalCellSecondDifference|def bankPrimeReciprocalCumulative|def dynamicPrefixPrimeBank|def normalizedBankPrimeCarrier|def mellinCellGradientAdapter|theorem .*SecondDifference|theorem .*Cumulative|theorem .*dynamicPrefixPrimeBank" RequestProject/Erdos377CarryRails.lean
rg -n -i "secondDifference.*variation|variation.*secondDifference|abs.*secondDifference|sum.*abs.*second|monotone.*cumulative|cumulative.*variation|totalVariation.*step|sum.*abs.*diff|bounded.*variation" RequestProject . --glob '*.lean'
rg -n -i "secondDifference.*variation|variation.*secondDifference|abs.*secondDifference|sum.*abs.*second|monotone.*cumulative|cumulative.*variation|totalVariation.*step|sum.*abs.*diff|bounded.*variation" .lake/packages/mathlib/Mathlib --glob '*.lean'
rg -n "(:|→) Erdos377Bound|Erdos377Bound :=|theorem .*Erdos377|axiom.*377|preterminalMellinVariation|PreterminalMellin|uniform.*Variation|Variation.*uniform|exists.*∀ n.*recursiveMellin" . --glob '*.lean'
rg -n "recursiveMellinCurvatureVariation|recursiveMellinAdapterVariation|preterminalMellinVariation|Erdos377Bound" .lake/packages/mathlib/Mathlib --glob '*.lean'
lean_leansearch "sum of absolute second differences of a monotone finite sequence is bounded by twice its total variation"
lean_leanfinder "finite sum absolute adjacent differences bounded for monotone function or cumulative distribution total variation"
rg -n "recursiveWarpedInteriorVariation.*dynamicBankEnergy|dynamicBankEnergy.*recursiveWarpedInteriorVariation|preterminalWarpedSamplingQuantization|preterminalWarpedVariation.*uniform|sampling.*quantization.*uniform|abs.*reciprocalCellSecondDifference" RequestProject . --glob '*.lean'
rg -n "abs_sub_le|abs_sub_comm|sum_fiberwise_of_maps_to|sum_filter_add_sum_filter_not|abs.*sum.*filter|sum.*abs.*sub" .lake/packages/mathlib/Mathlib --glob '*.lean'
lean_leansearch "absolute value of difference of two nonnegative finite sums is at most their sum"
lean_leansearch "finite sum over fibers equals sum over original finite set"
lean_loogle "abs (?a - ?b) ≤ ?a + ?b"
rg -n -i "preterminalHarmonicAtomicWarpedSamplingQuantizationVariation|preterminalHarmonicDiffuseWarpedSamplingQuantizationVariation|atomic.*sampling.*quantization.*uniform|diffuse.*sampling.*quantization.*uniform|stopping.*time|first.*carry|failure.*bank|survival.*kernel|swap.*sum.*prime|sum.*dynamicClosureWeight" RequestProject . --glob '*.lean' --glob '*.md' --glob '*.tex'
rg -n -i "stopping.*time|first.*failure|first.*hit|sum_comm|sum_product|sum_bij|sum_fiberwise|geometric.*sum|indicator.*monotone|filter.*sdiff" .lake/packages/mathlib/Mathlib --glob '*.lean'
lean_leansearch "swap two nested finite sums and collect a pointwise geometric stopping time kernel"
lean_leanfinder "finite decreasing boolean sequence represented by disjoint first failure layers and terminal survivors"
rg -n "Finset.sum_comm" .lake/packages/mathlib/Mathlib --glob '*.lean'
rg -n "occupiedDepths|sum_occupiedDepths|union.*railBand|railBand.*pairwise|sum.*railBand|mem_railBand|railDepth.*occupied|primesLE.*railBand|biUnion.*railBand" RequestProject/Erdos377CarryRails.lean
rg -n "union_sdiff_of_subset|union_sdiff|sdiff_union|subset.*sdiff.*union|filter.*sdiff" .lake/packages/mathlib/Mathlib/Data/Finset --glob '*.lean'
rg -n "theorem (sdiff_disjoint|disjoint_sdiff)" .lake/packages/mathlib/Mathlib/Data/Finset --glob '*.lean'
rg -n "def DynamicClosedOrbit|theorem .*DynamicClosedOrbit|dynamicClosedOrbit|railBand_dynamicClosureWeight_eq_ite|railBand_dynamicSquareSign_terminal" RequestProject/Erdos377CarryRails.lean
rg -n -i "compensatedFullyMellinLedger|compensated.*Mellin.*Ledger|FullyMellin.*compensat|terminalSignedFullyMellinRootLedger|preterminalSignedFullyMellinLedger|half_entrance_add_half_compensated|uniform.*compensat|compensat.*uniform|firstFailure|first_failure|failureLayer|failure_layer|stoppingKernel|stopping_kernel" RequestProject . --glob '*.lean' --glob '*.md' --glob '*.tex'
rg -n -i "compensatedFullyMellinLedger|compensated.*Mellin.*Ledger|terminalSignedFullyMellinRootLedger|preterminalSignedFullyMellinLedger|uniform.*compensat|compensat.*uniform|firstFailure|first_failure|failureLayer|failure_layer|stoppingKernel|stopping_kernel" .lake/packages/mathlib/Mathlib --glob '*.lean'
rg -n "∃ (K|C|A|D) : ℝ, ∀ n : ℕ|∃ (K|C|A|D) : ℝ, ∀ n" RequestProject/Erdos377CarryRails.lean
rg -n "compensatedFullyMellinLedger.*≤|≤.*compensatedFullyMellinLedger|terminalSignedFullyMellinRootLedger.*≤|preterminalSignedFullyMellinLedger.*≤" RequestProject . --glob '*.lean'
lean_local_search "compensatedFullyMellinLedger uniform bounded"
lean_leansearch "A finite signed sum is bounded above after telescoping first failure layers of a decreasing Boolean sequence"
lean_leanfinder "finite decreasing zero-one sequence decomposed into disjoint first failure times with telescoping weighted sum"
rg -n "dynamicSurvivalWeight.*(anti|mono|le)|survivalWeight.*(anti|mono|le)|dynamicClosureWeight.*(anti|mono|le)|closureWeight.*(anti|mono|le)|DynamicClosedOrbit.*(mono|anti)" RequestProject/Erdos377CarryRails.lean
lean_leansearch "The product of zero-one gates over range a is at least the product over range b when a ≤ b"
lean_loogle "Finset.prod_le_prod_of_subset"
rg -n -i "primeHaar|HaarPrime|logWeightedPrime|primeLogHarmonic|mellinPrimeWeight|harmonicAmplitude|one_div_log.*prime|log.*p.*\/.*p" RequestProject . --glob '*.lean' --glob '*.md' --glob '*.tex'
rg -n -i "primeHaar|HaarPrime|logWeightedPrime|primeLogHarmonic|mellinPrimeWeight|harmonicAmplitude|one_div_log.*prime|log.*p.*\/.*p" .lake/packages/mathlib/Mathlib --glob '*.lean'
lean_leansearch "For a real x greater than one, (log x / x) * (1 / log x) = 1 / x"
lean_leanfinder "factor reciprocal 1/x as logarithmic Haar weight log(x)/x times Mellin amplitude 1/log(x)"
rg -n "hasDerivAt_inv_log|deriv_inv_log|strictAnti.*inv_log|antitone.*inv_log|inv_log.*antitone|integral_inv_div_log_sq" .lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Log --glob '*.lean'
rg -n "orderIsoOfFin|orderIso.*Finset|sort.*Finset|Finset.*orderIso|monotone.*enum|Finset\.orderIso|attach.*sort" .lake/packages/mathlib/Mathlib/Data/Finset .lake/packages/mathlib/Mathlib/Order --glob '*.lean'
rg -n "sortedPrime|primeMesh|orderIsoOfFin|Finset.*sort" RequestProject --glob '*.lean'
lean_leansearch "Enumerate a finite set of natural numbers in strictly increasing order as a function Fin s.card to natural numbers"
lean_leanfinder "sorted enumeration of a finite set under a linear order with range equal to the finset"
rg -n "HarmonicAtomicRailBudget|HarmonicDiffuseRailContractionAt|UniformHarmonicDiffuseRailBandEnvelope|erdos377Bound_of_harmonicAtomic_diffuse_uniform_band" . --glob '*.lean'
rg -n "HarmonicAtomicRailBudget|HarmonicDiffuseRailContractionAt|UniformHarmonicDiffuseRailBandEnvelope|erdos377Bound_of_harmonicAtomic_diffuse_uniform_band" .lake/packages/mathlib/Mathlib --glob '*.lean'
lean_local_search "erdos377Bound"
lean_local_search "HarmonicAtomicRailBudget"
lean_leansearch "A finite family of positive weighted disjoint fibers whose total mass is dominated by r times one atom has uniformly bounded sum over r"
lean_leanfinder "Bound a sum over logarithmic depth bands by choosing one dominating atom in each band and charging it injectively to the underlying finite set"
lean_leansearch "Prime reciprocal sum over primes in a logarithmic interval is bounded by an absolute constant"
lean_leanfinder "Chebyshev theta partial summation upper bound for sum of reciprocal primes in an interval"
```

Two compiler-level decompositions of the Kummer step are included:

1. start with `rw [Nat.factorization_choose' hp hb]`, then characterize a zero-cardinality filter;
2. start with `rw [hp.dvd_iff_one_le_factorization hcne]`, then characterize a positive-cardinality
   filter by an explicit witness.
-/

open Finset

namespace CriticalLinePhasor.Erdos377

/-- The carry test at level `i` when doubling `n` in base `p`. -/
def carryAt (p n i : ℕ) : Prop := p ^ i ≤ 2 * (n % p ^ i)

/-- The finite carry ledger through cutoff `b`. -/
noncomputable def carryLedger (p n b : ℕ) : Finset ℕ := by
  classical
  exact (Ico 1 b).filter (carryAt p n)

/-- A rail is balanced through `b` when its carry ledger is identically zero. -/
def CarryFreeThrough (p n b : ℕ) : Prop := ∀ i ∈ Ico 1 b, 2 * (n % p ^ i) < p ^ i

/-- The canonical cutoff containing every possible carry in the central binomial coefficient. -/
def carryCutoff (p n : ℕ) : ℕ := Nat.log p (2 * n) + 1

/-- The unqualified balanced-rail predicate used by Erdős problem 377. -/
def CarryFree (p n : ℕ) : Prop := CarryFreeThrough p n (carryCutoff p n)

/-- Kummer specialized to the central binomial coefficient: its valuation is the carry count. -/
theorem centralBinom_factorization_eq_carryLedger_card {p n b : ℕ} (hp : p.Prime)
    (hb : Nat.log p (2 * n) < b) :
    ((2 * n).choose n).factorization p = (carryLedger p n b).card := by
  simpa only [two_mul, carryLedger, carryAt] using
    Nat.factorization_choose' (n := n) (k := n) hp (by simpa [two_mul] using hb)

/-- First decomposition: a prime is absent exactly when every carry test vanishes. -/
theorem prime_not_dvd_centralBinom_iff_carryFreeThrough {p n b : ℕ} (hp : p.Prime)
    (hb : Nat.log p (2 * n) < b) :
    ¬p ∣ (2 * n).choose n ↔ CarryFreeThrough p n b := by
  have hcne : (2 * n).choose n ≠ 0 := (Nat.choose_pos (by omega)).ne'
  have hzero : ((2 * n).choose n).factorization p = 0 ↔ ¬p ∣ (2 * n).choose n := by
    simp [Nat.factorization_eq_zero_iff, hp, hcne]
  rw [← hzero, centralBinom_factorization_eq_carryLedger_card hp hb]
  simp only [card_eq_zero, carryLedger, filter_eq_empty_iff, CarryFreeThrough, mem_Ico,
    carryAt, not_le, and_imp]

/-- Second decomposition: divisibility is witnessed by a concrete carry level. -/
theorem prime_dvd_centralBinom_iff_exists_carry {p n b : ℕ} (hp : p.Prime)
    (hb : Nat.log p (2 * n) < b) :
    p ∣ (2 * n).choose n ↔ ∃ i ∈ Ico 1 b, carryAt p n i := by
  classical
  have hcne : (2 * n).choose n ≠ 0 := (Nat.choose_pos (by omega)).ne'
  rw [hp.dvd_iff_one_le_factorization hcne,
    centralBinom_factorization_eq_carryLedger_card hp hb, Finset.one_le_card,
    carryLedger, Finset.filter_nonempty_iff]

/-- Canonical-cutoff form of the carry-free characterization. -/
theorem prime_not_dvd_centralBinom_iff_carryFree {p n : ℕ} (hp : p.Prime) :
    ¬p ∣ (2 * n).choose n ↔ CarryFree p n := by
  exact prime_not_dvd_centralBinom_iff_carryFreeThrough hp (Nat.lt_add_one _)

/-- Prime rails retained by the original divisibility formulation. -/
def nondivisorPrimes (n : ℕ) : Finset ℕ :=
  n.primesLE.filter fun p ↦ ¬p ∣ (2 * n).choose n

/-- The same prime rails selected intrinsically by their zero carry ledgers. -/
noncomputable def carryFreePrimes (n : ℕ) : Finset ℕ :=
  by
    classical
    exact n.primesLE.filter fun p ↦ CarryFree p n

/-- The two selection procedures give exactly the same bank of rails. -/
theorem nondivisorPrimes_eq_carryFreePrimes (n : ℕ) :
    nondivisorPrimes n = carryFreePrimes n := by
  ext p
  simp only [nondivisorPrimes, carryFreePrimes, mem_filter, and_congr_right_iff]
  intro hp
  exact prime_not_dvd_centralBinom_iff_carryFree (Nat.prime_of_mem_primesLE hp)

/-- Erdős's weighted prime ledger. -/
noncomputable def erdos377Mass (n : ℕ) : ℝ :=
  ∑ p ∈ nondivisorPrimes n, (1 : ℝ) / (p : ℝ)

/-- Exact MDHNT readout: the original mass is the sum over zero-carry rails. -/
theorem erdos377Mass_eq_carryFreeRailSum (n : ℕ) :
    erdos377Mass n = ∑ p ∈ carryFreePrimes n, (1 : ℝ) / (p : ℝ) := by
  rw [erdos377Mass, nondivisorPrimes_eq_carryFreePrimes]

/-- The unchanged target, now expressed entirely in the carrier's carry-ledger coordinates. -/
def Erdos377Bound : Prop := ∃ C : ℝ, ∀ n : ℕ, erdos377Mass n ≤ C

/-! ## The geometric carrier and its lossless adapter -/

/-- The doubled prefix, normalized to one `p^i`-cell.  A carry is exactly a crossing of phase one. -/
noncomputable def railPhase (p n i : ℕ) : ℝ :=
  (2 * (n % p ^ i) : ℕ) / (p ^ i : ℕ)

/-- Carrier-native closure: every prefix phase remains strictly inside its unit cell. -/
def GeometricCarryFreeThrough (p n b : ℕ) : Prop :=
  ∀ i ∈ Ico 1 b, railPhase p n i < 1

/-- Carrier-native closure at the canonical Kummer cutoff. -/
def GeometricCarryFree (p n : ℕ) : Prop :=
  GeometricCarryFreeThrough p n (carryCutoff p n)

/-- A carry bit is precisely a crossing of the unit-cell boundary in carrier coordinates. -/
theorem carryAt_iff_one_le_railPhase {p n i : ℕ} (hp : 0 < p) :
    carryAt p n i ↔ 1 ≤ railPhase p n i := by
  have hpow : (0 : ℝ) < (p ^ i : ℕ) := by positivity
  rw [carryAt, railPhase, le_div_iff₀ hpow]
  norm_num
  norm_cast

/-- The phase chart preserves the zero-ledger predicate exactly. -/
theorem carryFreeThrough_iff_geometric {p n b : ℕ} (hp : 0 < p) :
    CarryFreeThrough p n b ↔ GeometricCarryFreeThrough p n b := by
  simp only [CarryFreeThrough, GeometricCarryFreeThrough]
  apply forall_congr'
  intro i
  apply imp_congr_right
  intro _
  simpa only [carryAt, not_le] using
    not_congr (carryAt_iff_one_le_railPhase (n := n) (i := i) hp)

/-- Canonical form of the lossless phase adapter. -/
theorem carryFree_iff_geometric {p n : ℕ} (hp : 0 < p) :
    CarryFree p n ↔ GeometricCarryFree p n := by
  exact carryFreeThrough_iff_geometric hp

/-- Prime rails selected after transport into the geometric phase chart. -/
noncomputable def geometricCarryFreePrimes (n : ℕ) : Finset ℕ := by
  classical
  exact n.primesLE.filter fun p ↦ GeometricCarryFree p n

/-- The Kummer selector and the geometric cell selector are the same multi-rail bank. -/
theorem carryFreePrimes_eq_geometricCarryFreePrimes (n : ℕ) :
    carryFreePrimes n = geometricCarryFreePrimes n := by
  ext p
  simp only [carryFreePrimes, geometricCarryFreePrimes, mem_filter, and_congr_right_iff]
  intro hp
  exact carryFree_iff_geometric (Nat.prime_of_mem_primesLE hp).pos

/-- The weighted readout of the carrier-native zero-defect rails. -/
noncomputable def geometricRailMass (n : ℕ) : ℝ :=
  ∑ p ∈ geometricCarryFreePrimes n, (1 : ℝ) / (p : ℝ)

/-- Exact export adapter: the carrier-native mass reads out as Erdős's original sum. -/
theorem erdos377Mass_eq_geometricRailMass (n : ℕ) :
    erdos377Mass n = geometricRailMass n := by
  rw [erdos377Mass_eq_carryFreeRailSum, geometricRailMass,
    carryFreePrimes_eq_geometricCarryFreePrimes]

/-! ## Depth geometry and the first reciprocal band -/

/-- The rail depth is the number of nonzero base-`p` clock levels below `n`. -/
def railDepth (p n : ℕ) : ℕ := Nat.log p n

/-- The zero-defect rails at one fixed depth. -/
noncomputable def depthBand (n k : ℕ) : Finset ℕ := by
  classical
  exact (carryFreePrimes n).filter fun p ↦ railDepth p n = k

/-- The finite set of occupied rail depths. -/
noncomputable def occupiedDepths (n : ℕ) : Finset ℕ := by
  classical
  exact (carryFreePrimes n).image fun p ↦ railDepth p n

/-- Every occupied prime rail has at least one active logarithmic cell. -/
theorem occupiedDepth_pos {n r : ℕ} (hr : r ∈ occupiedDepths n) : 0 < r := by
  classical
  rw [occupiedDepths] at hr
  rcases mem_image.mp hr with ⟨p, hp, rfl⟩
  have hpLE : p ∈ n.primesLE := (mem_filter.mp hp).1
  have hpPrime : p.Prime := Nat.prime_of_mem_primesLE hpLE
  simpa [railDepth] using
    Nat.log_pos hpPrime.one_lt (Nat.le_of_mem_primesLE hpLE)

/-- Exact multi-rail decomposition: the total readout is the sum of its depth fibers. -/
theorem erdos377Mass_eq_sum_depthBands (n : ℕ) :
    erdos377Mass n =
      ∑ k ∈ occupiedDepths n, ∑ p ∈ depthBand n k, (1 : ℝ) / (p : ℝ) := by
  rw [erdos377Mass_eq_carryFreeRailSum]
  exact (Finset.sum_fiberwise_of_maps_to
    (t := occupiedDepths n)
    (g := fun p ↦ railDepth p n)
    (fun p hp ↦ Finset.mem_image_of_mem (fun q ↦ railDepth q n) hp)
    (fun p ↦ (1 : ℝ) / (p : ℝ))).symm

/-- A depth-one closed rail lies above `√(2n)` and closes in its first residue cell. -/
theorem geometric_depth_one_iff {p n : ℕ} (hp : p.Prime) :
    CarryFree p n ∧ railDepth p n = 1 ↔
      p ≤ n ∧ 2 * n < p ^ 2 ∧ 2 * (n % p) < p := by
  constructor
  · rintro ⟨hfree, hdepth⟩
    have hlog := (Nat.log_eq_one_iff.mp hdepth)
    have hnp2 : n < p ^ 2 := by simpa [pow_two] using hlog.1
    have hp_le_n : p ≤ n := hlog.2.2
    have hfirst : 2 * (n % p) < p := by
      have hp_le_two_n : p ≤ 2 * n := hp_le_n.trans (by omega)
      have hlog_ge : 1 ≤ Nat.log p (2 * n) :=
        Nat.le_log_of_pow_le hp.one_lt (by simpa using hp_le_two_n)
      simpa using hfree 1 (by
        simp only [carryCutoff, mem_Ico]
        omega)
    have htwo : 2 * n < p ^ 2 := by
      by_contra h
      have hp2_le : p ^ 2 ≤ 2 * n := Nat.le_of_not_gt h
      have hlog2 : 2 ≤ Nat.log p (2 * n) := Nat.le_log_of_pow_le hp.one_lt hp2_le
      have hsecond := hfree 2 (by
        simp only [carryCutoff, mem_Ico]
        omega)
      rw [Nat.mod_eq_of_lt hnp2] at hsecond
      omega
    exact ⟨hp_le_n, htwo, hfirst⟩
  · rintro ⟨hp_le_n, htwo, hfirst⟩
    have hnp2 : n < p ^ 2 := lt_of_le_of_lt (by omega) htwo
    have hdepth : railDepth p n = 1 := by
      exact Nat.log_eq_of_pow_le_of_lt_pow (by simpa using hp_le_n) (by simpa using hnp2)
    refine ⟨?_, hdepth⟩
    intro i hi
    simp only [carryCutoff, mem_Ico] at hi
    have hlog2 : Nat.log p (2 * n) = 1 := by
      exact Nat.log_eq_of_pow_le_of_lt_pow
        (by simpa using hp_le_n.trans (by omega)) (by simpa using htwo)
    rw [hlog2] at hi
    have hi1 : i = 1 := by omega
    simpa [hi1] using hfirst

/-- Quotient-coordinate form of the first-cell closure interval. -/
theorem first_cell_iff_reciprocal_interval {p n : ℕ} :
    2 * (n % p) < p ↔ 2 * n < (2 * (n / p) + 1) * p := by
  have hsplit := Nat.mod_add_div n p
  constructor <;> intro h <;> nlinarith

/-! ## Logarithmic/Mellin conversion and the finite harmonic transfer -/

/-- The global Mellin height `T = log n`. -/
noncomputable def mellinHeight (n : ℕ) : ℝ := Real.log n

/-- The prime-rail Mellin coordinate `u = log p`. -/
noncomputable def primeMellinCoordinate (p : ℕ) : ℝ := Real.log p

/-- The normalized rail frequency `x = log p / log n`. -/
noncomputable def normalizedRailFrequency (p n : ℕ) : ℝ :=
  primeMellinCoordinate p / mellinHeight n

/-- The harmonic coordinate is exact: `p = n^x`. -/
theorem rpow_normalizedRailFrequency {p n : ℕ} (hp : 0 < p) (hn : 1 < n) :
    (n : ℝ) ^ normalizedRailFrequency p n = p := by
  have hnpos : (0 : ℝ) < n := by positivity
  have hlogn : Real.log (n : ℝ) ≠ 0 := ne_of_gt (Real.log_pos (by exact_mod_cast hn))
  rw [normalizedRailFrequency, primeMellinCoordinate, mellinHeight,
    Real.rpow_def_of_pos hnpos]
  rw [mul_div_cancel₀ _ hlogn, Real.exp_log]
  positivity

/-- The hard lower-half-cell cutoff on the finite cyclic clock `ℤ/qℤ`. -/
noncomputable def halfCellIndicator (q : ℕ) (a : ZMod q) : ℂ :=
  if 2 * a.val < q then 1 else 0

/-- The normalized discrete Fourier coefficient of the half-cell cutoff. -/
noncomputable def halfCellFourierCoeff (q : ℕ) [NeZero q] (m : ZMod q) : ℂ :=
  (q : ℂ)⁻¹ * ZMod.dft (halfCellIndicator q) m

/-- Exact finite Fourier inversion of one hard carry cell. -/
theorem halfCell_fourier_expansion (q : ℕ) [NeZero q] (a : ZMod q) :
    halfCellIndicator q a =
      ∑ m : ZMod q, ZMod.stdAddChar (m * a) * halfCellFourierCoeff q m := by
  have hinv := congrFun (ZMod.dft.symm_apply_apply (halfCellIndicator q)) a
  rw [ZMod.invDFT_apply] at hinv
  rw [← hinv]
  simp only [smul_eq_mul, halfCellFourierCoeff, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m _
  ring

/-- The nonzero modes are the coherent part left after removing the cell average. -/
noncomputable def halfCellNonzeroModes (q : ℕ) [NeZero q] (a : ZMod q) : ℂ :=
  ∑ m ∈ (Finset.univ.erase 0 : Finset (ZMod q)),
    ZMod.stdAddChar (m * a) * halfCellFourierCoeff q m

/-- Exact zeroth-mode/nonzero-mode split for one carry cell. -/
theorem halfCell_eq_zeroMode_add_nonzeroModes (q : ℕ) [NeZero q] (a : ZMod q) :
    halfCellIndicator q a =
      halfCellFourierCoeff q 0 + halfCellNonzeroModes q a := by
  rw [halfCell_fourier_expansion]
  let f : ZMod q → ℂ := fun m ↦
    ZMod.stdAddChar (m * a) * halfCellFourierCoeff q m
  calc
    ∑ m, f m = (∑ m ∈ (Finset.univ.erase 0 : Finset (ZMod q)), f m) + f 0 := by
      simpa only using
        (Finset.sum_erase_add (Finset.univ : Finset (ZMod q)) f (Finset.mem_univ 0)).symm
    _ = halfCellFourierCoeff q 0 + halfCellNonzeroModes q a := by
      simp [f, halfCellNonzeroModes, add_comm]

/-- The `i`-th nested carry cell, before Fourier conversion. -/
noncomputable def prefixCellFactor (p n i : ℕ) : ℂ :=
  halfCellIndicator (p ^ i) (n : ZMod (p ^ i))

/-- The full finite carry selector as a product over nested harmonic cells. -/
noncomputable def carryAcceptance (p n : ℕ) : ℂ :=
  ∏ i ∈ Ico 1 (carryCutoff p n), prefixCellFactor p n i

/-- The finite-prefix predicate has a classical decision procedure for the exact selector. -/
noncomputable instance carryFreeDecidable (p n : ℕ) : Decidable (CarryFree p n) :=
  Classical.propDecidable _

/-- The product selector is exactly the Boolean zero-carry rail predicate. -/
theorem carryAcceptance_eq_ite (p n : ℕ) :
    carryAcceptance p n = if CarryFree p n then 1 else 0 := by
  classical
  simp only [carryAcceptance, prefixCellFactor, halfCellIndicator, ZMod.val_natCast,
    Finset.prod_boole, CarryFree, CarryFreeThrough]
  split_ifs <;> rfl

/-- One nested cell after exact finite Fourier conversion. -/
noncomputable def harmonicCellExpansion (p n i : ℕ) : ℂ :=
  if h : p ^ i = 0 then 0 else
    letI : NeZero (p ^ i) := ⟨h⟩
    ∑ m : ZMod (p ^ i),
      ZMod.stdAddChar (m * (n : ZMod (p ^ i))) * halfCellFourierCoeff (p ^ i) m

/-- The Fourier-expanded cell is exactly the original hard cell. -/
theorem harmonicCellExpansion_eq_prefixCellFactor {p n i : ℕ} (hp : 0 < p) :
    harmonicCellExpansion p n i = prefixCellFactor p n i := by
  letI : NeZero (p ^ i) := ⟨pow_ne_zero i hp.ne'⟩
  rw [harmonicCellExpansion, dif_neg (pow_ne_zero i hp.ne')]
  exact (halfCell_fourier_expansion (p ^ i) (n : ZMod (p ^ i))).symm

/-- The per-prime harmonic transfer operator across all nested digit scales. -/
noncomputable def harmonicRailTransfer (p n : ℕ) : ℂ :=
  ∏ i ∈ Ico 1 (carryCutoff p n), harmonicCellExpansion p n i

/-- The harmonic transfer is a lossless conversion of the carry selector. -/
theorem harmonicRailTransfer_eq_carryAcceptance {p n : ℕ} (hp : 0 < p) :
    harmonicRailTransfer p n = carryAcceptance p n := by
  apply Finset.prod_congr rfl
  intro i _
  exact harmonicCellExpansion_eq_prefixCellFactor hp

/-! ## The `π/3` harmonized dynamic cell operator

The user-indexed cell `x_{j+1} = (n % p^(j+1)) / p^j` is represented below with zero-based
index `j`.  It always lies in `[0,p)`, so multiplication by `π/3` places every depth on the
same circumference `pπ/3`.

Two compiler-level decompositions of the digit recurrence were checked:

1. start with `Nat.mod_mul_right_mod` and `Nat.mod_mul_right_div_self`, then reconstruct with
   `Nat.mod_add_div`;
2. start with `Nat.getD_digits`, identify the new digit, and reconstruct with `Nat.ofDigits`.

The first route is exact and avoids a list-valued intermediate.
-/

/-- The carrier unit used by the harmonized cells. -/
noncomputable def harmonizedUnit : ℝ := Real.pi / 3

/-- Every depth attached to prime `p` uses this same circumference. -/
noncomputable def harmonizedCircumference (p : ℕ) : ℝ := (p : ℝ) * harmonizedUnit

/-- The `j`-th base-`p` digit of `n`. -/
def railDigit (p n j : ℕ) : ℕ := n / p ^ j % p

/-- Zero-based form of the normalized coordinate `x_{j+1}`. -/
noncomputable def normalizedCellCoordinate (p n j : ℕ) : ℝ :=
  ((n % p ^ (j + 1) : ℕ) : ℝ) / ((p ^ j : ℕ) : ℝ)

/-- Angular form of the normalized coordinate on the `pπ/3` carrier. -/
noncomputable def harmonizedCellPhase (p n j : ℕ) : ℝ :=
  harmonizedUnit * normalizedCellCoordinate p n j

/-- Exact prefix reconstruction when one new base-`p` digit is exposed. -/
theorem mod_pow_succ_eq_mod_add_digit_mul_pow (p n j : ℕ) :
    n % p ^ (j + 1) = n % p ^ j + railDigit p n j * p ^ j := by
  rw [pow_succ]
  calc
    n % (p ^ j * p) = n % (p ^ j * p) % p ^ j +
        p ^ j * (n % (p ^ j * p) / p ^ j) := (Nat.mod_add_div _ _).symm
    _ = n % p ^ j + p ^ j * railDigit p n j := by
      rw [Nat.mod_mul_right_mod, Nat.mod_mul_right_div_self]
      rfl
    _ = n % p ^ j + railDigit p n j * p ^ j := by ac_rfl

/-- Every normalized depth cell lies on the same half-open carrier `[0,p)`. -/
theorem normalizedCellCoordinate_mem_carrier {p n j : ℕ} (hp : 0 < p) :
    0 ≤ normalizedCellCoordinate p n j ∧ normalizedCellCoordinate p n j < p := by
  have hpowNat : 0 < p ^ j := pow_pos hp j
  have hpow : (0 : ℝ) < ((p ^ j : ℕ) : ℝ) := by exact_mod_cast hpowNat
  have hmod := Nat.mod_lt n (pow_pos hp (j + 1))
  constructor
  · rw [normalizedCellCoordinate]
    positivity
  · rw [normalizedCellCoordinate, div_lt_iff₀ hpow]
    have hmodR : ((n % p ^ (j + 1) : ℕ) : ℝ) < ((p ^ (j + 1) : ℕ) : ℝ) := by
      exact_mod_cast hmod
    simpa [pow_succ, mul_comm] using hmodR

/-- The angular cell lies on `[0,pπ/3)`, independently of depth. -/
theorem harmonizedCellPhase_mem_carrier {p n j : ℕ} (hp : 0 < p) :
    0 ≤ harmonizedCellPhase p n j ∧
      harmonizedCellPhase p n j < harmonizedCircumference p := by
  have hunit : 0 < harmonizedUnit := by
    rw [harmonizedUnit]
    positivity
  have hx := normalizedCellCoordinate_mem_carrier (n := n) (j := j) hp
  constructor
  · exact mul_nonneg hunit.le hx.1
  · rw [harmonizedCellPhase, harmonizedCircumference]
    calc
      harmonizedUnit * normalizedCellCoordinate p n j < harmonizedUnit * p :=
        mul_lt_mul_of_pos_left hx.2 hunit
      _ = (p : ℝ) * harmonizedUnit := by ring

/-- Exact affine contraction between successive normalized cells. -/
theorem normalizedCellCoordinate_succ {p n j : ℕ} (hp : 0 < p) :
    normalizedCellCoordinate p n (j + 1) =
      railDigit p n (j + 1) + normalizedCellCoordinate p n j / p := by
  have hdecomp := mod_pow_succ_eq_mod_add_digit_mul_pow p n (j + 1)
  have hdecompR :
      ((n % p ^ (j + 1 + 1) : ℕ) : ℝ) =
        (n % p ^ (j + 1) : ℕ) + railDigit p n (j + 1) * (p ^ (j + 1) : ℕ) := by
    exact_mod_cast hdecomp
  rw [normalizedCellCoordinate, normalizedCellCoordinate, hdecompR]
  push_cast
  rw [pow_succ]
  field_simp [hp.ne']
  ring

/-- Angular form of the exact dynamic transition `θ ↦ θ/p + (π/3)a`. -/
theorem harmonizedCellPhase_succ {p n j : ℕ} (hp : 0 < p) :
    harmonizedCellPhase p n (j + 1) =
      harmonizedUnit * railDigit p n (j + 1) + harmonizedCellPhase p n j / p := by
  rw [harmonizedCellPhase, normalizedCellCoordinate_succ hp, harmonizedCellPhase]
  ring

/-!
The independent one-step potential is the lower-half gate averaged over all digit channels.  Two
decompositions are tested below:

1. `rw [← sum_filter]`: count the channels satisfying the normalized half-cell inequality;
2. `ring_nf`: split the actual gate into its channel average plus its centered discrepancy.
-/

/-- One normalized affine channel of the dynamic cell operator. -/
noncomputable def normalizedCellStep (p a : ℕ) (x : ℝ) : ℝ := (a : ℝ) + x / p

/-- Lower-half gate in normalized coordinates, independent of the `π/3` readout unit. -/
noncomputable def normalizedLowerHalfGate (p : ℕ) (x : ℝ) : ℝ :=
  if x < (p : ℝ) / 2 then 1 else 0

/-- On a previously closed cell, precisely the lower digit channels remain closed. -/
theorem normalizedCellStep_lt_half_iff {p a : ℕ} {x : ℝ} (hp : 1 < p)
    (hx0 : 0 ≤ x) (hxhalf : x < (p : ℝ) / 2) :
    normalizedCellStep p a x < (p : ℝ) / 2 ↔ a ≤ (p - 1) / 2 := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by omega)
  rw [normalizedCellStep]
  constructor
  · intro hstep
    have hxdiv : 0 ≤ x / (p : ℝ) := div_nonneg hx0 hpR.le
    have haR : 2 * (a : ℝ) < p := by nlinarith
    have ha : 2 * a < p := by exact_mod_cast haR
    omega
  · intro ha
    have ha2 : 2 * a + 1 ≤ p := by omega
    have ha2R : 2 * (a : ℝ) + 1 ≤ p := by exact_mod_cast ha2
    have hxdiv : x / (p : ℝ) < 1 / 2 := by
      rw [div_lt_iff₀ hpR]
      nlinarith
    nlinarith

/-- The finite transfer operator applied to the lower-half potential. -/
noncomputable def normalizedChannelAverage (p : ℕ) (x : ℝ) : ℝ :=
  (1 : ℝ) / p * ∑ a ∈ range p, normalizedLowerHalfGate p (normalizedCellStep p a x)

/-- Exact channel count: a closed input has `(p+1)/2` surviving digit channels. -/
theorem normalizedChannelGate_sum {p : ℕ} {x : ℝ} (hp : 1 < p)
    (hx0 : 0 ≤ x) (hxhalf : x < (p : ℝ) / 2) :
    ∑ a ∈ range p, normalizedLowerHalfGate p (normalizedCellStep p a x) =
      (((p + 1) / 2 : ℕ) : ℝ) := by
  have hfilter :
      (range p).filter (fun a ↦ a ≤ (p - 1) / 2) = range ((p - 1) / 2 + 1) := by
    ext a
    simp only [mem_filter, mem_range]
    omega
  calc
    ∑ a ∈ range p, normalizedLowerHalfGate p (normalizedCellStep p a x) =
        ∑ a ∈ range p, if a ≤ (p - 1) / 2 then (1 : ℝ) else 0 := by
          apply sum_congr rfl
          intro a _
          rw [normalizedLowerHalfGate]
          by_cases ha : a ≤ (p - 1) / 2
          · have hstep := (normalizedCellStep_lt_half_iff hp hx0 hxhalf).mpr ha
            simp [ha, hstep]
          · have hstep : ¬normalizedCellStep p a x < (p : ℝ) / 2 :=
              fun h ↦ ha ((normalizedCellStep_lt_half_iff hp hx0 hxhalf).mp h)
            simp [ha, hstep]
    _ = ∑ a ∈ (range p).filter (fun a ↦ a ≤ (p - 1) / 2), (1 : ℝ) := by
          rw [sum_filter]
    _ = (((p + 1) / 2 : ℕ) : ℝ) := by
          have hhalf : (p - 1) / 2 + 1 = (p + 1) / 2 := by omega
          rw [hfilter]
          simp [hhalf]

/-- Closed-cell value of the finite channel transfer. -/
theorem normalizedChannelAverage_eq {p : ℕ} {x : ℝ} (hp : 1 < p)
    (hx0 : 0 ≤ x) (hxhalf : x < (p : ℝ) / 2) :
    normalizedChannelAverage p x = (((p + 1) / 2 : ℕ) : ℝ) / p := by
  rw [normalizedChannelAverage, normalizedChannelGate_sum hp hx0 hxhalf]
  ring

/-- The independent channel operator contracts the lower-half potential by at most `2/3`. -/
theorem normalizedChannelAverage_le_two_thirds {p : ℕ} {x : ℝ} (hp : 1 < p)
    (hx0 : 0 ≤ x) (hxhalf : x < (p : ℝ) / 2) :
    normalizedChannelAverage p x ≤ (2 : ℝ) / 3 := by
  rw [normalizedChannelAverage_eq hp hx0 hxhalf]
  have hcount : 3 * ((p + 1) / 2) ≤ 2 * p := by omega
  have hcountR : (3 : ℝ) * (((p + 1) / 2 : ℕ) : ℝ) ≤ 2 * p := by
    exact_mod_cast hcount
  have hpR : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by omega)
  rw [div_le_iff₀ hpR]
  nlinarith

/-- Centered error of the actual digit channel relative to the independent channel average. -/
noncomputable def normalizedChannelDiscrepancy (p a : ℕ) (x : ℝ) : ℝ :=
  normalizedLowerHalfGate p (normalizedCellStep p a x) - normalizedChannelAverage p x

/-- Every actual gate is exactly its independent channel average plus its centered error. -/
theorem normalizedGate_eq_average_add_discrepancy (p a : ℕ) (x : ℝ) :
    normalizedLowerHalfGate p (normalizedCellStep p a x) =
      normalizedChannelAverage p x + normalizedChannelDiscrepancy p a x := by
  rw [normalizedChannelDiscrepancy]
  ring

/-- The channel discrepancy is exactly centered over all `p` digit channels. -/
theorem normalizedChannelDiscrepancy_sum_eq_zero {p : ℕ} (hp : 0 < p) (x : ℝ) :
    ∑ a ∈ range p, normalizedChannelDiscrepancy p a x = 0 := by
  simp_rw [normalizedChannelDiscrepancy]
  rw [sum_sub_distrib]
  simp only [sum_const, card_range, nsmul_eq_mul]
  rw [normalizedChannelAverage]
  have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne'
  field_simp [hpR]
  ring

/-- The coherent base-three zero channel exactly pays the missing `1/3` discrepancy. -/
theorem normalizedChannelDiscrepancy_three_zero :
    normalizedChannelDiscrepancy 3 0 0 = (1 : ℝ) / 3 := by
  have havg : normalizedChannelAverage 3 0 = (2 : ℝ) / 3 := by
    simpa using normalizedChannelAverage_eq (p := 3) (x := 0)
      (by norm_num) (by norm_num) (by norm_num)
  rw [normalizedChannelDiscrepancy, havg]
  norm_num [normalizedLowerHalfGate, normalizedCellStep]

/-- The angular and normalized half-cell comparisons agree exactly. -/
theorem harmonizedCellPhase_lt_half_iff_normalized (p n j : ℕ) :
    harmonizedCellPhase p n j < harmonizedCircumference p / 2 ↔
      normalizedCellCoordinate p n j < (p : ℝ) / 2 := by
  have hunit : 0 < harmonizedUnit := by
    rw [harmonizedUnit]
    positivity
  rw [harmonizedCellPhase, harmonizedCircumference]
  constructor
  · intro hphase
    by_contra hx
    have hmul := mul_le_mul_of_nonneg_left (le_of_not_gt hx) hunit.le
    nlinarith
  · intro hx
    have hmul := mul_lt_mul_of_pos_left hx hunit
    nlinarith

/-- Indicator of the lower half of the harmonized carrier. -/
noncomputable def lowerHalfCellGate (p : ℕ) (phase : ℝ) : ℝ :=
  if phase < harmonizedCircumference p / 2 then 1 else 0

/-- Lossless adapter between normalized and angular gate indicators. -/
theorem lowerHalfCellGate_harmonized_eq_normalized (p : ℕ) (x : ℝ) :
    lowerHalfCellGate p (harmonizedUnit * x) = normalizedLowerHalfGate p x := by
  rw [lowerHalfCellGate, normalizedLowerHalfGate, harmonizedCircumference]
  have hunit : 0 < harmonizedUnit := by
    rw [harmonizedUnit]
    positivity
  have hiff : harmonizedUnit * x < (p : ℝ) * harmonizedUnit / 2 ↔ x < (p : ℝ) / 2 := by
    constructor
    · intro hphase
      by_contra hx
      have hmul := mul_le_mul_of_nonneg_left (le_of_not_gt hx) hunit.le
      nlinarith
    · intro hx
      have hmul := mul_lt_mul_of_pos_left hx hunit
      nlinarith
  by_cases hx : x < (p : ℝ) / 2
  · have hphase := hiff.mpr hx
    simp [hx, hphase]
  · have hphase : ¬harmonizedUnit * x < (p : ℝ) * harmonizedUnit / 2 :=
      fun h ↦ hx (hiff.mp h)
    simp [hx, hphase]

/-- The new phase is the old Kummer phase scaled by half the harmonized circumference. -/
theorem harmonizedCellPhase_eq_halfCircumference_mul_railPhase {p n j : ℕ} (hp : 0 < p) :
    harmonizedCellPhase p n j =
      (harmonizedCircumference p / 2) * railPhase p n (j + 1) := by
  rw [harmonizedCellPhase, normalizedCellCoordinate, harmonizedCircumference, railPhase,
    harmonizedUnit]
  push_cast
  rw [pow_succ]
  field_simp [hp.ne']
  ring

/-- The Kummer no-carry gate is exactly the lower angular half-cell. -/
theorem harmonizedCellPhase_lt_half_iff {p n j : ℕ} (hp : 0 < p) :
    harmonizedCellPhase p n j < harmonizedCircumference p / 2 ↔
      2 * (n % p ^ (j + 1)) < p ^ (j + 1) := by
  have hcirc : 0 < harmonizedCircumference p / 2 := by
    rw [harmonizedCircumference, harmonizedUnit]
    positivity
  rw [harmonizedCellPhase_eq_halfCircumference_mul_railPhase hp]
  have hscale :
      harmonizedCircumference p / 2 * railPhase p n (j + 1) <
          harmonizedCircumference p / 2 ↔ railPhase p n (j + 1) < 1 := by
    constructor <;> intro h <;> nlinarith
  rw [hscale]
  have hcarry := not_congr (carryAt_iff_one_le_railPhase (n := n) (i := j + 1) hp)
  simpa only [carryAt, not_le] using hcarry.symm

/-- Once the previous cell is closed, the next cell is closed exactly for the lower digit
channels.  This includes the boundary channel for odd `p` and is valid for every `p > 1`. -/
theorem next_noCarry_iff_digit_le_half {p n j : ℕ} (hp : 1 < p)
    (hprevious : 2 * (n % p ^ (j + 1)) < p ^ (j + 1)) :
    2 * (n % p ^ (j + 1 + 1)) < p ^ (j + 1 + 1) ↔
      railDigit p n (j + 1) ≤ (p - 1) / 2 := by
  let q := p ^ (j + 1)
  let a := railDigit p n (j + 1)
  have hq : 0 < q := pow_pos (by omega) (j + 1)
  have hdecomp := mod_pow_succ_eq_mod_add_digit_mul_pow p n (j + 1)
  rw [hdecomp]
  change 2 * (n % q + a * q) < q * p ↔ a ≤ (p - 1) / 2
  constructor
  · intro hnext
    have hmul : (2 * a) * q < p * q := calc
      (2 * a) * q = 2 * (a * q) := by ring
      _ ≤ 2 * (n % q + a * q) := by omega
      _ < q * p := hnext
      _ = p * q := by ac_rfl
    have ha : 2 * a < p := (Nat.mul_lt_mul_right hq).mp hmul
    omega
  · intro ha
    have ha2 : 2 * a ≤ p - 1 := by omega
    have hmul := Nat.mul_le_mul_right q ha2
    have hpdecomp : 1 + (p - 1) = p := by omega
    calc
      2 * (n % q + a * q) = 2 * (n % q) + (2 * a) * q := by ring
      _ < q + (2 * a) * q := Nat.add_lt_add_right hprevious ((2 * a) * q)
      _ ≤ q + (p - 1) * q := Nat.add_le_add_left hmul q
      _ = (1 + (p - 1)) * q := by ring
      _ = q * p := by rw [hpdecomp, mul_comm]

/-- Angular statement of exact lower-channel selection. -/
theorem next_harmonizedCell_closed_iff_digit_le_half {p n j : ℕ} (hp : 1 < p)
    (hprevious : harmonizedCellPhase p n j < harmonizedCircumference p / 2) :
    harmonizedCellPhase p n (j + 1) < harmonizedCircumference p / 2 ↔
      railDigit p n (j + 1) ≤ (p - 1) / 2 := by
  have hprevious' := (harmonizedCellPhase_lt_half_iff (n := n) (j := j) (by omega)).mp
    hprevious
  rw [harmonizedCellPhase_lt_half_iff (n := n) (j := j + 1) (by omega)]
  exact next_noCarry_iff_digit_le_half hp hprevious'

/-- A trajectory is dynamically closed through `cells` normalized carry cells. -/
def DynamicClosedOrbit (p n cells : ℕ) : Prop :=
  ∀ j < cells, harmonizedCellPhase p n j < harmonizedCircumference p / 2

/-- Finite dynamic closure has a classical decision procedure. -/
noncomputable instance dynamicClosedOrbitDecidable (p n cells : ℕ) :
    Decidable (DynamicClosedOrbit p n cells) := Classical.propDecidable _

/-- Dynamic closure through `cells` is exactly Kummer closure through level `cells`. -/
theorem dynamicClosedOrbit_iff_carryFreeThrough {p n cells : ℕ} (hp : 0 < p) :
    DynamicClosedOrbit p n cells ↔ CarryFreeThrough p n (cells + 1) := by
  constructor
  · intro horbit i hi
    have hi' := mem_Ico.mp hi
    have hphase := horbit (i - 1) (by omega)
    have hcell := (harmonizedCellPhase_lt_half_iff
      (n := n) (j := i - 1) hp).mp hphase
    simpa [Nat.sub_add_cancel hi'.1] using hcell
  · intro hfree j hj
    apply (harmonizedCellPhase_lt_half_iff (n := n) (j := j) hp).mpr
    exact hfree (j + 1) (by simp only [mem_Ico]; omega)

/-- Kummer's theorem exported directly as terminal closure of the dynamic orbit. -/
theorem prime_not_dvd_centralBinom_iff_dynamicClosedOrbit {p n : ℕ} (hp : p.Prime) :
    ¬p ∣ (2 * n).choose n ↔ DynamicClosedOrbit p n (Nat.log p (2 * n)) := by
  rw [prime_not_dvd_centralBinom_iff_carryFree hp, CarryFree, carryCutoff,
    dynamicClosedOrbit_iff_carryFreeThrough hp.pos]

/-- Exact product of the first `cells` dynamic half-cell gates. -/
noncomputable def dynamicSurvivalWeight (p n cells : ℕ) : ℝ :=
  ∏ i ∈ range cells, lowerHalfCellGate p (harmonizedCellPhase p n i)

/-- The dynamic survival weight is the Boolean indicator of a closed orbit. -/
theorem dynamicSurvivalWeight_eq_ite (p n cells : ℕ) :
    dynamicSurvivalWeight p n cells = if DynamicClosedOrbit p n cells then 1 else 0 := by
  classical
  by_cases horbit : DynamicClosedOrbit p n cells
  · rw [if_pos horbit]
    apply prod_eq_one
    intro i hi
    rw [lowerHalfCellGate, if_pos (horbit i (mem_range.mp hi))]
  · rw [if_neg horbit]
    simp only [DynamicClosedOrbit, not_forall, not_lt] at horbit
    obtain ⟨i, hi, hgate⟩ := horbit
    apply prod_eq_zero (mem_range.mpr hi)
    rw [lowerHalfCellGate, if_neg (not_lt.mpr hgate)]

/-- Exact terminal coherence weight at the canonical Kummer depth. -/
noncomputable def dynamicFinalWeight (p n : ℕ) : ℝ :=
  dynamicSurvivalWeight p n (Nat.log p (2 * n))

/-- The terminal dynamic coherence is exactly the original carry-free selector. -/
theorem dynamicFinalWeight_eq_ite_carryFree {p n : ℕ} (hp : 0 < p) :
    dynamicFinalWeight p n = if CarryFree p n then 1 else 0 := by
  rw [dynamicFinalWeight, dynamicSurvivalWeight_eq_ite]
  have horbit :
      DynamicClosedOrbit p n (Nat.log p (2 * n)) ↔ CarryFree p n := by
    rw [CarryFree, carryCutoff, dynamicClosedOrbit_iff_carryFreeThrough hp]
  by_cases hclosed : DynamicClosedOrbit p n (Nat.log p (2 * n))
  · have hfree := horbit.mp hclosed
    simp [hclosed, hfree]
  · have hfree : ¬CarryFree p n := fun h ↦ hclosed (horbit.mpr h)
    simp [hclosed, hfree]

/-- State transported by the dynamic cell operator. -/
@[ext] structure DynamicCellState where
  phase : ℝ
  remaining : ℕ
  coherence : ℝ

/-- Universal dynamic cell operator at base `p` and digit channel `a`. -/
noncomputable def dynamicCellOperator (p a : ℕ) (s : DynamicCellState) : DynamicCellState :=
  let nextPhase := harmonizedUnit * a + s.phase / p
  {
    phase := nextPhase
    remaining := s.remaining - 1
    coherence := s.coherence * lowerHalfCellGate p nextPhase
  }

/-- Exact accumulated closure weight through zero-based cell `j`. -/
noncomputable def dynamicClosureWeight (p n j : ℕ) : ℝ :=
  dynamicSurvivalWeight p n (j + 1)

/-- The arithmetic orbit embedded in the dynamic state space. -/
noncomputable def dynamicOrbitState (p n totalDepth j : ℕ) : DynamicCellState :=
  {
    phase := harmonizedCellPhase p n j
    remaining := totalDepth - (j + 1)
    coherence := dynamicClosureWeight p n j
  }

/-- The dynamic operator follows the exact arithmetic orbit, rather than a fitted model. -/
theorem dynamicCellOperator_exact_orbit {p n totalDepth j : ℕ} (hp : 0 < p) :
    dynamicCellOperator p (railDigit p n (j + 1))
        (dynamicOrbitState p n totalDepth j) =
      dynamicOrbitState p n totalDepth (j + 1) := by
  ext
  · simpa [dynamicCellOperator, dynamicOrbitState] using
      (harmonizedCellPhase_succ (p := p) (n := n) (j := j) hp).symm
  · simp only [dynamicCellOperator, dynamicOrbitState]
    omega
  · simp [dynamicCellOperator, dynamicOrbitState, dynamicClosureWeight,
      dynamicSurvivalWeight, prod_range_succ, harmonizedCellPhase_succ hp]

/-- Coherence is a Lyapunov coordinate: one exact dynamic step cannot increase it. -/
theorem dynamicCellOperator_coherence_le (p a : ℕ) (s : DynamicCellState)
    (hcoherence : 0 ≤ s.coherence) :
    (dynamicCellOperator p a s).coherence ≤ s.coherence := by
  rw [dynamicCellOperator]
  dsimp only
  by_cases hgate : harmonizedUnit * a + s.phase / p < harmonizedCircumference p / 2
  · simp [lowerHalfCellGate, hgate]
  · simp [lowerHalfCellGate, hgate, hcoherence]

/-- The exact closure weight is nonnegative. -/
theorem dynamicClosureWeight_nonneg (p n j : ℕ) : 0 ≤ dynamicClosureWeight p n j := by
  rw [dynamicClosureWeight, dynamicSurvivalWeight]
  apply prod_nonneg
  intro i _
  by_cases hgate : harmonizedCellPhase p n i < harmonizedCircumference p / 2
  · simp [lowerHalfCellGate, hgate]
  · simp [lowerHalfCellGate, hgate]

/-- Exact closure weights are Boolean and hence at most one. -/
theorem dynamicClosureWeight_le_one (p n j : ℕ) : dynamicClosureWeight p n j ≤ 1 := by
  rw [dynamicClosureWeight, dynamicSurvivalWeight_eq_ite]
  split <;> norm_num

/-- One more exact carry cell cannot increase the accumulated closure weight. -/
theorem dynamicClosureWeight_succ_le {p n j : ℕ} (hp : 0 < p) :
    dynamicClosureWeight p n (j + 1) ≤ dynamicClosureWeight p n j := by
  rw [dynamicClosureWeight, dynamicClosureWeight, dynamicSurvivalWeight,
    dynamicSurvivalWeight, prod_range_succ]
  have h := dynamicCellOperator_coherence_le p (railDigit p n (j + 1))
    { phase := harmonizedCellPhase p n j
      remaining := 0
      coherence := ∏ i ∈ range (j + 1), lowerHalfCellGate p (harmonizedCellPhase p n i) }
    (dynamicClosureWeight_nonneg p n j)
  simpa [dynamicCellOperator, harmonizedCellPhase_succ hp] using h

/-- Exact dynamic update split into the independent channel average and the actual-channel
discrepancy. -/
theorem dynamicClosureWeight_succ_eq_average_add_discrepancy {p n j : ℕ} (hp : 0 < p) :
    dynamicClosureWeight p n (j + 1) =
      dynamicClosureWeight p n j *
          normalizedChannelAverage p (normalizedCellCoordinate p n j) +
        dynamicClosureWeight p n j * normalizedChannelDiscrepancy p
          (railDigit p n (j + 1)) (normalizedCellCoordinate p n j) := by
  have hphase :
      harmonizedCellPhase p n (j + 1) = harmonizedUnit *
        normalizedCellStep p (railDigit p n (j + 1)) (normalizedCellCoordinate p n j) := by
    rw [harmonizedCellPhase, normalizedCellCoordinate_succ hp, normalizedCellStep]
  calc
    dynamicClosureWeight p n (j + 1) =
        dynamicClosureWeight p n j *
          lowerHalfCellGate p (harmonizedCellPhase p n (j + 1)) := by
            simp [dynamicClosureWeight, dynamicSurvivalWeight, prod_range_succ]
    _ = dynamicClosureWeight p n j * normalizedLowerHalfGate p
        (normalizedCellStep p (railDigit p n (j + 1))
          (normalizedCellCoordinate p n j)) := by
            rw [hphase, lowerHalfCellGate_harmonized_eq_normalized]
    _ = dynamicClosureWeight p n j *
          normalizedChannelAverage p (normalizedCellCoordinate p n j) +
        dynamicClosureWeight p n j * normalizedChannelDiscrepancy p
          (railDigit p n (j + 1)) (normalizedCellCoordinate p n j) := by
            rw [normalizedGate_eq_average_add_discrepancy]
            ring

/-- Boolean form of the accumulated closure coordinate. -/
theorem dynamicClosureWeight_eq_ite (p n j : ℕ) :
    dynamicClosureWeight p n j = if DynamicClosedOrbit p n (j + 1) then 1 else 0 := by
  rw [dynamicClosureWeight, dynamicSurvivalWeight_eq_ite]

/-- The independent channel-average part contracts every surviving exact orbit by `2/3`. -/
theorem dynamicClosure_mul_channelAverage_le_two_thirds {p n j : ℕ} (hp : 1 < p) :
    dynamicClosureWeight p n j * normalizedChannelAverage p
        (normalizedCellCoordinate p n j) ≤
      (2 : ℝ) / 3 * dynamicClosureWeight p n j := by
  by_cases horbit : DynamicClosedOrbit p n (j + 1)
  · have hphase := horbit j (by omega)
    have hxhalf := (harmonizedCellPhase_lt_half_iff_normalized p n j).mp hphase
    have hx0 := (normalizedCellCoordinate_mem_carrier
      (p := p) (n := n) (j := j) (by omega)).1
    rw [dynamicClosureWeight_eq_ite, if_pos horbit]
    simpa using normalizedChannelAverage_le_two_thirds hp hx0 hxhalf
  · rw [dynamicClosureWeight_eq_ite, if_neg horbit]
    norm_num

/-- Prime-harmonic energy surviving through cell `j`. -/
noncomputable def dynamicHarmonicEnergy (n j : ℕ) : ℝ :=
  ∑ p ∈ n.primesLE, (1 : ℝ) / (p : ℝ) * dynamicClosureWeight p n j

/-- Prime-harmonic error of the actual digits relative to the independent channel operator. -/
noncomputable def dynamicHarmonicDiscrepancy (n j : ℕ) : ℝ :=
  ∑ p ∈ n.primesLE, (1 : ℝ) / (p : ℝ) * dynamicClosureWeight p n j *
    normalizedChannelDiscrepancy p (railDigit p n (j + 1))
      (normalizedCellCoordinate p n j)

/-- Non-recursive transfer inequality: universal `2/3` contraction plus the explicit arithmetic
channel discrepancy. -/
theorem dynamicHarmonicEnergy_succ_le_two_thirds_add_discrepancy (n j : ℕ) :
    dynamicHarmonicEnergy n (j + 1) ≤
      (2 : ℝ) / 3 * dynamicHarmonicEnergy n j + dynamicHarmonicDiscrepancy n j := by
  rw [dynamicHarmonicEnergy, dynamicHarmonicEnergy, dynamicHarmonicDiscrepancy]
  calc
    ∑ p ∈ n.primesLE, (1 : ℝ) / (p : ℝ) * dynamicClosureWeight p n (j + 1) ≤
        ∑ p ∈ n.primesLE,
          ((2 : ℝ) / 3 * ((1 : ℝ) / (p : ℝ) * dynamicClosureWeight p n j) +
            (1 : ℝ) / (p : ℝ) * dynamicClosureWeight p n j *
              normalizedChannelDiscrepancy p (railDigit p n (j + 1))
                (normalizedCellCoordinate p n j)) := by
          apply sum_le_sum
          intro p hpMem
          have hpPrime := Nat.prime_of_mem_primesLE hpMem
          have hrecip : 0 ≤ (1 : ℝ) / (p : ℝ) := by positivity
          have haverage := dynamicClosure_mul_channelAverage_le_two_thirds
            (p := p) (n := n) (j := j) hpPrime.one_lt
          calc
            (1 : ℝ) / (p : ℝ) * dynamicClosureWeight p n (j + 1) =
                (1 : ℝ) / (p : ℝ) *
                  (dynamicClosureWeight p n j * normalizedChannelAverage p
                      (normalizedCellCoordinate p n j) +
                    dynamicClosureWeight p n j * normalizedChannelDiscrepancy p
                      (railDigit p n (j + 1)) (normalizedCellCoordinate p n j)) := by
                        rw [dynamicClosureWeight_succ_eq_average_add_discrepancy hpPrime.pos]
            _ ≤ (1 : ℝ) / (p : ℝ) *
                ((2 : ℝ) / 3 * dynamicClosureWeight p n j +
                    dynamicClosureWeight p n j * normalizedChannelDiscrepancy p
                    (railDigit p n (j + 1)) (normalizedCellCoordinate p n j)) :=
                      mul_le_mul_of_nonneg_left (by linarith [haverage]) hrecip
            _ = (2 : ℝ) / 3 *
                  ((1 : ℝ) / (p : ℝ) * dynamicClosureWeight p n j) +
                (1 : ℝ) / (p : ℝ) * dynamicClosureWeight p n j *
                  normalizedChannelDiscrepancy p (railDigit p n (j + 1))
                    (normalizedCellCoordinate p n j) := by ring
    _ = (2 : ℝ) / 3 *
          (∑ p ∈ n.primesLE, (1 : ℝ) / (p : ℝ) * dynamicClosureWeight p n j) +
        ∑ p ∈ n.primesLE, (1 : ℝ) / (p : ℝ) * dynamicClosureWeight p n j *
          normalizedChannelDiscrepancy p (railDigit p n (j + 1))
            (normalizedCellCoordinate p n j) := by
              rw [sum_add_distrib, Finset.mul_sum]

/-- The exact dynamic harmonic energy is nonincreasing with carry depth. -/
theorem dynamicHarmonicEnergy_succ_le (n j : ℕ) :
    dynamicHarmonicEnergy n (j + 1) ≤ dynamicHarmonicEnergy n j := by
  apply sum_le_sum
  intro p hp
  exact mul_le_mul_of_nonneg_left (dynamicClosureWeight_succ_le
    (p := p) (n := n) (j := j) (Nat.prime_of_mem_primesLE hp).pos) (by
    have hpprime := Nat.prime_of_mem_primesLE hp
    positivity)

/-- Prime-harmonic readout of all terminal dynamic states. -/
noncomputable def dynamicRailMass (n : ℕ) : ℝ :=
  ∑ p ∈ n.primesLE, (1 : ℝ) / (p : ℝ) * dynamicFinalWeight p n

/-- Lossless dynamic adapter: the terminal coherence readout is Erdős's original mass. -/
theorem dynamicRailMass_eq_erdos377Mass (n : ℕ) :
    dynamicRailMass n = erdos377Mass n := by
  rw [erdos377Mass_eq_carryFreeRailSum, dynamicRailMass, carryFreePrimes]
  simp only [sum_filter]
  apply sum_congr rfl
  intro p hp
  rw [dynamicFinalWeight_eq_ite_carryFree (Nat.prime_of_mem_primesLE hp).pos]
  by_cases hfree : CarryFree p n <;> simp [hfree]

/-! ## Carry rails in the `(n,p)`-plane -/

/-- The Boolean carry state at prefix level `i`; it is always `0` or `1` for `p > 0`. -/
def carryState (p n i : ℕ) : ℕ := (2 * (n % p ^ i)) / p ^ i

/-- The signed change of carry state between adjacent nested rails. -/
def carryIncrement (p n j : ℕ) : ℤ :=
  (carryState p n (j + 1) : ℤ) - carryState p n j

/-- The zeroth prefix has no carry state. -/
theorem carryState_zero (p n : ℕ) : carryState p n 0 = 0 := by
  rw [carryState, pow_zero, Nat.mod_one]
  norm_num

/-- A prefix is inside its zero-carry rail exactly when its carry state is zero. -/
theorem carryState_eq_zero_iff {p n i : ℕ} (hp : 0 < p) :
    carryState p n i = 0 ↔ 2 * (n % p ^ i) < p ^ i := by
  rw [carryState, Nat.div_eq_zero_iff]
  constructor
  · rintro (hzero | hlt)
    · exact absurd hzero (pow_ne_zero i hp.ne')
    · exact hlt
  · exact Or.inr

/-- Vanishing increments from level zero force the state at level `i` to vanish. -/
theorem carryState_eq_zero_of_increments {p n i : ℕ}
    (hκ : ∀ j < i, carryIncrement p n j = 0) : carryState p n i = 0 := by
  induction i with
  | zero => exact carryState_zero p n
  | succ i ih =>
      have hprev : carryState p n i = 0 := ih fun j hj ↦ hκ j (hj.trans i.lt_succ_self)
      have hstep := hκ i i.lt_succ_self
      rw [carryIncrement, sub_eq_zero] at hstep
      have hprevCast : (carryState p n i : ℤ) = 0 := congrArg (fun x : ℕ ↦ (x : ℤ)) hprev
      have hnextCast : (carryState p n (i + 1) : ℤ) = 0 := hstep.trans hprevCast
      exact_mod_cast hnextCast

/-- A rail is closed through `b` when every adjacent carry increment before `b` is zero. -/
def IncrementClosedThrough (p n b : ℕ) : Prop :=
  ∀ j, j + 1 < b → carryIncrement p n j = 0

/-- Increment closure and the original zero-carry ledger are the same rail geometry. -/
theorem incrementClosedThrough_iff_carryFreeThrough {p n b : ℕ} (hp : 0 < p) :
    IncrementClosedThrough p n b ↔ CarryFreeThrough p n b := by
  constructor
  · intro hκ i hi
    rw [← carryState_eq_zero_iff hp]
    have hi' := mem_Ico.mp hi
    exact carryState_eq_zero_of_increments fun j hj ↦
      hκ j ((Nat.succ_le_of_lt hj).trans_lt hi'.2)
  · intro hfree j hj
    rw [carryIncrement, sub_eq_zero]
    have hnext : carryState p n (j + 1) = 0 :=
      (carryState_eq_zero_iff hp).2 (hfree (j + 1) (by simp only [mem_Ico]; omega))
    have hprev : carryState p n j = 0 := by
      rcases j with _ | j
      · exact carryState_zero p n
      · exact (carryState_eq_zero_iff hp).2
          (hfree (j + 1) (by simp only [mem_Ico]; omega))
    omega

/-- Every closed depth-`r` rail lies in the sharper harmonic band
`p^r ≤ n < 2n < p^(r+1)`. -/
theorem carryFree_depth_band_bounds {p n r : ℕ} (hp : p.Prime) (hn : 0 < n)
    (hfree : CarryFree p n) (hdepth : railDepth p n = r) :
    p ^ r ≤ n ∧ 2 * n < p ^ (r + 1) := by
  have hlower : p ^ r ≤ n := by
    rw [← hdepth]
    exact Nat.pow_log_le_self p hn.ne'
  refine ⟨hlower, ?_⟩
  by_contra h
  have hp_le : p ^ (r + 1) ≤ 2 * n := Nat.le_of_not_gt h
  have hlog_le : r + 1 ≤ Nat.log p (2 * n) := Nat.le_log_of_pow_le hp.one_lt hp_le
  have hcell := hfree (r + 1) (by
    simp only [carryCutoff, mem_Ico]
    omega)
  have hn_lt : n < p ^ (r + 1) := by
    rw [← hdepth]
    exact Nat.lt_pow_succ_log_self hp.one_lt n
  rw [Nat.mod_eq_of_lt hn_lt] at hcell
  omega

/-- A surviving depth-`r` rail has cutoff `r+1`, hence exactly `r` active carry cells. -/
theorem carryFree_carryCutoff_eq_depth_succ {p n r : ℕ} (hp : p.Prime) (hn : 0 < n)
    (hfree : CarryFree p n) (hdepth : railDepth p n = r) :
    carryCutoff p n = r + 1 := by
  have hband := carryFree_depth_band_bounds hp hn hfree hdepth
  have hlower : r ≤ Nat.log p (2 * n) :=
    Nat.le_log_of_pow_le hp.one_lt (hband.1.trans (by omega))
  have hupper : Nat.log p (2 * n) < r + 1 :=
    Nat.log_lt_of_lt_pow (by omega) hband.2
  rw [carryCutoff]
  omega

/-- Cardinal form of the active-cell count: the geometric survival factor is calibrated by `r`
half-cell intersections. -/
theorem activeCarryCells_eq_depth {p n r : ℕ} (hp : p.Prime) (hn : 0 < n)
    (hfree : CarryFree p n) (hdepth : railDepth p n = r) :
    #(Ico 1 (carryCutoff p n)) = r := by
  rw [carryFree_carryCutoff_eq_depth_succ hp hn hfree hdepth]
  simp

/-- All prime rails in the `r`-th logarithmic band, before imposing carry closure. -/
def railBand (n r : ℕ) : Finset ℕ :=
  n.primesLE.filter fun p ↦ railDepth p n = r

/-- Prime harmonic mass of a finite rail bank. -/
noncomputable def primeHarmonicMass (s : Finset ℕ) : ℝ :=
  ∑ p ∈ s, (1 : ℝ) / (p : ℝ)

/-- The complete mass is the sum of the harmonic masses of its occupied depth rails. -/
theorem erdos377Mass_eq_sum_depthBandMass (n : ℕ) :
    erdos377Mass n = ∑ r ∈ occupiedDepths n, primeHarmonicMass (depthBand n r) := by
  simpa only [primeHarmonicMass] using erdos377Mass_eq_sum_depthBands n

/-- Imposing the nested zero-carry rails is nonexpansive in prime harmonic measure. -/
theorem depthBand_harmonicMass_le_railBand (n r : ℕ) :
    primeHarmonicMass (depthBand n r) ≤ primeHarmonicMass (railBand n r) := by
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro p hp
    change p ∈ (carryFreePrimes n).filter (fun q ↦ railDepth q n = r) at hp
    rcases mem_filter.mp hp with ⟨hpcf, hdepth⟩
    change p ∈ n.primesLE.filter (fun q ↦ CarryFree q n) at hpcf
    have hpprime : p ∈ n.primesLE := (mem_filter.mp hpcf).1
    change p ∈ n.primesLE.filter (fun q ↦ railDepth q n = r)
    exact mem_filter.mpr ⟨hpprime, hdepth⟩
  · intro p _ _
    positivity

/-- The deterministic geometric target: every additional closed rail contracts prime harmonic
mass by one uniform factor. -/
def UniformRailContraction : Prop :=
  ∃ A ρ : ℝ, 0 ≤ A ∧ 0 ≤ ρ ∧ ρ < 1 ∧
    ∀ n r : ℕ,
      primeHarmonicMass (depthBand n r) ≤
        A * ρ ^ r * primeHarmonicMass (railBand n r)

/-!
Two independent checks of the proposed strict contraction target start as follows:

1. `refine ⟨3 ^ k, k, ?_⟩`: test coherent power rails, whose base-three expansion is a
   single nonzero digit;
2. `obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one ...`: force the proposed geometric factor
   below the exactly surviving singleton mass.

The following compiled family executes both checks.  It shows that a relative contraction for
every individual depth band loses an atomic term: at `n = 3^k`, the depth-`k` raw rail bank and
closed rail bank are both the singleton `{3}` for every `k ≥ 2`.
-/

theorem two_pow_succ_le_three_pow {k : ℕ} (hk : 2 ≤ k) :
    2 ^ (k + 1) ≤ 3 ^ k := by
  induction k, hk using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
      calc
        2 ^ ((k + 1) + 1) = 2 ^ (k + 1) * 2 := by rw [pow_succ]
        _ ≤ 3 ^ k * 2 := Nat.mul_le_mul_right 2 ih
        _ ≤ 3 ^ k * 3 := Nat.mul_le_mul_left (3 ^ k) (by norm_num)
        _ = 3 ^ (k + 1) := by rw [pow_succ]

theorem three_pow_carryCutoff (k : ℕ) : carryCutoff 3 (3 ^ k) = k + 1 := by
  rw [carryCutoff]
  congr 1
  apply Nat.log_eq_of_pow_le_of_lt_pow
  · simp
  · rw [pow_succ]
    nlinarith [pow_pos (by norm_num : 0 < (3 : ℕ)) k]

theorem three_pow_carryFree (k : ℕ) : CarryFree 3 (3 ^ k) := by
  intro i hi
  rw [three_pow_carryCutoff] at hi
  simp only [mem_Ico] at hi
  have hik : i ≤ k := by omega
  have hdvd : 3 ^ i ∣ 3 ^ k := Nat.pow_dvd_pow 3 hik
  rw [Nat.mod_eq_zero_of_dvd hdvd]
  positivity

/-- The coherent power orbit keeps unit dynamic coherence through every active cell. -/
theorem three_pow_dynamicSurvivalWeight_eq_one {k cells : ℕ} (hcells : cells ≤ k) :
    dynamicSurvivalWeight 3 (3 ^ k) cells = 1 := by
  rw [dynamicSurvivalWeight_eq_ite, if_pos]
  intro j hj
  apply (harmonizedCellPhase_lt_half_iff (p := 3) (n := 3 ^ k) (j := j) (by norm_num)).mpr
  have hpow : j + 1 ≤ k := by omega
  rw [Nat.mod_eq_zero_of_dvd (Nat.pow_dvd_pow 3 hpow)]
  positivity

theorem three_pow_railDepth (k : ℕ) : railDepth 3 (3 ^ k) = k := by
  exact Nat.log_pow (by norm_num) k

theorem mem_railBand_three_pow_iff {p k : ℕ} (hk : 2 ≤ k) :
    p ∈ railBand (3 ^ k) k ↔ p = 3 := by
  constructor
  · intro hmem
    have hprime : p.Prime := Nat.prime_of_mem_primesLE (mem_filter.mp hmem).1
    have hdepth : Nat.log p (3 ^ k) = k := (mem_filter.mp hmem).2
    have hpow : p ^ k ≤ 3 ^ k := by
      calc
        p ^ k = p ^ Nat.log p (3 ^ k) := by rw [hdepth]
        _ ≤ 3 ^ k := Nat.pow_log_le_self p (show 3 ^ k ≠ 0 by positivity)
    have hp_le_three : p ≤ 3 := (Nat.pow_le_pow_iff_left (by omega)).mp hpow
    have hp_two_le : 2 ≤ p := hprime.two_le
    have hp_cases : p = 2 ∨ p = 3 := by omega
    rcases hp_cases with rfl | rfl
    · have hstrict := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) (3 ^ k)
      rw [hdepth] at hstrict
      exact absurd hstrict (Nat.not_lt_of_ge (two_pow_succ_le_three_pow hk))
    · rfl
  · rintro rfl
    apply mem_filter.mpr
    refine ⟨?_, three_pow_railDepth k⟩
    exact Nat.mem_primesLE.mpr ⟨by
      calc
        3 ≤ 3 ^ 2 := by norm_num
        _ ≤ 3 ^ k := Nat.pow_le_pow_right (by norm_num) hk, by norm_num⟩

theorem railBand_three_pow {k : ℕ} (hk : 2 ≤ k) :
    railBand (3 ^ k) k = {3} := by
  ext p
  simpa using mem_railBand_three_pow_iff (p := p) hk

theorem depthBand_three_pow {k : ℕ} (hk : 2 ≤ k) :
    depthBand (3 ^ k) k = {3} := by
  apply Finset.Subset.antisymm
  · intro p hp
    have hraw : p ∈ railBand (3 ^ k) k := by
      apply mem_filter.mpr
      have hcf := (mem_filter.mp hp).1
      exact ⟨(mem_filter.mp hcf).1, (mem_filter.mp hp).2⟩
    simpa [railBand_three_pow hk] using hraw
  · intro p hp
    have hp3 : p = 3 := by simpa using hp
    subst p
    apply mem_filter.mpr
    refine ⟨?_, three_pow_railDepth k⟩
    apply mem_filter.mpr
    exact ⟨Nat.mem_primesLE.mpr ⟨by
      calc
        3 ≤ 3 ^ 2 := by norm_num
        _ ≤ 3 ^ k := Nat.pow_le_pow_right (by norm_num) hk, by norm_num⟩,
      three_pow_carryFree k⟩

theorem primeHarmonicMass_singleton_three :
    primeHarmonicMass {3} = (1 : ℝ) / 3 := by
  simp [primeHarmonicMass]

theorem not_uniformRailContraction : ¬UniformRailContraction := by
  rintro ⟨A, ρ, hA, hρ0, hρ1, hcontract⟩
  by_cases hAzero : A = 0
  · have h := hcontract (3 ^ 2) 2
    rw [depthBand_three_pow (by omega), railBand_three_pow (by omega),
      primeHarmonicMass_singleton_three, hAzero] at h
    norm_num at h
  · have hApos : 0 < A := lt_of_le_of_ne hA (Ne.symm hAzero)
    have hthreshold : 0 < (1 : ℝ) / (A + 1) := by positivity
    obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one hthreshold hρ1
    let K := k + 2
    have hK : 2 ≤ K := by simp [K]
    have hρle : ρ ≤ 1 := le_of_lt hρ1
    have hpow : ρ ^ K ≤ ρ ^ k := by
      rw [show K = k + 2 by rfl, pow_add]
      have hsquare : ρ ^ 2 ≤ 1 := pow_le_one₀ hρ0 hρle
      nlinarith [pow_nonneg hρ0 k]
    have hAdecay : A * ρ ^ K < 1 := calc
      A * ρ ^ K ≤ A * ρ ^ k := mul_le_mul_of_nonneg_left hpow hA
      _ < A * ((1 : ℝ) / (A + 1)) := mul_lt_mul_of_pos_left hk hApos
      _ < 1 := by
        rw [one_div, ← div_eq_mul_inv, div_lt_one (by linarith : 0 < A + 1)]
        linarith
    have h := hcontract (3 ^ K) K
    rw [depthBand_three_pow hK, railBand_three_pow hK,
      primeHarmonicMass_singleton_three] at h
    nlinarith

/-! ## Atomic/diffuse repair of the rail target

A depth-`r` raw band with at most `r` prime rails is atom-dominated.  Its closed mass is charged
to the coherent ledger instead of being forced through a relative contraction estimate.  The
complementary bands contain more samples than active carry cells and form the diffuse ledger.
-/

/-- A band is atom-dominated when it contains no more raw prime samples than carry levels. -/
def IsAtomicRailBand (n r : ℕ) : Prop := (railBand n r).card ≤ r

/-- Closed rails belonging to an atom-dominated band. -/
noncomputable def atomicDepthBand (n r : ℕ) : Finset ℕ := by
  classical
  exact if IsAtomicRailBand n r then depthBand n r else ∅

/-- Closed rails in a sufficiently populated band. -/
noncomputable def diffuseDepthBand (n r : ℕ) : Finset ℕ := by
  classical
  exact if IsAtomicRailBand n r then ∅ else depthBand n r

/-- Raw prime rails supporting the diffuse closed ledger. -/
noncomputable def diffuseRailBand (n r : ℕ) : Finset ℕ := by
  classical
  exact if IsAtomicRailBand n r then ∅ else railBand n r

/-- Every closed depth band splits exactly into its coherent and diffuse ledgers. -/
theorem depthBand_eq_atomic_union_diffuse (n r : ℕ) :
    depthBand n r = atomicDepthBand n r ∪ diffuseDepthBand n r := by
  classical
  by_cases h : IsAtomicRailBand n r
  · simp [atomicDepthBand, diffuseDepthBand, h]
  · simp [atomicDepthBand, diffuseDepthBand, h]

/-- Exact additive harmonic readout of the coherent/diffuse split. -/
theorem primeHarmonicMass_depthBand_eq_atomic_add_diffuse (n r : ℕ) :
    primeHarmonicMass (depthBand n r) =
      primeHarmonicMass (atomicDepthBand n r) +
        primeHarmonicMass (diffuseDepthBand n r) := by
  classical
  by_cases h : IsAtomicRailBand n r
  · simp [atomicDepthBand, diffuseDepthBand, h, primeHarmonicMass]
  · simp [atomicDepthBand, diffuseDepthBand, h, primeHarmonicMass]

/-- The coherent power family is routed wholly into the atomic ledger. -/
theorem atomicDepthBand_three_pow {k : ℕ} (hk : 2 ≤ k) :
    atomicDepthBand (3 ^ k) k = {3} := by
  have hatomic : IsAtomicRailBand (3 ^ k) k := by
    rw [IsAtomicRailBand, railBand_three_pow hk]
    simp
    omega
  simp [atomicDepthBand, hatomic, depthBand_three_pow hk]

/-- No part of the coherent power family is incorrectly sent to the diffuse operator. -/
theorem diffuseDepthBand_three_pow {k : ℕ} (hk : 2 ≤ k) :
    diffuseDepthBand (3 ^ k) k = ∅ := by
  have hatomic : IsAtomicRailBand (3 ^ k) k := by
    rw [IsAtomicRailBand, railBand_three_pow hk]
    simp
    omega
  simp [diffuseDepthBand, hatomic]

/-! ## Harmonic atomic/diffuse split

The cardinal split above is useful combinatorially, but it is not itself scale invariant.  The
following split uses only reciprocal-prime mass: a band is harmonic-atomic when one atom carries
at least `1/r` of the raw band mass. -/

/-- Dimensionless harmonic concentration condition for one logarithmic depth band. -/
def IsHarmonicAtomicRailBand (n r : ℕ) : Prop :=
  ∃ p ∈ railBand n r,
    primeHarmonicMass (railBand n r) ≤
      (r : ℝ) * ((1 : ℝ) / (p : ℝ))

/-- Closed rails whose raw band contains a harmonically concentrated atom. -/
noncomputable def harmonicAtomicDepthBand (n r : ℕ) : Finset ℕ := by
  classical
  exact if IsHarmonicAtomicRailBand n r then depthBand n r else ∅

/-- Raw rails supporting the harmonic-atomic closed ledger. -/
noncomputable def harmonicAtomicRailBand (n r : ℕ) : Finset ℕ := by
  classical
  exact if IsHarmonicAtomicRailBand n r then railBand n r else ∅

/-- Closed rails in the harmonic-diffuse complement. -/
noncomputable def harmonicDiffuseDepthBand (n r : ℕ) : Finset ℕ := by
  classical
  exact if IsHarmonicAtomicRailBand n r then ∅ else depthBand n r

/-- Raw rails supporting the harmonic-diffuse closed ledger. -/
noncomputable def harmonicDiffuseRailBand (n r : ℕ) : Finset ℕ := by
  classical
  exact if IsHarmonicAtomicRailBand n r then ∅ else railBand n r

theorem harmonicAtomicRailBand_subset_railBand (n r : ℕ) :
    harmonicAtomicRailBand n r ⊆ railBand n r := by
  classical
  by_cases h : IsHarmonicAtomicRailBand n r <;>
    simp [harmonicAtomicRailBand, h]

theorem harmonicDiffuseRailBand_subset_railBand (n r : ℕ) :
    harmonicDiffuseRailBand n r ⊆ railBand n r := by
  classical
  by_cases h : IsHarmonicAtomicRailBand n r <;>
    simp [harmonicDiffuseRailBand, h]

/-- In a harmonic-diffuse band, every individual reciprocal-prime atom is strictly below the
`1/r` concentration scale of the whole band. -/
theorem harmonicDiffuse_atom_lt_bandMass {p n r : ℕ}
    (hp : p ∈ harmonicDiffuseRailBand n r) :
    (r : ℝ) * ((1 : ℝ) / (p : ℝ)) <
      primeHarmonicMass (harmonicDiffuseRailBand n r) := by
  classical
  by_cases hatomic : IsHarmonicAtomicRailBand n r
  · simp [harmonicDiffuseRailBand, hatomic] at hp
  · have hprail : p ∈ railBand n r := by
      simpa [harmonicDiffuseRailBand, hatomic] using hp
    have hnle : ¬primeHarmonicMass (railBand n r) ≤
        (r : ℝ) * ((1 : ℝ) / (p : ℝ)) := by
      intro hmass
      exact hatomic ⟨p, hprail, hmass⟩
    have hlt : (r : ℝ) * ((1 : ℝ) / (p : ℝ)) <
        primeHarmonicMass (railBand n r) := lt_of_not_ge hnle
    simpa [harmonicDiffuseRailBand, hatomic] using hlt

/-- Exact harmonic-scale partition of every closed band. -/
theorem depthBand_eq_harmonicAtomic_union_diffuse (n r : ℕ) :
    depthBand n r =
      harmonicAtomicDepthBand n r ∪ harmonicDiffuseDepthBand n r := by
  classical
  by_cases h : IsHarmonicAtomicRailBand n r
  · simp [harmonicAtomicDepthBand, harmonicDiffuseDepthBand, h]
  · simp [harmonicAtomicDepthBand, harmonicDiffuseDepthBand, h]

/-- Exact additive harmonic readout of the scale-invariant partition. -/
theorem primeHarmonicMass_depthBand_eq_harmonicAtomic_add_diffuse (n r : ℕ) :
    primeHarmonicMass (depthBand n r) =
      primeHarmonicMass (harmonicAtomicDepthBand n r) +
        primeHarmonicMass (harmonicDiffuseDepthBand n r) := by
  classical
  by_cases h : IsHarmonicAtomicRailBand n r
  · simp [harmonicAtomicDepthBand, harmonicDiffuseDepthBand, h, primeHarmonicMass]
  · simp [harmonicAtomicDepthBand, harmonicDiffuseDepthBand, h, primeHarmonicMass]

/-- The coherent power rail is detected by harmonic concentration alone. -/
theorem harmonicAtomicDepthBand_three_pow {k : ℕ} (hk : 2 ≤ k) :
    harmonicAtomicDepthBand (3 ^ k) k = {3} := by
  have hatomic : IsHarmonicAtomicRailBand (3 ^ k) k := by
    refine ⟨3, ?_, ?_⟩
    · rw [railBand_three_pow hk]
      simp
    · rw [railBand_three_pow hk, primeHarmonicMass_singleton_three]
      have hkreal : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast (show 1 ≤ k by omega)
      nlinarith
  simp [harmonicAtomicDepthBand, hatomic, depthBand_three_pow hk]

/-- Consequently the coherent power rail contributes nothing to the harmonic-diffuse ledger. -/
theorem harmonicDiffuseDepthBand_three_pow {k : ℕ} (hk : 2 ≤ k) :
    harmonicDiffuseDepthBand (3 ^ k) k = ∅ := by
  have hatomic : IsHarmonicAtomicRailBand (3 ^ k) k := by
    refine ⟨3, ?_, ?_⟩
    · rw [railBand_three_pow hk]
      simp
    · rw [railBand_three_pow hk, primeHarmonicMass_singleton_three]
      have hkreal : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast (show 1 ≤ k by omega)
      nlinarith
  simp [harmonicDiffuseDepthBand, hatomic]

/-- Harmonic concentration and primality bound the complete raw atomic band by `r/2`. -/
theorem primeHarmonicMass_harmonicAtomicRailBand_le_depth_over_two (n r : ℕ) :
    primeHarmonicMass (harmonicAtomicRailBand n r) ≤ (r : ℝ) / 2 := by
  classical
  by_cases hatomic : IsHarmonicAtomicRailBand n r
  · simp only [harmonicAtomicRailBand, hatomic]
    rcases hatomic with ⟨p, hp, hmass⟩
    have hpPrime : p.Prime := Nat.prime_of_mem_primesLE (mem_filter.mp hp).1
    have hpR : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpPrime.two_le
    have hrecip : (1 : ℝ) / (p : ℝ) ≤ (1 : ℝ) / 2 :=
      one_div_le_one_div_of_le (by norm_num) hpR
    calc
      primeHarmonicMass (railBand n r) ≤
          (r : ℝ) * ((1 : ℝ) / (p : ℝ)) := hmass
      _ ≤ (r : ℝ) * ((1 : ℝ) / 2) :=
        mul_le_mul_of_nonneg_left hrecip (by positivity)
      _ = (r : ℝ) / 2 := by ring
  · simp [harmonicAtomicRailBand, hatomic, primeHarmonicMass]
    positivity

/-- Uniform budget requested only from atom-dominated closed rails. -/
def AtomicRailBudget (B : ℝ) : Prop :=
  ∀ n : ℕ,
    ∑ r ∈ occupiedDepths n, primeHarmonicMass (atomicDepthBand n r) ≤ B

/-- Relative contraction requested only after the raw band has enough rail samples. -/
def DiffuseRailContractionAt (A ρ : ℝ) : Prop :=
  ∀ n r : ℕ,
    primeHarmonicMass (diffuseDepthBand n r) ≤
      A * ρ ^ r * primeHarmonicMass (diffuseRailBand n r)

/-- Harmonic/Mellin envelope for the contracted diffuse carrier. -/
def DiffuseCarrierEnvelope (A ρ D : ℝ) : Prop :=
  ∀ n : ℕ,
    ∑ r ∈ occupiedDepths n,
      A * ρ ^ r * primeHarmonicMass (diffuseRailBand n r) ≤ D

/-- Uniform prime-harmonic mass bound for each populated raw depth band. -/
def UniformDiffuseRailBandEnvelope (H : ℝ) : Prop :=
  ∀ n r : ℕ, primeHarmonicMass (diffuseRailBand n r) ≤ H

/-- Harmonic conversion: a uniform per-band envelope becomes a total Mellin envelope after
geometric contraction. -/
theorem diffuseCarrierEnvelope_of_uniform_band {A ρ H : ℝ}
    (hA : 0 ≤ A) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (hH : 0 ≤ H)
    (hband : UniformDiffuseRailBandEnvelope H) :
    DiffuseCarrierEnvelope A ρ (A * H * (1 - ρ)⁻¹) := by
  intro n
  have hsummable : Summable (fun r : ℕ ↦ ρ ^ r) :=
    summable_geometric_of_lt_one hρ0 hρ1
  have hfinite :
      ∑ r ∈ occupiedDepths n, ρ ^ r ≤ ∑' r : ℕ, ρ ^ r :=
    hsummable.sum_le_tsum (occupiedDepths n) (fun r _ ↦ pow_nonneg hρ0 r)
  calc
    ∑ r ∈ occupiedDepths n,
        A * ρ ^ r * primeHarmonicMass (diffuseRailBand n r) ≤
        ∑ r ∈ occupiedDepths n, A * ρ ^ r * H := by
          apply sum_le_sum
          intro r _
          exact mul_le_mul_of_nonneg_left (hband n r)
            (mul_nonneg hA (pow_nonneg hρ0 r))
    _ = A * H * ∑ r ∈ occupiedDepths n, ρ ^ r := by
          rw [Finset.mul_sum]
          apply sum_congr rfl
          intro r _
          ring
    _ ≤ A * H * ∑' r : ℕ, ρ ^ r :=
          mul_le_mul_of_nonneg_left hfinite (mul_nonneg hA hH)
    _ = A * H * (1 - ρ)⁻¹ := by rw [tsum_geometric_of_lt_one hρ0 hρ1]

/-- Exact adapter theorem: an atomic budget plus a contracted diffuse envelope exports the
uniform Erdős-377 bound. -/
theorem erdos377Bound_of_atomic_diffuse {A ρ B D : ℝ}
    (hatomic : AtomicRailBudget B)
    (hcontract : DiffuseRailContractionAt A ρ)
    (henvelope : DiffuseCarrierEnvelope A ρ D) :
    Erdos377Bound := by
  refine ⟨B + D, ?_⟩
  intro n
  rw [erdos377Mass_eq_sum_depthBandMass]
  calc
    ∑ r ∈ occupiedDepths n, primeHarmonicMass (depthBand n r) =
        ∑ r ∈ occupiedDepths n,
          (primeHarmonicMass (atomicDepthBand n r) +
            primeHarmonicMass (diffuseDepthBand n r)) := by
              apply sum_congr rfl
              intro r _
              exact primeHarmonicMass_depthBand_eq_atomic_add_diffuse n r
    _ = (∑ r ∈ occupiedDepths n, primeHarmonicMass (atomicDepthBand n r)) +
        ∑ r ∈ occupiedDepths n, primeHarmonicMass (diffuseDepthBand n r) := by
          simp only [sum_add_distrib]
    _ ≤ B + ∑ r ∈ occupiedDepths n,
        A * ρ ^ r * primeHarmonicMass (diffuseRailBand n r) := by
          apply add_le_add (hatomic n)
          apply sum_le_sum
          intro r _
          exact hcontract n r
    _ ≤ B + D := by linarith [henvelope n]

/-- Export adapter with the Mellin envelope discharged by the geometric series. -/
theorem erdos377Bound_of_atomic_diffuse_uniform_band {A ρ B H : ℝ}
    (hA : 0 ≤ A) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (hH : 0 ≤ H)
    (hatomic : AtomicRailBudget B)
    (hcontract : DiffuseRailContractionAt A ρ)
    (hband : UniformDiffuseRailBandEnvelope H) :
    Erdos377Bound := by
  exact erdos377Bound_of_atomic_diffuse hatomic hcontract
    (diffuseCarrierEnvelope_of_uniform_band hA hρ0 hρ1 hH hband)

/-! ## Quotient-contour carrier warp

Two compiler-level decompositions of the proposed reflection are used here:

1. keep a quotient packet `m` and reciprocal cell `k` fixed, then solve the phase-reflection
   equation algebraically;
2. specialize the resulting Möbius map to an actual prime point and test whether it remains an
   integer rail.
-/

/-- The exact centered sign of the next dynamic half-cell. -/
noncomputable def dynamicSquareSign (p n j : ℕ) : ℝ :=
  if harmonizedCellPhase p n (j + 1) < harmonizedCircumference p / 2 then 1 else -1

/-- A Boolean half-cell gate is exactly its zeroth mode plus half its square-wave sign. -/
theorem lowerHalfCellGate_eq_half_add_squareSign (p n j : ℕ) :
    lowerHalfCellGate p (harmonizedCellPhase p n (j + 1)) =
      (1 : ℝ) / 2 + (1 : ℝ) / 2 * dynamicSquareSign p n j := by
  rw [lowerHalfCellGate, dynamicSquareSign]
  by_cases hcell : harmonizedCellPhase p n (j + 1) < harmonizedCircumference p / 2
  · simp [hcell]
    norm_num
  · simp [hcell]

/-- Exact one-step signed-ledger recurrence before summing over primes. -/
theorem dynamicClosureWeight_succ_eq_half_add_signed (p n j : ℕ) :
    dynamicClosureWeight p n (j + 1) =
      (1 : ℝ) / 2 * dynamicClosureWeight p n j +
        (1 : ℝ) / 2 * dynamicClosureWeight p n j * dynamicSquareSign p n j := by
  calc
    dynamicClosureWeight p n (j + 1) = dynamicClosureWeight p n j *
        lowerHalfCellGate p (harmonizedCellPhase p n (j + 1)) := by
          simp [dynamicClosureWeight, dynamicSurvivalWeight, prod_range_succ]
    _ = (1 : ℝ) / 2 * dynamicClosureWeight p n j +
        (1 : ℝ) / 2 * dynamicClosureWeight p n j * dynamicSquareSign p n j := by
          rw [lowerHalfCellGate_eq_half_add_squareSign]
          ring

/-- Dynamic harmonic energy restricted to an arbitrary finite prime bank. -/
noncomputable def dynamicBankEnergy (s : Finset ℕ) (n j : ℕ) : ℝ :=
  ∑ p ∈ s, (1 : ℝ) / (p : ℝ) * dynamicClosureWeight p n j

/-- Pointwise closure monotonicity transports through every positive harmonic prime bank. -/
theorem dynamicBankEnergy_succ_le_of_positive_primes
    {s : Finset ℕ} {n j : ℕ} (hpos : ∀ p ∈ s, 0 < p) :
    dynamicBankEnergy s n (j + 1) ≤ dynamicBankEnergy s n j := by
  rw [dynamicBankEnergy, dynamicBankEnergy]
  apply sum_le_sum
  intro p hp
  exact mul_le_mul_of_nonneg_left
    (dynamicClosureWeight_succ_le (hpos p hp)) (by positivity)

/-- Dynamic closure cannot increase the raw harmonic mass of any finite rail bank. -/
theorem dynamicBankEnergy_le_primeHarmonicMass (s : Finset ℕ) (n j : ℕ) :
    dynamicBankEnergy s n j ≤ primeHarmonicMass s := by
  rw [dynamicBankEnergy, primeHarmonicMass]
  apply sum_le_sum
  intro p _
  calc
    (1 : ℝ) / (p : ℝ) * dynamicClosureWeight p n j ≤
        (1 : ℝ) / (p : ℝ) * 1 :=
      mul_le_mul_of_nonneg_left (dynamicClosureWeight_le_one p n j) (by positivity)
    _ = (1 : ℝ) / (p : ℝ) := by ring

/-- Signed square-wave ledger restricted to the same finite prime bank. -/
noncomputable def dynamicBankSignedLedger (s : Finset ℕ) (n j : ℕ) : ℝ :=
  ∑ p ∈ s, (1 : ℝ) / (p : ℝ) * dynamicClosureWeight p n j *
    dynamicSquareSign p n j

/-- Exact harmonic identity: the next energy is half the current energy plus half the signed
ledger. -/
theorem dynamicBankEnergy_succ_eq_half_add_signed (s : Finset ℕ) (n j : ℕ) :
    dynamicBankEnergy s n (j + 1) =
      (1 : ℝ) / 2 * dynamicBankEnergy s n j +
        (1 : ℝ) / 2 * dynamicBankSignedLedger s n j := by
  rw [dynamicBankEnergy, dynamicBankEnergy, dynamicBankSignedLedger]
  calc
    ∑ p ∈ s, (1 : ℝ) / (p : ℝ) * dynamicClosureWeight p n (j + 1) =
        ∑ p ∈ s,
          ((1 : ℝ) / 2 * ((1 : ℝ) / (p : ℝ) * dynamicClosureWeight p n j) +
            (1 : ℝ) / 2 * ((1 : ℝ) / (p : ℝ) * dynamicClosureWeight p n j *
              dynamicSquareSign p n j)) := by
                apply sum_congr rfl
                intro p _
                rw [dynamicClosureWeight_succ_eq_half_add_signed]
                ring
    _ = (1 : ℝ) / 2 * (∑ p ∈ s, (1 : ℝ) / (p : ℝ) * dynamicClosureWeight p n j) +
        (1 : ℝ) / 2 * (∑ p ∈ s, (1 : ℝ) / (p : ℝ) * dynamicClosureWeight p n j *
          dynamicSquareSign p n j) := by
            rw [sum_add_distrib, Finset.mul_sum, Finset.mul_sum]

/-- Algebraic unrolling of an exact half-transfer recurrence.  This fixes the dwell exponent at
`r - j`, including the half-factor paid by the ledger at its own step. -/
theorem halfTransferRecurrence_unroll (energy ledger : ℕ → ℝ)
    (hstep : ∀ j : ℕ, energy (j + 1) =
      (1 : ℝ) / 2 * energy j + (1 : ℝ) / 2 * ledger j) (r : ℕ) :
    energy r = ((1 : ℝ) / 2) ^ r * energy 0 +
      ∑ j ∈ range r, ((1 : ℝ) / 2) ^ (r - j) * ledger j := by
  induction r with
  | zero => simp
  | succ r ih =>
      have hshift :
          ∑ j ∈ range r, ((1 : ℝ) / 2) ^ (r + 1 - j) * ledger j =
            (1 : ℝ) / 2 *
              ∑ j ∈ range r, ((1 : ℝ) / 2) ^ (r - j) * ledger j := by
        rw [Finset.mul_sum]
        apply sum_congr rfl
        intro j hj
        have hjr : j < r := mem_range.mp hj
        have hsub : r + 1 - j = (r - j) + 1 := by omega
        rw [hsub, pow_succ]
        ring
      rw [hstep r, ih, sum_range_succ, hshift]
      norm_num
      ring

/-- The dynamic bank energy is its geometrically vanishing entrance mass plus the exact signed
ledger transported with dwell `2^-(r-j)`. -/
theorem dynamicBankEnergy_eq_vanishingDwell (s : Finset ℕ) (n r : ℕ) :
    dynamicBankEnergy s n r = ((1 : ℝ) / 2) ^ r * dynamicBankEnergy s n 0 +
      ∑ j ∈ range r, ((1 : ℝ) / 2) ^ (r - j) * dynamicBankSignedLedger s n j := by
  exact halfTransferRecurrence_unroll (dynamicBankEnergy s n) (dynamicBankSignedLedger s n)
    (dynamicBankEnergy_succ_eq_half_add_signed s n) r

/-- A depth-`r` raw rail has no relevant carry cell beyond `r+1`. -/
theorem railBand_log_two_mul_lt_depth_add_two {p n r : ℕ} (hmem : p ∈ railBand n r) :
    Nat.log p (2 * n) < r + 2 := by
  have hpPrime := Nat.prime_of_mem_primesLE (mem_filter.mp hmem).1
  have hdepth : Nat.log p n = r := (mem_filter.mp hmem).2
  have hnlt : n < p ^ (r + 1) := by
    simpa [hdepth] using Nat.lt_pow_succ_log_self hpPrime.one_lt n
  have htwo : 2 * n < p ^ (r + 2) := calc
    2 * n < 2 * p ^ (r + 1) := by omega
    _ ≤ p * p ^ (r + 1) := Nat.mul_le_mul_right (p ^ (r + 1)) hpPrime.two_le
    _ = p ^ ((r + 1) + 1) := (pow_succ' p (r + 1)).symm
    _ = p ^ (r + 2) := by congr 1
  have hpMem : p ∈ n.primesLE := (mem_filter.mp hmem).1
  have hnpos : 0 < n := hpPrime.pos.trans_le (Nat.le_of_mem_primesLE hpMem)
  exact Nat.log_lt_of_lt_pow (mul_ne_zero (by norm_num) hnpos.ne') htwo

/-- On a raw depth-`r` rail, closure through `r+1` cells is exactly the original Kummer
selector. -/
theorem railBand_dynamicClosureWeight_eq_ite {p n r : ℕ} (hmem : p ∈ railBand n r) :
    dynamicClosureWeight p n r = if CarryFree p n then 1 else 0 := by
  have hpPrime := Nat.prime_of_mem_primesLE (mem_filter.mp hmem).1
  have hlog := railBand_log_two_mul_lt_depth_add_two hmem
  rw [dynamicClosureWeight_eq_ite]
  have horbit : DynamicClosedOrbit p n (r + 1) ↔ CarryFree p n := calc
    DynamicClosedOrbit p n (r + 1) ↔ CarryFreeThrough p n (r + 2) :=
      dynamicClosedOrbit_iff_carryFreeThrough hpPrime.pos
    _ ↔ ¬p ∣ (2 * n).choose n :=
      (prime_not_dvd_centralBinom_iff_carryFreeThrough hpPrime hlog).symm
    _ ↔ CarryFree p n := prime_not_dvd_centralBinom_iff_carryFree hpPrime
  exact if_congr horbit rfl rfl

/-- Terminal dynamic energy on one raw depth band is exactly the carry-free harmonic mass of
that band. -/
theorem dynamicBankEnergy_railBand_terminal_eq_depthBandMass (n r : ℕ) :
    dynamicBankEnergy (railBand n r) n r = primeHarmonicMass (depthBand n r) := by
  classical
  rw [dynamicBankEnergy, primeHarmonicMass]
  calc
    ∑ p ∈ railBand n r, (1 : ℝ) / (p : ℝ) * dynamicClosureWeight p n r =
        ∑ p ∈ railBand n r, if CarryFree p n then (1 : ℝ) / (p : ℝ) else 0 := by
          apply sum_congr rfl
          intro p hp
          rw [railBand_dynamicClosureWeight_eq_ite hp]
          by_cases hfree : CarryFree p n <;> simp [hfree]
    _ = ∑ p ∈ (railBand n r).filter (CarryFree · n), (1 : ℝ) / (p : ℝ) := by
          rw [sum_filter]
    _ = ∑ p ∈ depthBand n r, (1 : ℝ) / (p : ℝ) := by
          apply sum_congr
          · ext p
            simp only [railBand, depthBand, carryFreePrimes, mem_filter]
            tauto
          · intro p _
            rfl

/-- Terminal energy restricted to the harmonic-atomic raw bank reads exactly the closed atomic
mass. -/
theorem dynamicBankEnergy_harmonicAtomic_terminal_eq_mass (n r : ℕ) :
    dynamicBankEnergy (harmonicAtomicRailBand n r) n r =
      primeHarmonicMass (harmonicAtomicDepthBand n r) := by
  classical
  by_cases h : IsHarmonicAtomicRailBand n r
  · simpa [harmonicAtomicRailBand, harmonicAtomicDepthBand, h] using
      dynamicBankEnergy_railBand_terminal_eq_depthBandMass n r
  · simp [harmonicAtomicRailBand, harmonicAtomicDepthBand, h,
      dynamicBankEnergy, primeHarmonicMass]

/-- Terminal energy restricted to the harmonic-diffuse raw bank reads exactly the closed
diffuse mass. -/
theorem dynamicBankEnergy_harmonicDiffuse_terminal_eq_mass (n r : ℕ) :
    dynamicBankEnergy (harmonicDiffuseRailBand n r) n r =
      primeHarmonicMass (harmonicDiffuseDepthBand n r) := by
  classical
  by_cases h : IsHarmonicAtomicRailBand n r
  · simp [harmonicDiffuseRailBand, harmonicDiffuseDepthBand, h,
      dynamicBankEnergy, primeHarmonicMass]
  · simpa [harmonicDiffuseRailBand, harmonicDiffuseDepthBand, h] using
      dynamicBankEnergy_railBand_terminal_eq_depthBandMass n r

/-- Stop the diffuse transfer one cell before terminal closure.  Monotonicity pays for the
omitted terminal square-wave packet without estimating that packet. -/
theorem dynamicBankEnergy_harmonicDiffuse_terminal_le_preterminal
    {n r : ℕ} (hr : 0 < r) :
    dynamicBankEnergy (harmonicDiffuseRailBand n r) n r ≤
      dynamicBankEnergy (harmonicDiffuseRailBand n r) n (r - 1) := by
  have hpos : ∀ p ∈ harmonicDiffuseRailBand n r, 0 < p := by
    intro p hp
    have hrail : p ∈ railBand n r :=
      harmonicDiffuseRailBand_subset_railBand n r hp
    exact (Nat.prime_of_mem_primesLE (mem_filter.mp hrail).1).pos
  have hstep := dynamicBankEnergy_succ_le_of_positive_primes
    (s := harmonicDiffuseRailBand n r) (n := n) (j := r - 1) hpos
  simpa [Nat.sub_add_cancel hr] using hstep

/-- The closed diffuse harmonic mass is bounded by its preterminal survivor energy. -/
theorem primeHarmonicMass_harmonicDiffuseDepthBand_le_preterminal
    {n r : ℕ} (hr : 0 < r) :
    primeHarmonicMass (harmonicDiffuseDepthBand n r) ≤
      dynamicBankEnergy (harmonicDiffuseRailBand n r) n (r - 1) := by
  rw [← dynamicBankEnergy_harmonicDiffuse_terminal_eq_mass]
  exact dynamicBankEnergy_harmonicDiffuse_terminal_le_preterminal hr

/-- Exact global harmonic conversion: the Erdős ledger is the sum of the vanishing entrance
mass and signed quotient ledger on each occupied depth. -/
theorem erdos377Mass_eq_sum_vanishingDwell (n : ℕ) :
    erdos377Mass n =
      ∑ r ∈ occupiedDepths n,
        (((1 : ℝ) / 2) ^ r * dynamicBankEnergy (railBand n r) n 0 +
          ∑ j ∈ range r, ((1 : ℝ) / 2) ^ (r - j) *
            dynamicBankSignedLedger (railBand n r) n j) := by
  rw [erdos377Mass_eq_sum_depthBandMass]
  apply sum_congr rfl
  intro r _
  rw [← dynamicBankEnergy_railBand_terminal_eq_depthBandMass]
  exact dynamicBankEnergy_eq_vanishingDwell (railBand n r) n r

/-- Exact terminal-energy split on the harmonically normalized atomic/diffuse banks. -/
theorem erdos377Mass_eq_sum_harmonicAtomicDiffuseEnergy (n : ℕ) :
    erdos377Mass n =
      ∑ r ∈ occupiedDepths n,
        (dynamicBankEnergy (harmonicAtomicRailBand n r) n r +
          dynamicBankEnergy (harmonicDiffuseRailBand n r) n r) := by
  rw [erdos377Mass_eq_sum_depthBandMass]
  apply sum_congr rfl
  intro r _
  rw [dynamicBankEnergy_harmonicAtomic_terminal_eq_mass,
    dynamicBankEnergy_harmonicDiffuse_terminal_eq_mass]
  exact primeHarmonicMass_depthBand_eq_harmonicAtomic_add_diffuse n r

/-- Exact dwell decomposition after the harmonic concentration split. -/
theorem erdos377Mass_eq_sum_harmonicAtomicDiffuseDwell (n : ℕ) :
    erdos377Mass n =
      ∑ r ∈ occupiedDepths n,
        ((((1 : ℝ) / 2) ^ r * dynamicBankEnergy (harmonicAtomicRailBand n r) n 0 +
            ∑ j ∈ range r, ((1 : ℝ) / 2) ^ (r - j) *
              dynamicBankSignedLedger (harmonicAtomicRailBand n r) n j) +
          (((1 : ℝ) / 2) ^ r * dynamicBankEnergy (harmonicDiffuseRailBand n r) n 0 +
            ∑ j ∈ range r, ((1 : ℝ) / 2) ^ (r - j) *
              dynamicBankSignedLedger (harmonicDiffuseRailBand n r) n j)) := by
  rw [erdos377Mass_eq_sum_harmonicAtomicDiffuseEnergy]
  apply sum_congr rfl
  intro r _
  have hatomic :=
    dynamicBankEnergy_eq_vanishingDwell (harmonicAtomicRailBand n r) n r
  have hdiffuse :=
    dynamicBankEnergy_eq_vanishingDwell (harmonicDiffuseRailBand n r) n r
  rw [hatomic, hdiffuse]

/-- Exact total budget of the depth-weighted harmonic entrance carrier. -/
theorem tsum_depth_mul_dwell_div_two_eq_one :
    (∑' r : ℕ, (r : ℝ) * ((1 : ℝ) / 2) ^ r / 2) = 1 := by
  have h :=
    tsum_coe_mul_geometric_of_norm_lt_one (𝕜 := ℝ) (r := (1 : ℝ) / 2) (by norm_num)
  simp only [div_eq_mul_inv]
  rw [tsum_mul_right]
  norm_num at h ⊢
  rw [h]
  norm_num

/-- Harmonic concentration completely controls the entrance part of the atomic ledger: after
the exact dwell is applied, its total contribution is at most one for every `n`. -/
theorem harmonicAtomicEntranceMass_le_one (n : ℕ) :
    ∑ r ∈ occupiedDepths n,
        ((1 : ℝ) / 2) ^ r * dynamicBankEnergy (harmonicAtomicRailBand n r) n 0 ≤ 1 := by
  have hsummable : Summable (fun r : ℕ ↦ (r : ℝ) * ((1 : ℝ) / 2) ^ r / 2) := by
    exact ((hasSum_coe_mul_geometric_of_norm_lt_one (𝕜 := ℝ)
      (r := (1 : ℝ) / 2) (by norm_num)).summable).div_const 2
  calc
    ∑ r ∈ occupiedDepths n,
        ((1 : ℝ) / 2) ^ r * dynamicBankEnergy (harmonicAtomicRailBand n r) n 0 ≤
        ∑ r ∈ occupiedDepths n, (r : ℝ) * ((1 : ℝ) / 2) ^ r / 2 := by
          apply sum_le_sum
          intro r _
          have hdwell : 0 ≤ ((1 : ℝ) / 2) ^ r := by positivity
          calc
            ((1 : ℝ) / 2) ^ r *
                dynamicBankEnergy (harmonicAtomicRailBand n r) n 0 ≤
                ((1 : ℝ) / 2) ^ r *
                  primeHarmonicMass (harmonicAtomicRailBand n r) :=
              mul_le_mul_of_nonneg_left
                (dynamicBankEnergy_le_primeHarmonicMass (harmonicAtomicRailBand n r) n 0)
                hdwell
            _ ≤ ((1 : ℝ) / 2) ^ r * ((r : ℝ) / 2) :=
              mul_le_mul_of_nonneg_left
                (primeHarmonicMass_harmonicAtomicRailBand_le_depth_over_two n r) hdwell
            _ = (r : ℝ) * ((1 : ℝ) / 2) ^ r / 2 := by ring
    _ ≤ ∑' r : ℕ, (r : ℝ) * ((1 : ℝ) / 2) ^ r / 2 :=
      hsummable.sum_le_tsum (occupiedDepths n) (fun r _ ↦ by positivity)
    _ = 1 := tsum_depth_mul_dwell_div_two_eq_one

/-- Arithmetic quotient exposed at dynamic step `j`. -/
def quotientPrefix (n j p : ℕ) : ℕ := n / p ^ (j + 1)

/-- Discrete reciprocal-cell index inside a fixed quotient packet. -/
def quotientCellIndex (m p : ℕ) : ℕ := m / p

/-- Digit phase of a quotient packet, normalized to `[0,1)`. -/
noncomputable def quotientDigitPhase (m p : ℕ) : ℝ :=
  ((m % p : ℕ) : ℝ) / (p : ℝ)

/-- Square-wave sign of the quotient digit. -/
noncomputable def quotientDigitSign (m p : ℕ) : ℝ :=
  if 2 * (m % p) < p then 1 else -1

/-- A prior closed orbit identifies the dynamic square wave with the quotient-digit square wave. -/
theorem dynamicSquareSign_eq_quotientDigitSign {p n j : ℕ} (hp : 1 < p)
    (hprevious : harmonizedCellPhase p n j < harmonizedCircumference p / 2) :
    dynamicSquareSign p n j = quotientDigitSign (quotientPrefix n j p) p := by
  have hnext := next_harmonizedCell_closed_iff_digit_le_half hp hprevious
  have hiff :
      harmonizedCellPhase p n (j + 1) < harmonizedCircumference p / 2 ↔
        2 * (quotientPrefix n j p % p) < p := by
    rw [hnext, quotientPrefix, railDigit]
    omega
  rw [dynamicSquareSign, quotientDigitSign]
  by_cases hcell : harmonizedCellPhase p n (j + 1) < harmonizedCircumference p / 2
  · rw [if_pos hcell, if_pos (hiff.mp hcell)]
  · rw [if_neg hcell, if_neg (fun h ↦ hcell (hiff.mpr h))]

/-- Prime rails with fixed arithmetic quotient `m` and reciprocal-cell index `k`. -/
noncomputable def quotientContourPacket (n j m k : ℕ) : Finset ℕ := by
  classical
  exact n.primesLE.filter fun p ↦ quotientPrefix n j p = m ∧ quotientCellIndex m p = k

/-- Lower-half prime rails inside one quotient-contour packet. -/
noncomputable def lowerQuotientContourPacket (n j m k : ℕ) : Finset ℕ := by
  classical
  exact (quotientContourPacket n j m k).filter fun p ↦ 2 * (m % p) < p

/-- Upper-half prime rails inside one quotient-contour packet. -/
noncomputable def upperQuotientContourPacket (n j m k : ℕ) : Finset ℕ := by
  classical
  exact (quotientContourPacket n j m k).filter fun p ↦ ¬2 * (m % p) < p

/-- The complete packet is the disjoint union of its two square-wave orientations. -/
theorem quotientContourPacket_eq_lower_union_upper (n j m k : ℕ) :
    quotientContourPacket n j m k =
      lowerQuotientContourPacket n j m k ∪ upperQuotientContourPacket n j m k := by
  classical
  ext p
  simp only [lowerQuotientContourPacket, upperQuotientContourPacket, mem_union, mem_filter]
  tauto

/-- Exact packet form of warped pairing: its signed ledger is the lower mass minus the upper
mass.  Any packet proof must bound this difference, since there is no pointwise prime
involution. -/
theorem quotientContourPacket_signedLedger_eq_sub (n j m k : ℕ) (w : ℕ → ℝ) :
    ∑ p ∈ quotientContourPacket n j m k, w p * quotientDigitSign m p =
      (∑ p ∈ lowerQuotientContourPacket n j m k, w p) -
        ∑ p ∈ upperQuotientContourPacket n j m k, w p := by
  classical
  rw [lowerQuotientContourPacket, upperQuotientContourPacket, sum_filter, sum_filter,
    ← sum_sub_distrib]
  apply sum_congr rfl
  intro p _
  rw [quotientDigitSign]
  by_cases hlower : 2 * (m % p) < p <;> simp [hlower]

/-- Phase inside the reciprocal quotient cell `k ≤ m / p ≤ k + 1`. -/
noncomputable def quotientContourPhase (m k p : ℝ) : ℝ := m / p - k

/-- Triangular primitive of the centered half-cell square wave. -/
noncomputable def triangularPrimitive (x : ℝ) : ℝ := min x (1 - x)

/-- The lower and upper half-cells have opposite orientations. -/
noncomputable def quotientSquareSign (x : ℝ) : ℝ :=
  if x < (1 : ℝ) / 2 then 1 else -1

/-- Exact reciprocal-cell reflection obtained from `x⁺ = 1 - x`. -/
noncomputable def warpedReflection (m k p : ℝ) : ℝ :=
  m / (2 * k + 1 - m / p)

/-- Pullback density of the quotient phase, with positive orientation. -/
noncomputable def quotientWarpDensity (m p : ℝ) : ℝ := m / p ^ 2

/-- Radon–Nikodym factor converting warped density back to harmonic density. -/
noncomputable def quotientWarpAmplitude (m p : ℝ) : ℝ := p / m

/-- The contour phase has the proposed derivative, including its negative orientation. -/
theorem hasDerivAt_quotientContourPhase {m k p : ℝ} (hp : p ≠ 0) :
    HasDerivAt (quotientContourPhase m k) (-m / p ^ 2) p := by
  change HasDerivAt (fun x : ℝ ↦ m / x - k) (-m / p ^ 2) p
  simpa only [Pi.div_apply, Pi.sub_apply, id_eq, zero_mul, mul_one, zero_sub] using
    ((hasDerivAt_const p m).div (hasDerivAt_id p) hp).sub_const k

/-- The warped density and its amplitude reproduce the original harmonic element exactly. -/
theorem quotientWarpAmplitude_mul_density {m p : ℝ} (hm : m ≠ 0) (hp : p ≠ 0) :
    quotientWarpAmplitude m p * quotientWarpDensity m p = 1 / p := by
  rw [quotientWarpAmplitude, quotientWarpDensity]
  field_simp

/-- The Möbius warp reflects the quotient phase across the midpoint. -/
theorem quotientContourPhase_warpedReflection {m k p : ℝ}
    (hm : m ≠ 0) (hp : p ≠ 0) :
    quotientContourPhase m k (warpedReflection m k p) =
      1 - quotientContourPhase m k p := by
  simp only [quotientContourPhase, warpedReflection]
  field_simp [hm, hp]
  ring

/-- The real contour phase is exactly the normalized residue phase on a discrete quotient cell. -/
theorem quotientContourPhase_eq_quotientDigitPhase {m k p : ℕ} (hp : 0 < p)
    (hcell : quotientCellIndex m p = k) :
    quotientContourPhase (m : ℝ) (k : ℝ) (p : ℝ) = quotientDigitPhase m p := by
  have hcell' : m / p = k := by simpa [quotientCellIndex] using hcell
  have hnat : m = m % p + p * k := by
    calc
      m = m % p + p * (m / p) := (Nat.mod_add_div m p).symm
      _ = m % p + p * k := by rw [hcell']
  have hdecompR : (m : ℝ) = (m % p : ℕ) + (p : ℝ) * (k : ℝ) := by
    exact_mod_cast hnat
  have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne'
  rw [quotientContourPhase, quotientDigitPhase]
  calc
    (m : ℝ) / (p : ℝ) - (k : ℝ) =
        ((m : ℝ) - (k : ℝ) * (p : ℝ)) / (p : ℝ) := by
          field_simp [hpR]
    _ = ((m % p : ℕ) : ℝ) / (p : ℝ) := by
          rw [hdecompR]
          ring

/-- Away from its pole, the warped reflection is an involution. -/
theorem warpedReflection_involutive {m k p : ℝ}
    (hm : m ≠ 0) (hp : p ≠ 0) :
    warpedReflection m k (warpedReflection m k p) = p := by
  simp only [warpedReflection]
  field_simp [hm, hp]
  ring

/-- The zero-phase endpoint of reciprocal cell `k`. -/
noncomputable def quotientCellZeroEndpoint (m k : ℝ) : ℝ := m / k

/-- The one-phase endpoint of reciprocal cell `k`. -/
noncomputable def quotientCellOneEndpoint (m k : ℝ) : ℝ := m / (k + 1)

/-- Midpoint where the quotient square wave changes sign. -/
noncomputable def quotientCellMidpoint (m k : ℝ) : ℝ := 2 * m / (2 * k + 1)

/-- Exact complete-cell harmonic residual after triangular reflection. -/
noncomputable def harmonicContourResidual (k : ℝ) : ℝ :=
  Real.log (1 + 1 / (4 * k * (k + 1)))

/-- A complete reciprocal contour begins at triangular potential zero. -/
theorem triangularPrimitive_zero : triangularPrimitive 0 = 0 := by
  norm_num [triangularPrimitive]

/-- A complete reciprocal contour ends at the same triangular potential. -/
theorem triangularPrimitive_one : triangularPrimitive 1 = 0 := by
  norm_num [triangularPrimitive]

/-- The phase at the zero endpoint is exactly zero. -/
theorem quotientContourPhase_zeroEndpoint {m k : ℝ} (hm : m ≠ 0) :
    quotientContourPhase m k (quotientCellZeroEndpoint m k) = 0 := by
  simp only [quotientContourPhase, quotientCellZeroEndpoint]
  field_simp [hm]
  ring

/-- The phase at the other endpoint is exactly one. -/
theorem quotientContourPhase_oneEndpoint {m k : ℝ}
    (hm : m ≠ 0) :
    quotientContourPhase m k (quotientCellOneEndpoint m k) = 1 := by
  simp only [quotientContourPhase, quotientCellOneEndpoint]
  field_simp [hm]
  ring

/-- Amplitude variation over one complete reciprocal cell is the telescoping quantity
`1 / (k(k+1))`. -/
theorem quotientWarpAmplitude_endpoint_distortion {m k : ℝ}
    (hm : m ≠ 0) (hk : k ≠ 0) (hks : k + 1 ≠ 0) :
    quotientWarpAmplitude m (quotientCellZeroEndpoint m k) -
        quotientWarpAmplitude m (quotientCellOneEndpoint m k) =
      1 / (k * (k + 1)) := by
  simp only [quotientWarpAmplitude, quotientCellZeroEndpoint, quotientCellOneEndpoint]
  field_simp [hm, hk, hks]
  ring

/-- The quotient of the lower and upper harmonic endpoint ratios is independent of the packet
height `m`. -/
theorem quotientCell_endpointRatio_eq {m k : ℝ} (hm : m ≠ 0) (hk : k ≠ 0)
    (hks : k + 1 ≠ 0) :
    (quotientCellZeroEndpoint m k / quotientCellMidpoint m k) /
        (quotientCellMidpoint m k / quotientCellOneEndpoint m k) =
      1 + 1 / (4 * k * (k + 1)) := by
  simp only [quotientCellZeroEndpoint, quotientCellOneEndpoint, quotientCellMidpoint]
  field_simp [hm, hk, hks]
  ring

/-- The two logarithmic half-cell increments differ by exactly the reflected harmonic residual.
This is the continuous Mellin adapter behind the reciprocal-cell warp. -/
theorem quotientCell_logClockDefect_eq_harmonicContourResidual
    {m k : ℝ} (hm : 0 < m) (hk : 0 < k) :
    (Real.log (quotientCellZeroEndpoint m k) -
        Real.log (quotientCellMidpoint m k)) -
      (Real.log (quotientCellMidpoint m k) -
        Real.log (quotientCellOneEndpoint m k)) =
      harmonicContourResidual k := by
  have hzero : 0 < quotientCellZeroEndpoint m k := by
    simp only [quotientCellZeroEndpoint]
    positivity
  have hone : 0 < quotientCellOneEndpoint m k := by
    simp only [quotientCellOneEndpoint]
    positivity
  have hmid : 0 < quotientCellMidpoint m k := by
    simp only [quotientCellMidpoint]
    positivity
  rw [harmonicContourResidual,
    ← quotientCell_endpointRatio_eq hm.ne' hk.ne' (by positivity)]
  rw [Real.log_div (div_ne_zero hzero.ne' hmid.ne') (div_ne_zero hmid.ne' hone.ne'),
    Real.log_div hzero.ne' hmid.ne', Real.log_div hmid.ne' hone.ne']

/-- A complete continuous contour cell has nonnegative residual bounded by its telescoping
amplitude distortion. -/
theorem harmonicContourResidual_nonneg_le {k : ℝ} (hk : 0 < k) :
    0 ≤ harmonicContourResidual k ∧
      harmonicContourResidual k ≤ 1 / (4 * k * (k + 1)) := by
  have hx : 0 ≤ 1 / (4 * k * (k + 1)) := by positivity
  have hxpos : 0 < 1 + 1 / (4 * k * (k + 1)) := by linarith
  constructor
  · rw [harmonicContourResidual]
    exact Real.log_nonneg (by linarith)
  · rw [harmonicContourResidual]
    have hlog := Real.log_le_sub_one_of_pos hxpos
    linarith

/-- The full finite budget of reciprocal-cell amplitude variations telescopes exactly. -/
theorem sum_range_reciprocal_cell_distortion (K : ℕ) :
    ∑ k ∈ range K,
        1 / (((k + 1 : ℕ) : ℝ) * ((k + 2 : ℕ) : ℝ)) =
      1 - 1 / ((K + 1 : ℕ) : ℝ) := by
  induction K with
  | zero => norm_num
  | succ K ih =>
      rw [sum_range_succ, ih]
      push_cast
      field_simp
      ring

/-- All complete continuous quotient cells together consume at most one quarter unit of harmonic
mass. -/
theorem sum_range_harmonicContourResidual_le_quarter (K : ℕ) :
    ∑ k ∈ range K, harmonicContourResidual ((k + 1 : ℕ) : ℝ) ≤ (1 : ℝ) / 4 := by
  calc
    ∑ k ∈ range K, harmonicContourResidual ((k + 1 : ℕ) : ℝ) ≤
        ∑ k ∈ range K,
          1 / (4 * ((k + 1 : ℕ) : ℝ) * ((k + 2 : ℕ) : ℝ)) := by
            apply sum_le_sum
            intro k _
            have hk := (harmonicContourResidual_nonneg_le
              (show (0 : ℝ) < ((k + 1 : ℕ) : ℝ) by positivity)).2
            have hsucc : (((k + 1 : ℕ) : ℝ) + 1) = ((k + 2 : ℕ) : ℝ) := by
              push_cast
              ring
            rw [hsucc] at hk
            exact hk
    _ = (1 : ℝ) / 4 *
        ∑ k ∈ range K,
          1 / (((k + 1 : ℕ) : ℝ) * ((k + 2 : ℕ) : ℝ)) := by
            rw [Finset.mul_sum]
            apply sum_congr rfl
            intro k _
            field_simp
    _ = (1 : ℝ) / 4 * (1 - 1 / ((K + 1 : ℕ) : ℝ)) := by
          rw [sum_range_reciprocal_cell_distortion]
    _ ≤ (1 : ℝ) / 4 := by
          have hrecip : 0 ≤ (1 : ℝ) / ((K + 1 : ℕ) : ℝ) := by positivity
          linarith

/-- Positive reciprocal-cell indices carry the same quarter-unit residual budget. -/
theorem sum_Ico_harmonicContourResidual_le_quarter (K : ℕ) :
    ∑ k ∈ Ico 1 (K + 1), harmonicContourResidual (k : ℝ) ≤ (1 : ℝ) / 4 := by
  rw [Finset.sum_Ico_eq_sum_range]
  simpa [add_comm] using sum_range_harmonicContourResidual_le_quarter K

/-- After every cell is placed on the same logarithmic carrier, the complete-contour clock
defects have the exact summable budget `(1/4) * 2⁻ʳ`. -/
theorem sum_range_scaled_quotientCell_logClockDefect_le_quarter
    (m : ℝ) (hm : 0 < m) (r K : ℕ) :
    ∑ k ∈ range K,
        ((1 : ℝ) / 2) ^ r *
          ((Real.log (quotientCellZeroEndpoint m ((k + 1 : ℕ) : ℝ)) -
              Real.log (quotientCellMidpoint m ((k + 1 : ℕ) : ℝ))) -
            (Real.log (quotientCellMidpoint m ((k + 1 : ℕ) : ℝ)) -
              Real.log (quotientCellOneEndpoint m ((k + 1 : ℕ) : ℝ)))) ≤
      (1 : ℝ) / 4 * ((1 : ℝ) / 2) ^ r := by
  have hdwell : 0 ≤ ((1 : ℝ) / 2) ^ r := by positivity
  calc
    _ = ((1 : ℝ) / 2) ^ r *
        ∑ k ∈ range K, harmonicContourResidual ((k + 1 : ℕ) : ℝ) := by
          rw [Finset.mul_sum]
          apply sum_congr rfl
          intro k _
          rw [quotientCell_logClockDefect_eq_harmonicContourResidual hm (by positivity)]
    _ ≤ ((1 : ℝ) / 2) ^ r * ((1 : ℝ) / 4) :=
      mul_le_mul_of_nonneg_left (sum_range_harmonicContourResidual_le_quarter K) hdwell
    _ = (1 : ℝ) / 4 * ((1 : ℝ) / 2) ^ r := by ring

/-- The exact reflection of the prime point `p = 3` in packet `(m,k) = (10,3)`. -/
theorem warpedReflection_ten_three_three : warpedReflection 10 3 3 = (30 : ℝ) / 11 := by
  norm_num [warpedReflection]

/-- The quotient reflection does not define an involution on integer, hence prime, rails. -/
theorem warpedReflection_not_integer_example :
    ¬ ∃ q : ℕ, (q : ℝ) = warpedReflection 10 3 3 := by
  rintro ⟨q, hq⟩
  rw [warpedReflection_ten_three_three] at hq
  have hq2 : 2 < q := by
    exact_mod_cast (show (2 : ℝ) < q by rw [hq]; norm_num)
  have hq3 : q < 3 := by
    exact_mod_cast (show (q : ℝ) < 3 by rw [hq]; norm_num)
  omega

/-! ## Discrete warped variation and Stieltjes transfer

The proposed warped variation is made finite and ordered here.  The order parameter is the mesh
index after quotient packets have been sorted along their warped contour.  Its discrete derivative
is the quantity consumed by Abel summation.
-/

/-- Total variation of a scalar carrier on its first `M` warped mesh edges. -/
noncomputable def warpedMeshVariation (w : ℕ → ℝ) (M : ℕ) : ℝ :=
  ∑ i ∈ range M, |w (i + 1) - w i|

/-- Mesh variation is nonnegative. -/
theorem warpedMeshVariation_nonneg (w : ℕ → ℝ) (M : ℕ) :
    0 ≤ warpedMeshVariation w M := by
  exact sum_nonneg fun _ _ ↦ abs_nonneg _

/-- A depth dwell factor pulls exactly through warped total variation. -/
theorem warpedMeshVariation_const_mul (c : ℝ) (w : ℕ → ℝ) (M : ℕ) :
    warpedMeshVariation (fun i ↦ c * w i) M = |c| * warpedMeshVariation w M := by
  simp only [warpedMeshVariation]
  calc
    ∑ i ∈ range M, |c * w (i + 1) - c * w i| =
        ∑ i ∈ range M, |c| * |w (i + 1) - w i| := by
          apply sum_congr rfl
          intro i _
          rw [← mul_sub, abs_mul]
    _ = |c| * ∑ i ∈ range M, |w (i + 1) - w i| := by
          rw [Finset.mul_sum]

/-- Finite prime-counting Stieltjes estimate.  If `a` is the discrepancy increment and its
partial sums are `B`-bounded, then a carrier of modulus `W` and warped variation `V` has sampling
error at most `B(W+V)`. -/
theorem discreteStieltjesVariationBound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (a : ℕ → E) (w : ℕ → ℝ) {B W V : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ k, ‖∑ i ∈ range k, a i‖ ≤ B) (hW : ∀ i, ‖w i‖ ≤ W)
    (hV : ∀ M, warpedMeshVariation w M ≤ V) :
    ∀ M, ‖∑ i ∈ range M, w i • a i‖ ≤ B * W + B * V := by
  have hW0 : 0 ≤ W := le_trans (norm_nonneg _) (hW 0)
  intro M
  rw [Finset.sum_range_by_parts w a M]
  refine (norm_sub_le _ _).trans (add_le_add ?_ ?_)
  · rw [norm_smul]
    calc
      ‖w (M - 1)‖ * ‖∑ i ∈ range M, a i‖ ≤ W * B :=
        mul_le_mul (hW _) (hB M) (norm_nonneg _) hW0
      _ = B * W := mul_comm W B
  · calc
      ‖∑ i ∈ range (M - 1),
          (w (i + 1) - w i) • ∑ j ∈ range (i + 1), a j‖ ≤
          ∑ i ∈ range (M - 1),
            ‖(w (i + 1) - w i) • ∑ j ∈ range (i + 1), a j‖ := norm_sum_le _ _
      _ ≤ ∑ i ∈ range (M - 1), ‖w (i + 1) - w i‖ * B := by
            apply sum_le_sum
            intro i _
            rw [norm_smul]
            exact mul_le_mul_of_nonneg_left (hB (i + 1)) (norm_nonneg _)
      _ = B * warpedMeshVariation w (M - 1) := by
            simp only [warpedMeshVariation, Real.norm_eq_abs]
            rw [← Finset.sum_mul, mul_comm]
      _ ≤ B * V := mul_le_mul_of_nonneg_left (hV (M - 1)) hB0

/-- If the unscaled reflected carrier has uniformly bounded modulus and variation, the vanishing
dwell factor gives the proposed `2⁻ʳ` Stieltjes discrepancy exactly. -/
theorem discreteStieltjes_depth_decay {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (a : ℕ → E) (v : ℕ → ℝ) {B C : ℝ} (hB0 : 0 ≤ B) (_hC0 : 0 ≤ C)
    (hB : ∀ k, ‖∑ i ∈ range k, a i‖ ≤ B) (hmod : ∀ i, ‖v i‖ ≤ C)
    (hvar : ∀ M, warpedMeshVariation v M ≤ C) :
    ∀ r M,
      ‖∑ i ∈ range M, ((((1 : ℝ) / 2) ^ r) * v i) • a i‖ ≤
        2 * B * C * ((1 : ℝ) / 2) ^ r := by
  intro r M
  have hhalf : 0 ≤ ((1 : ℝ) / 2) ^ r := by positivity
  have hW : ∀ i, ‖(((1 : ℝ) / 2) ^ r) * v i‖ ≤ ((1 : ℝ) / 2) ^ r * C := by
    intro i
    rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg hhalf]
    exact mul_le_mul_of_nonneg_left (hmod i) hhalf
  have hV : ∀ N,
      warpedMeshVariation (fun i ↦ ((1 : ℝ) / 2) ^ r * v i) N ≤
        ((1 : ℝ) / 2) ^ r * C := by
    intro N
    rw [warpedMeshVariation_const_mul, abs_of_nonneg hhalf]
    exact mul_le_mul_of_nonneg_left (hvar N) hhalf
  have h := discreteStieltjesVariationBound a
    (fun i ↦ ((1 : ℝ) / 2) ^ r * v i) hB0 hB hW hV M
  calc
    ‖∑ i ∈ range M, ((((1 : ℝ) / 2) ^ r) * v i) • a i‖ ≤
        B * (((1 : ℝ) / 2) ^ r * C) + B * (((1 : ℝ) / 2) ^ r * C) := h
    _ = 2 * B * C * ((1 : ℝ) / 2) ^ r := by ring

/-- The finite depth sum of the vanishing dwell factors is at most two. -/
theorem sum_range_half_pow_le_two (R : ℕ) :
    ∑ r ∈ range R, ((1 : ℝ) / 2) ^ r ≤ 2 := by
  have hgeom : ∑ r ∈ range R, ((1 : ℝ) / 2) ^ r =
      2 * (1 - ((1 : ℝ) / 2) ^ R) := by
    induction R with
    | zero => norm_num
    | succ R ih =>
        rw [sum_range_succ, ih, pow_succ]
        ring
  rw [hgeom]
  have hpow : 0 ≤ ((1 : ℝ) / 2) ^ R := by positivity
  linarith

/-- Reversing the preterminal dwell clock removes its missing zeroth term, so its total mass is
at most one. -/
theorem sum_range_preterminal_half_pow_le_one (r : ℕ) :
    ∑ j ∈ range (r - 1), ((1 : ℝ) / 2) ^ (r - 1 - j) ≤ 1 := by
  calc
    (∑ j ∈ range (r - 1), ((1 : ℝ) / 2) ^ (r - 1 - j)) =
        (1 : ℝ) / 2 *
          ∑ j ∈ range (r - 1), ((1 : ℝ) / 2) ^ ((r - 1) - 1 - j) := by
            rw [Finset.mul_sum]
            apply sum_congr rfl
            intro j hj
            have hjlt : j < r - 1 := mem_range.mp hj
            have hexp : r - 1 - j = ((r - 1) - 1 - j) + 1 := by omega
            rw [hexp, pow_succ]
            ring
    _ = (1 : ℝ) / 2 *
        ∑ j ∈ range (r - 1), ((1 : ℝ) / 2) ^ j := by
          rw [Finset.sum_range_reflect]
    _ ≤ (1 : ℝ) / 2 * 2 :=
      mul_le_mul_of_nonneg_left (sum_range_half_pow_le_two (r - 1)) (by norm_num)
    _ = 1 := by norm_num

/-- Arbitrarily changing packet heights and mesh lengths does not change the total harmonic
clock-defect budget: after dwell scaling, all continuous quotient contours together cost at most
one half-unit. -/
theorem sum_depth_scaled_quotientCell_logClockDefect_le_half
    (packetHeight : ℕ → ℝ) (meshSize : ℕ → ℕ)
    (hheight : ∀ r, 0 < packetHeight r) (R : ℕ) :
    ∑ r ∈ range R,
      ∑ k ∈ range (meshSize r),
        ((1 : ℝ) / 2) ^ r *
          ((Real.log
                (quotientCellZeroEndpoint (packetHeight r) ((k + 1 : ℕ) : ℝ)) -
              Real.log
                (quotientCellMidpoint (packetHeight r) ((k + 1 : ℕ) : ℝ))) -
            (Real.log
                (quotientCellMidpoint (packetHeight r) ((k + 1 : ℕ) : ℝ)) -
              Real.log
                (quotientCellOneEndpoint (packetHeight r) ((k + 1 : ℕ) : ℝ)))) ≤
      (1 : ℝ) / 2 := by
  calc
    _ ≤ ∑ r ∈ range R, (1 : ℝ) / 4 * ((1 : ℝ) / 2) ^ r := by
      apply sum_le_sum
      intro r _
      exact sum_range_scaled_quotientCell_logClockDefect_le_quarter
        (packetHeight r) (hheight r) r (meshSize r)
    _ = (1 : ℝ) / 4 * ∑ r ∈ range R, ((1 : ℝ) / 2) ^ r := by
      rw [Finset.mul_sum]
    _ ≤ (1 : ℝ) / 4 * 2 :=
      mul_le_mul_of_nonneg_left (sum_range_half_pow_le_two R) (by norm_num)
    _ = (1 : ℝ) / 2 := by ring

/-- A `2⁻ʳ` Stieltjes discrepancy is summable over all finite depth truncations. -/
theorem sum_depth_stieltjesDiscrepancy_le (D : ℕ → ℝ) {B C : ℝ}
    (hB0 : 0 ≤ B) (hC0 : 0 ≤ C)
    (hD : ∀ r, |D r| ≤ 2 * B * C * ((1 : ℝ) / 2) ^ r) (R : ℕ) :
    ∑ r ∈ range R, |D r| ≤ 4 * B * C := by
  calc
    ∑ r ∈ range R, |D r| ≤
        ∑ r ∈ range R, 2 * B * C * ((1 : ℝ) / 2) ^ r := by
          exact sum_le_sum fun r _ ↦ hD r
    _ = (2 * B * C) * ∑ r ∈ range R, ((1 : ℝ) / 2) ^ r := by
          rw [Finset.mul_sum]
    _ ≤ (2 * B * C) * 2 := by
          exact mul_le_mul_of_nonneg_left (sum_range_half_pow_le_two R)
            (mul_nonneg (mul_nonneg (by norm_num) hB0) hC0)
    _ = 4 * B * C := by ring

/-! Strategy B checks the raw signed reciprocal kernel.  Total variation counts its every
orientation reversal, so it is not the carrier to which the bounded-variation hypothesis can be
attached. -/

/-- Alternating reciprocal mesh: the simplest discrete square-wave harmonic carrier. -/
noncomputable def alternatingReciprocalKernel (i : ℕ) : ℝ :=
  (-1 : ℝ) ^ i / ((i + 1 : ℕ) : ℝ)

/-- Every square-wave reversal pays the sum of the two adjacent reciprocal amplitudes. -/
theorem alternatingReciprocalKernel_jump (i : ℕ) :
    |alternatingReciprocalKernel (i + 1) - alternatingReciprocalKernel i| =
      1 / ((i + 1 : ℕ) : ℝ) + 1 / ((i + 2 : ℕ) : ℝ) := by
  rw [alternatingReciprocalKernel, alternatingReciprocalKernel]
  push_cast
  rw [pow_succ]
  have hi1 : (0 : ℝ) < i + 1 := by positivity
  have hi2 : (0 : ℝ) < i + 2 := by positivity
  have hsum : (0 : ℝ) < 1 / (i + 1) + 1 / (i + 2) :=
    add_pos (one_div_pos.mpr hi1) (one_div_pos.mpr hi2)
  calc
    |(-1 : ℝ) ^ i * -1 / (i + 1 + 1) - (-1 : ℝ) ^ i / (i + 1)| =
        |(-1 : ℝ) ^ i * (-(1 / (i + 1) + 1 / (i + 2)))| := by
          congr 1
          field_simp
          ring
    _ = 1 / (i + 1) + 1 / (i + 2) := by
          rw [abs_mul, abs_pow, abs_neg, abs_neg, abs_one, one_pow, one_mul,
            abs_of_pos hsum]

/-- Raw square-wave reciprocal variation dominates the harmonic partial sum. -/
theorem harmonic_sum_le_alternatingReciprocalKernel_variation (M : ℕ) :
    (∑ i ∈ range M, (1 / (i + 1) : ℝ)) ≤
      warpedMeshVariation alternatingReciprocalKernel M := by
  rw [warpedMeshVariation]
  apply sum_le_sum
  intro i _
  rw [alternatingReciprocalKernel_jump]
  have hnonneg : (0 : ℝ) ≤ 1 / ((i + 2 : ℕ) : ℝ) := by positivity
  norm_num [Nat.cast_add, Nat.cast_one] at hnonneg ⊢
  linarith

/-- Consequently no uniform constant bounds the warped variation of the raw reciprocal square
wave.  The bounded-variation carrier must be the reflected residual/primitive. -/
theorem alternatingReciprocalKernel_variation_unbounded (C : ℝ) :
    ∃ M, C < warpedMeshVariation alternatingReciprocalKernel M := by
  have hevent : ∀ᶠ M : ℕ in Filter.atTop,
      C < ∑ i ∈ range M, (1 / (i + 1) : ℝ) :=
    Real.tendsto_sum_range_one_div_nat_succ_atTop.eventually (Filter.eventually_gt_atTop C)
  obtain ⟨M, hM⟩ := hevent.exists
  exact ⟨M, hM.trans_le (harmonic_sum_le_alternatingReciprocalKernel_variation M)⟩

/-- The complete-cell reflected residual, indexed by positive reciprocal cells. -/
noncomputable def reflectedResidualKernel (k : ℕ) : ℝ :=
  harmonicContourResidual ((k + 1 : ℕ) : ℝ)

/-- Each edge variation of the reflected residual is charged to twice the telescoping cell
distortion. -/
theorem reflectedResidualKernel_edgeVariation_le (k : ℕ) :
    |reflectedResidualKernel (k + 1) - reflectedResidualKernel k| ≤
      2 * (1 / (((4 : ℝ) * ((k + 1 : ℕ) : ℝ)) * ((k + 2 : ℕ) : ℝ))) := by
  have hk0 := harmonicContourResidual_nonneg_le
    (show (0 : ℝ) < ((k + 1 : ℕ) : ℝ) by positivity)
  have hk1 := harmonicContourResidual_nonneg_le
    (show (0 : ℝ) < ((k + 2 : ℕ) : ℝ) by positivity)
  have hden :
      1 / (((4 : ℝ) * ((k + 2 : ℕ) : ℝ)) * ((k + 3 : ℕ) : ℝ)) ≤
        1 / (((4 : ℝ) * ((k + 1 : ℕ) : ℝ)) * ((k + 2 : ℕ) : ℝ)) := by
    apply one_div_le_one_div_of_le (by positivity)
    push_cast
    nlinarith
  have hk1' : harmonicContourResidual ((k + 2 : ℕ) : ℝ) ≤
      1 / (((4 : ℝ) * ((k + 2 : ℕ) : ℝ)) * ((k + 3 : ℕ) : ℝ)) := by
    convert hk1.2 using 1
    all_goals
      push_cast
      ring
  have hk0' : harmonicContourResidual ((k + 1 : ℕ) : ℝ) ≤
      1 / (((4 : ℝ) * ((k + 1 : ℕ) : ℝ)) * ((k + 2 : ℕ) : ℝ)) := by
    convert hk0.2 using 1
    all_goals
      push_cast
      ring
  have href1 : reflectedResidualKernel (k + 1) =
      harmonicContourResidual ((k + 2 : ℕ) : ℝ) := by
    rw [reflectedResidualKernel]
  have href0 : reflectedResidualKernel k =
      harmonicContourResidual ((k + 1 : ℕ) : ℝ) := rfl
  rw [href1, href0]
  calc
    |harmonicContourResidual ((k + 2 : ℕ) : ℝ) -
        harmonicContourResidual ((k + 1 : ℕ) : ℝ)| ≤
        |harmonicContourResidual ((k + 2 : ℕ) : ℝ)| +
          |harmonicContourResidual ((k + 1 : ℕ) : ℝ)| := by
          simpa only [Real.norm_eq_abs] using
            norm_sub_le (harmonicContourResidual ((k + 2 : ℕ) : ℝ))
              (harmonicContourResidual ((k + 1 : ℕ) : ℝ))
    _ = harmonicContourResidual ((k + 2 : ℕ) : ℝ) +
          harmonicContourResidual ((k + 1 : ℕ) : ℝ) := by
          rw [abs_of_nonneg hk1.1, abs_of_nonneg hk0.1]
    _ ≤ 1 / (((4 : ℝ) * ((k + 1 : ℕ) : ℝ)) * ((k + 2 : ℕ) : ℝ)) +
          1 / (((4 : ℝ) * ((k + 1 : ℕ) : ℝ)) * ((k + 2 : ℕ) : ℝ)) := by
          apply add_le_add
          · exact hk1'.trans hden
          · exact hk0'
    _ = 2 * (1 / (((4 : ℝ) * ((k + 1 : ℕ) : ℝ)) * ((k + 2 : ℕ) : ℝ))) := by ring

/-- The reflected complete-cell carrier has a uniform half-unit warped-variation budget. -/
theorem reflectedResidualKernel_warpedVariation_le_half (M : ℕ) :
    warpedMeshVariation reflectedResidualKernel M ≤ (1 : ℝ) / 2 := by
  calc
    warpedMeshVariation reflectedResidualKernel M ≤
        ∑ k ∈ range M,
          2 * (1 / (((4 : ℝ) * ((k + 1 : ℕ) : ℝ)) * ((k + 2 : ℕ) : ℝ))) := by
            apply sum_le_sum
            intro k _
            exact reflectedResidualKernel_edgeVariation_le k
    _ = (1 : ℝ) / 2 *
        ∑ k ∈ range M,
          1 / (((k + 1 : ℕ) : ℝ) * ((k + 2 : ℕ) : ℝ)) := by
            rw [Finset.mul_sum]
            apply sum_congr rfl
            intro k _
            field_simp
            ring
    _ = (1 : ℝ) / 2 * (1 - 1 / ((M + 1 : ℕ) : ℝ)) := by
          rw [sum_range_reciprocal_cell_distortion]
    _ ≤ (1 : ℝ) / 2 := by
          have hrecip : 0 ≤ (1 : ℝ) / ((M + 1 : ℕ) : ℝ) := by positivity
          linarith

/-- This is the proposed structural estimate on the correct carrier: after multiplying by the
vanishing dwell factor, warped variation is at most `(1/2)·2⁻ʳ`. -/
theorem scaled_reflectedResidualKernel_warpedVariation_decay (r M : ℕ) :
    warpedMeshVariation
        (fun k ↦ ((1 : ℝ) / 2) ^ r * reflectedResidualKernel k) M ≤
      (1 : ℝ) / 2 * ((1 : ℝ) / 2) ^ r := by
  have hhalf : 0 ≤ ((1 : ℝ) / 2) ^ r := by positivity
  rw [warpedMeshVariation_const_mul, abs_of_nonneg hhalf]
  calc
    ((1 : ℝ) / 2) ^ r * warpedMeshVariation reflectedResidualKernel M ≤
        ((1 : ℝ) / 2) ^ r * ((1 : ℝ) / 2) :=
          mul_le_mul_of_nonneg_left (reflectedResidualKernel_warpedVariation_le_half M) hhalf
    _ = (1 : ℝ) / 2 * ((1 : ℝ) / 2) ^ r := by ring

/-- The reflected residual also has half-unit modulus, providing the endpoint term required by
the finite Stieltjes estimate. -/
theorem norm_reflectedResidualKernel_le_half (k : ℕ) :
    ‖reflectedResidualKernel k‖ ≤ (1 : ℝ) / 2 := by
  have hk := harmonicContourResidual_nonneg_le
    (show (0 : ℝ) < ((k + 1 : ℕ) : ℝ) by positivity)
  have hk' : harmonicContourResidual ((k + 1 : ℕ) : ℝ) ≤
      1 / (((4 : ℝ) * ((k + 1 : ℕ) : ℝ)) * ((k + 2 : ℕ) : ℝ)) := by
    convert hk.2 using 1
    all_goals
      push_cast
      ring
  rw [Real.norm_eq_abs, abs_of_nonneg]
  · calc
      reflectedResidualKernel k ≤
          1 / (((4 : ℝ) * ((k + 1 : ℕ) : ℝ)) * ((k + 2 : ℕ) : ℝ)) := by
            simpa [reflectedResidualKernel] using hk'
      _ ≤ (1 : ℝ) / 2 := by
            apply one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2)
            push_cast
            nlinarith [sq_nonneg (k : ℝ)]
  · simpa [reflectedResidualKernel] using hk.1

/-- Stieltjes sampling of the reflected residual costs exactly one bounded-prime-primitive unit
times `2⁻ʳ`. -/
theorem reflectedResidualKernel_stieltjes_depth_decay {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (a : ℕ → E) {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ k, ‖∑ i ∈ range k, a i‖ ≤ B) :
    ∀ r M,
      ‖∑ i ∈ range M,
          ((((1 : ℝ) / 2) ^ r) * reflectedResidualKernel i) • a i‖ ≤
        B * ((1 : ℝ) / 2) ^ r := by
  intro r M
  have h := discreteStieltjes_depth_decay a reflectedResidualKernel hB0
    (show (0 : ℝ) ≤ (1 : ℝ) / 2 by norm_num) hB norm_reflectedResidualKernel_le_half
    reflectedResidualKernel_warpedVariation_le_half r M
  calc
    ‖∑ i ∈ range M,
        ((((1 : ℝ) / 2) ^ r) * reflectedResidualKernel i) • a i‖ ≤
      2 * B * ((1 : ℝ) / 2) * ((1 : ℝ) / 2) ^ r := h
    _ = B * ((1 : ℝ) / 2) ^ r := by ring

/-- The reflected-residual sampling discrepancy has a uniform two-unit total depth budget. -/
theorem sum_depth_reflectedResidualDiscrepancy_le (D : ℕ → ℝ) {B : ℝ}
    (hB0 : 0 ≤ B) (hD : ∀ r, |D r| ≤ B * ((1 : ℝ) / 2) ^ r) (R : ℕ) :
    ∑ r ∈ range R, |D r| ≤ 2 * B := by
  calc
    ∑ r ∈ range R, |D r| ≤
        ∑ r ∈ range R, B * ((1 : ℝ) / 2) ^ r := by
          exact sum_le_sum fun r _ ↦ hD r
    _ = B * ∑ r ∈ range R, ((1 : ℝ) / 2) ^ r := by rw [Finset.mul_sum]
    _ ≤ B * 2 := mul_le_mul_of_nonneg_left (sum_range_half_pow_le_two R) hB0
    _ = 2 * B := by ring

/-! ## Parity rails and the exact prime-cell second difference

The small-prime adapter uses the quotient parity of `2n`.  It avoids Fourier truncation: a carry
is exactly the odd correction to the doubled quotient.  On a fixed reciprocal cell the correction
changes orientation once, at its harmonic midpoint.
-/

/-- Doubling a Euclidean division produces an even quotient plus its single carry bit. -/
theorem double_div_eq_two_mul_div_add_carryBit {n q : ℕ} (hq : 0 < q) :
    (2 * n) / q = 2 * (n / q) + if q ≤ 2 * (n % q) then 1 else 0 := by
  have hr : n % q < q := Nat.mod_lt n hq
  have hdecomp : (2 * n) / q = (2 * (n % q)) / q + 2 * (n / q) := by
    calc
      (2 * n) / q = (2 * (n % q) + q * (2 * (n / q))) / q := by
        congr 1
        nth_rw 1 [← Nat.mod_add_div n q]
        ring
      _ = (2 * (n % q)) / q + 2 * (n / q) := Nat.add_mul_div_left _ _ hq
  by_cases hcarry : q ≤ 2 * (n % q)
  · have hdigit : (2 * (n % q)) / q = 1 := by
      apply Nat.div_eq_of_lt_le
      · simpa using hcarry
      · omega
    rw [hdecomp, if_pos hcarry, hdigit]
    omega
  · have hnocarry : 2 * (n % q) < q := by omega
    rw [hdecomp, if_neg hcarry, Nat.div_eq_of_lt hnocarry]
    omega

/-- A carry-free level is exactly an even quotient on the doubled lacunary orbit. -/
theorem noCarryAt_iff_even_doubleQuotient {n q : ℕ} (hq : 0 < q) :
    2 * (n % q) < q ↔ Even ((2 * n) / q) := by
  rw [double_div_eq_two_mul_div_add_carryBit hq]
  by_cases hcarry : q ≤ 2 * (n % q)
  · rw [if_pos hcarry]
    constructor
    · intro h
      omega
    · intro heven
      exfalso
      exact (Nat.not_even_two_mul_add_one (n / q)) (by simpa [add_comm] using heven)
  · rw [if_neg hcarry]
    constructor
    · exact fun _ ↦ ⟨n / q, by omega⟩
    · omega

/-- Kummer closure through `b` is the even-parity orbit of all doubled power quotients. -/
theorem carryFreeThrough_iff_evenQuotientOrbit {p n b : ℕ} (hp : 0 < p) :
    CarryFreeThrough p n b ↔
      ∀ i ∈ Ico 1 b, Even ((2 * n) / p ^ i) := by
  constructor
  · intro h i hi
    exact (noCarryAt_iff_even_doubleQuotient (pow_pos hp i)).mp (h i hi)
  · intro h i hi
    exact (noCarryAt_iff_even_doubleQuotient (pow_pos hp i)).mpr (h i hi)

/-- Exact parity-rail form of the central-binomial nondivisor condition. -/
theorem prime_not_dvd_centralBinom_iff_evenQuotientOrbit {p n b : ℕ} (hp : p.Prime)
    (hb : Nat.log p (2 * n) < b) :
    ¬p ∣ (2 * n).choose n ↔
      ∀ i ∈ Ico 1 b, Even ((2 * n) / p ^ i) := by
  rw [prime_not_dvd_centralBinom_iff_carryFreeThrough hp hb,
    carryFreeThrough_iff_evenQuotientOrbit hp.pos]

/-- Inside reciprocal cell `k = ⌊m/p⌋`, the lower digit half is exactly the portion above the
harmonic midpoint `2m/(2k+1)`. -/
theorem quotientDigit_lower_iff_midpoint {m k p : ℕ} (hcell : quotientCellIndex m p = k) :
    2 * (m % p) < p ↔ 2 * m < (2 * k + 1) * p := by
  have hm := Nat.mod_add_div m p
  rw [quotientCellIndex] at hcell
  rw [hcell] at hm
  have hmidform : (2 * k + 1) * p = 2 * (p * k) + p := by ring
  omega

/-- The arithmetic square wave is the sign of the exact midpoint comparison. -/
theorem quotientDigitSign_eq_midpointSign {m k p : ℕ}
    (hcell : quotientCellIndex m p = k) :
    quotientDigitSign m p = if 2 * m < (2 * k + 1) * p then 1 else -1 := by
  rw [quotientDigitSign]
  exact if_congr (quotientDigit_lower_iff_midpoint hcell) rfl rfl

/-- All prime rails in the complete reciprocal cell `k = ⌊m/p⌋`. -/
noncomputable def reciprocalPrimeCell (m k : ℕ) : Finset ℕ := by
  classical
  exact m.primesLE.filter fun p ↦ quotientCellIndex m p = k

/-- Positive-orientation half of a complete reciprocal prime cell. -/
noncomputable def lowerReciprocalPrimeCell (m k : ℕ) : Finset ℕ := by
  classical
  exact (reciprocalPrimeCell m k).filter fun p ↦ 2 * (m % p) < p

/-- Negative-orientation half of a complete reciprocal prime cell. -/
noncomputable def upperReciprocalPrimeCell (m k : ℕ) : Finset ℕ := by
  classical
  exact (reciprocalPrimeCell m k).filter fun p ↦ ¬2 * (m % p) < p

/-- Natural lower endpoint of reciprocal cell `k`. -/
def reciprocalCellLow (m k : ℕ) : ℕ := m / (k + 1)

/-- Natural harmonic midpoint of reciprocal cell `k`. -/
def reciprocalCellMid (m k : ℕ) : ℕ := (2 * m) / (2 * k + 1)

/-- Natural upper endpoint of reciprocal cell `k`. -/
def reciprocalCellHigh (m k : ℕ) : ℕ := m / k

/-- The positive half-cell is precisely the prime interval `(Mid, High]`. -/
theorem lowerReciprocalPrimeCell_eq_sdiff (m k : ℕ) (hk : 0 < k) :
    lowerReciprocalPrimeCell m k =
      (reciprocalCellHigh m k).primesLE \ (reciprocalCellMid m k).primesLE := by
  classical
  ext p
  simp only [lowerReciprocalPrimeCell, reciprocalPrimeCell, mem_filter, mem_sdiff,
    Nat.mem_primesLE, reciprocalCellHigh, reciprocalCellMid, quotientCellIndex]
  constructor
  · rintro ⟨⟨⟨hpm, hpprime⟩, hcell⟩, hlower⟩
    have hkp : p * k ≤ m := by
      simpa [hcell, mul_comm] using Nat.div_mul_le_self m p
    have hphigh : p ≤ m / k := (Nat.le_div_iff_mul_le hk).mpr hkp
    have hmidpoint : 2 * m < (2 * k + 1) * p :=
      (quotientDigit_lower_iff_midpoint (m := m) (k := k) (p := p) hcell).mp hlower
    have hpmid : (2 * m) / (2 * k + 1) < p :=
      (Nat.div_lt_iff_lt_mul (k := 2 * k + 1) (x := 2 * m) (y := p) (by omega)).mpr
        (by simpa [mul_comm] using hmidpoint)
    exact ⟨⟨hphigh, hpprime⟩, fun h ↦ (not_le_of_gt hpmid) h.1⟩
  · rintro ⟨⟨hphigh, hpprime⟩, hnotmid⟩
    have hkp : p * k ≤ m := (Nat.le_div_iff_mul_le hk).mp hphigh
    have hpmid : (2 * m) / (2 * k + 1) < p := by
      by_contra h
      exact hnotmid ⟨by omega, hpprime⟩
    have hmidpoint : 2 * m < (2 * k + 1) * p :=
      (by
        have h := (Nat.div_lt_iff_lt_mul (k := 2 * k + 1) (x := 2 * m) (y := p)
          (by omega)).mp hpmid
        simpa [mul_comm] using h)
    have hmidform : (2 * k + 1) * p = 2 * (p * k) + p := by ring
    have hnextform : (k + 1) * p = p * k + p := by ring
    have hmlt : m < (k + 1) * p := by omega
    have hcell : m / p = k := by
      apply Nat.div_eq_of_lt_le
      · simpa [mul_comm] using hkp
      · simpa [mul_comm] using hmlt
    have hpm : p ≤ m :=
      (Nat.le_mul_of_pos_right p hk).trans hkp
    exact ⟨⟨⟨hpm, hpprime⟩, hcell⟩,
      (quotientDigit_lower_iff_midpoint (m := m) (k := k) (p := p) hcell).mpr
        hmidpoint⟩

/-- The negative half-cell is precisely the prime interval `(Low, Mid]`. -/
theorem upperReciprocalPrimeCell_eq_sdiff (m k : ℕ) (hk : 0 < k) :
    upperReciprocalPrimeCell m k =
      (reciprocalCellMid m k).primesLE \ (reciprocalCellLow m k).primesLE := by
  classical
  ext p
  simp only [upperReciprocalPrimeCell, reciprocalPrimeCell, mem_filter, mem_sdiff,
    Nat.mem_primesLE, reciprocalCellMid, reciprocalCellLow, quotientCellIndex]
  constructor
  · rintro ⟨⟨⟨hpm, hpprime⟩, hcell⟩, hupper⟩
    have hmlt : m < (k + 1) * p := by
      apply (Nat.div_lt_iff_lt_mul hpprime.pos).mp
      rw [hcell]
      omega
    have hlowp : m / (k + 1) < p := by
      exact (Nat.div_lt_iff_lt_mul (k := k + 1) (x := m) (y := p) (by omega)).mpr
        (by simpa [mul_comm] using hmlt)
    have hmidpoint : (2 * k + 1) * p ≤ 2 * m := by
      have := quotientDigit_lower_iff_midpoint (m := m) (k := k) (p := p) hcell
      omega
    have hpmid : p ≤ (2 * m) / (2 * k + 1) :=
      (Nat.le_div_iff_mul_le (k := 2 * k + 1) (x := p) (y := 2 * m) (by omega)).mpr
        (by simpa [mul_comm] using hmidpoint)
    exact ⟨⟨hpmid, hpprime⟩, fun h ↦ (not_le_of_gt hlowp) h.1⟩
  · rintro ⟨⟨hpmid, hpprime⟩, hnotlow⟩
    have hlowp : m / (k + 1) < p := by
      by_contra h
      exact hnotlow ⟨by omega, hpprime⟩
    have hmlt : m < (k + 1) * p :=
      (by
        have h := (Nat.div_lt_iff_lt_mul (k := k + 1) (x := m) (y := p)
          (by omega)).mp hlowp
        simpa [mul_comm] using h)
    have hmidpoint : (2 * k + 1) * p ≤ 2 * m :=
      (by
        have h := (Nat.le_div_iff_mul_le (k := 2 * k + 1) (x := p) (y := 2 * m)
          (by omega)).mp hpmid
        simpa [mul_comm] using h)
    have hmidform : (2 * k + 1) * p = 2 * (p * k) + p := by ring
    have hkp : p * k ≤ m := by omega
    have hcell : m / p = k := by
      apply Nat.div_eq_of_lt_le
      · simpa [mul_comm] using hkp
      · simpa [mul_comm] using hmlt
    have hpm : p ≤ m :=
      (Nat.le_mul_of_pos_right p hk).trans hkp
    exact ⟨⟨⟨hpm, hpprime⟩, hcell⟩, by
      intro hlower
      have := (quotientDigit_lower_iff_midpoint (m := m) (k := k) (p := p) hcell).mp
        hlower
      omega⟩

/-- Cumulative reciprocal-prime mass. -/
noncomputable def primeReciprocalCumulative (x : ℕ) : ℝ :=
  ∑ p ∈ x.primesLE, (1 : ℝ) / (p : ℝ)

/-- Reciprocal mass of a nested prime interval is a difference of cumulative masses. -/
theorem primeReciprocalCumulative_sdiff {a b : ℕ} (hab : a ≤ b) :
    ∑ p ∈ b.primesLE \ a.primesLE, (1 : ℝ) / (p : ℝ) =
      primeReciprocalCumulative b - primeReciprocalCumulative a := by
  have hsubset : a.primesLE ⊆ b.primesLE := by
    intro p hp
    have hmem := Nat.mem_primesLE.mp hp
    exact Nat.mem_primesLE.mpr ⟨hmem.1.trans hab, hmem.2⟩
  rw [primeReciprocalCumulative, primeReciprocalCumulative,
    ← sum_sdiff hsubset]
  ring

/-- The complete-cell signed prime mass is the exact second difference of cumulative reciprocal
prime mass at `(Low, Mid, High)`.  This is the discrete warped-contour pairing. -/
theorem reciprocalPrimeCell_signedMass_eq_secondDifference (m k : ℕ) (hk : 0 < k) :
    (∑ p ∈ lowerReciprocalPrimeCell m k, (1 : ℝ) / (p : ℝ)) -
        ∑ p ∈ upperReciprocalPrimeCell m k, (1 : ℝ) / (p : ℝ) =
      primeReciprocalCumulative (reciprocalCellHigh m k) -
        2 * primeReciprocalCumulative (reciprocalCellMid m k) +
          primeReciprocalCumulative (reciprocalCellLow m k) := by
  have hlowmid : reciprocalCellLow m k ≤ reciprocalCellMid m k := by
    rw [reciprocalCellLow, reciprocalCellMid]
    apply (Nat.le_div_iff_mul_le (by omega)).mpr
    have hdiv := Nat.div_mul_le_self m (k + 1)
    nlinarith
  have hmidhigh : reciprocalCellMid m k ≤ reciprocalCellHigh m k := by
    rw [reciprocalCellMid, reciprocalCellHigh]
    apply (Nat.le_div_iff_mul_le hk).mpr
    have hdiv := Nat.div_mul_le_self (2 * m) (2 * k + 1)
    nlinarith
  rw [lowerReciprocalPrimeCell_eq_sdiff m k hk,
    upperReciprocalPrimeCell_eq_sdiff m k hk,
    primeReciprocalCumulative_sdiff hmidhigh,
    primeReciprocalCumulative_sdiff hlowmid]
  ring

/-- Second difference of a cumulative potential over one harmonic reciprocal cell. -/
noncomputable def reciprocalCellSecondDifference (F : ℕ → ℝ) (m k : ℕ) : ℝ :=
  F (reciprocalCellHigh m k) - 2 * F (reciprocalCellMid m k) +
    F (reciprocalCellLow m k)

/-- Adjacent reciprocal cells share their integer endpoint exactly. -/
theorem reciprocalCellLow_eq_high_succ (m k : ℕ) :
    reciprocalCellLow m k = reciprocalCellHigh m (k + 1) := rfl

/-- Smooth prime-harmonic main potential, normalized to zero below its logarithmic range. -/
noncomputable def primeMertensMain (x : ℕ) : ℝ :=
  if 2 ≤ x then Real.log (Real.log (x : ℝ)) else 0

/-- Exact residual of cumulative reciprocal-prime mass after removing the log-log carrier. -/
noncomputable def primeMertensError (x : ℕ) : ℝ :=
  primeReciprocalCumulative x - primeMertensMain x

/-- Every prime-cell ledger splits exactly into its smooth midpoint-quadrature defect and the
second difference of the prime Mertens residual. -/
theorem reciprocalPrimeCell_secondDifference_eq_main_add_error (m k : ℕ) :
    reciprocalCellSecondDifference primeReciprocalCumulative m k =
      reciprocalCellSecondDifference primeMertensMain m k +
        reciprocalCellSecondDifference primeMertensError m k := by
  simp only [reciprocalCellSecondDifference, primeMertensError]
  ring

/-- Signed harmonic ledger of the least base-`p` digit over all primes up to `m`. -/
noncomputable def firstDigitSignedPrimeLedger (m : ℕ) : ℝ :=
  ∑ p ∈ m.primesLE, (1 : ℝ) / (p : ℝ) * quotientDigitSign m p

/-- The signed sum on one reciprocal cell is its lower mass minus its upper mass. -/
theorem reciprocalPrimeCell_signedLedger_eq_sub (m k : ℕ) :
    ∑ p ∈ reciprocalPrimeCell m k,
        (1 : ℝ) / (p : ℝ) * quotientDigitSign m p =
      (∑ p ∈ lowerReciprocalPrimeCell m k, (1 : ℝ) / (p : ℝ)) -
        ∑ p ∈ upperReciprocalPrimeCell m k, (1 : ℝ) / (p : ℝ) := by
  classical
  rw [lowerReciprocalPrimeCell, upperReciprocalPrimeCell, sum_filter, sum_filter,
    ← sum_sub_distrib]
  apply sum_congr rfl
  intro p _
  rw [quotientDigitSign]
  by_cases hlower : 2 * (m % p) < p <;> simp [hlower]

/-- Exact whole-rail quadrature formula: the least-digit signed prime ledger is the sum of the
reciprocal-cell second differences.  No prime reflection and no sampling approximation occurs. -/
theorem firstDigitSignedPrimeLedger_eq_sum_secondDifferences (m : ℕ) :
    firstDigitSignedPrimeLedger m =
      ∑ k ∈ Ico 1 (m + 1),
        reciprocalCellSecondDifference primeReciprocalCumulative m k := by
  classical
  have hmaps : ∀ p ∈ m.primesLE,
      quotientCellIndex m p ∈ Ico 1 (m + 1) := by
    intro p hp
    have hmem := Nat.mem_primesLE.mp hp
    have hpone : 1 ≤ p := hmem.2.one_le
    have hlower : 1 ≤ m / p := (Nat.one_le_div_iff hmem.2.pos).mpr hmem.1
    have hupper : m / p < m + 1 := (Nat.div_le_self m p).trans_lt (Nat.lt_succ_self m)
    exact mem_Ico.mpr ⟨hlower, hupper⟩
  rw [firstDigitSignedPrimeLedger]
  calc
    ∑ p ∈ m.primesLE, (1 : ℝ) / (p : ℝ) * quotientDigitSign m p =
        ∑ k ∈ Ico 1 (m + 1),
          ∑ p ∈ m.primesLE with quotientCellIndex m p = k,
            (1 : ℝ) / (p : ℝ) * quotientDigitSign m p := by
              symm
              exact Finset.sum_fiberwise_of_maps_to hmaps _
    _ = ∑ k ∈ Ico 1 (m + 1),
        ∑ p ∈ reciprocalPrimeCell m k,
          (1 : ℝ) / (p : ℝ) * quotientDigitSign m p := by
            apply sum_congr rfl
            intro k _
            rfl
    _ = ∑ k ∈ Ico 1 (m + 1),
        reciprocalCellSecondDifference primeReciprocalCumulative m k := by
          apply sum_congr rfl
          intro k hk
          have hkpos : 0 < k := (mem_Ico.mp hk).1
          rw [reciprocalPrimeCell_signedLedger_eq_sub,
            reciprocalPrimeCell_signedMass_eq_secondDifference m k hkpos]
          rfl

/-- The whole least-digit ledger splits into a smooth quadrature bank and a chained Mertens-error
bank.  This is the prime-counting Stieltjes adapter in finite exact form. -/
theorem firstDigitSignedPrimeLedger_eq_main_add_error (m : ℕ) :
    firstDigitSignedPrimeLedger m =
      (∑ k ∈ Ico 1 (m + 1), reciprocalCellSecondDifference primeMertensMain m k) +
        ∑ k ∈ Ico 1 (m + 1), reciprocalCellSecondDifference primeMertensError m k := by
  rw [firstDigitSignedPrimeLedger_eq_sum_secondDifferences, ← sum_add_distrib]
  apply sum_congr rfl
  intro k _
  exact reciprocalPrimeCell_secondDifference_eq_main_add_error m k

/-!
## Recursive bank adapter

The complete-cell formula above does not require the ambient bank to contain every prime.  The
same second difference is exact after intersecting all three cutoffs with an arbitrary finite
survivor bank.  This is the point at which the quotient warp becomes recursive: the bank at depth
`j` is the closed-orbit bank produced by depths `0, ..., j`.
-/

/-- Reciprocal-prime cumulative potential restricted to an arbitrary finite bank. -/
noncomputable def bankPrimeReciprocalCumulative (s : Finset ℕ) (x : ℕ) : ℝ :=
  ∑ p ∈ s ∩ x.primesLE, (1 : ℝ) / (p : ℝ)

theorem bankPrimeReciprocalCumulative_nonneg (s : Finset ℕ) (x : ℕ) :
    0 ≤ bankPrimeReciprocalCumulative s x := by
  rw [bankPrimeReciprocalCumulative]
  exact sum_nonneg fun _ _ ↦ by positivity

theorem bankPrimeReciprocalCumulative_le_primeHarmonicMass
    (s : Finset ℕ) (x : ℕ) :
    bankPrimeReciprocalCumulative s x ≤ primeHarmonicMass s := by
  rw [bankPrimeReciprocalCumulative, primeHarmonicMass]
  exact Finset.sum_le_sum_of_subset_of_nonneg inter_subset_left (by
    intro p _ _
    positivity)

/-- A nested prime interval remains a cumulative difference after restriction to a finite bank. -/
theorem bankPrimeReciprocalCumulative_sdiff (s : Finset ℕ) {a b : ℕ} (hab : a ≤ b) :
    ∑ p ∈ (s ∩ b.primesLE) \ (s ∩ a.primesLE), (1 : ℝ) / (p : ℝ) =
      bankPrimeReciprocalCumulative s b - bankPrimeReciprocalCumulative s a := by
  have hsubset : s ∩ a.primesLE ⊆ s ∩ b.primesLE := by
    intro p hp
    have hmem := mem_inter.mp hp
    have hp := Nat.mem_primesLE.mp hmem.2
    exact mem_inter.mpr ⟨hmem.1, Nat.mem_primesLE.mpr ⟨hp.1.trans hab, hp.2⟩⟩
  rw [bankPrimeReciprocalCumulative, bankPrimeReciprocalCumulative,
    ← sum_sdiff hsubset]
  ring

/-- Lower half of one reciprocal cell, restricted to a finite prime bank. -/
noncomputable def bankLowerReciprocalPrimeCell (s : Finset ℕ) (m k : ℕ) : Finset ℕ :=
  s ∩ lowerReciprocalPrimeCell m k

/-- Upper half of one reciprocal cell, restricted to a finite prime bank. -/
noncomputable def bankUpperReciprocalPrimeCell (s : Finset ℕ) (m k : ℕ) : Finset ℕ :=
  s ∩ upperReciprocalPrimeCell m k

/-- Restriction to a bank commutes with the lower complete-cell interval decomposition. -/
theorem bankLowerReciprocalPrimeCell_eq_sdiff (s : Finset ℕ) (m k : ℕ) (hk : 0 < k) :
    bankLowerReciprocalPrimeCell s m k =
      (s ∩ (reciprocalCellHigh m k).primesLE) \
        (s ∩ (reciprocalCellMid m k).primesLE) := by
  classical
  rw [bankLowerReciprocalPrimeCell, lowerReciprocalPrimeCell_eq_sdiff m k hk]
  ext p
  simp only [mem_inter, mem_sdiff]
  tauto

/-- Restriction to a bank commutes with the upper complete-cell interval decomposition. -/
theorem bankUpperReciprocalPrimeCell_eq_sdiff (s : Finset ℕ) (m k : ℕ) (hk : 0 < k) :
    bankUpperReciprocalPrimeCell s m k =
      (s ∩ (reciprocalCellMid m k).primesLE) \
        (s ∩ (reciprocalCellLow m k).primesLE) := by
  classical
  rw [bankUpperReciprocalPrimeCell, upperReciprocalPrimeCell_eq_sdiff m k hk]
  ext p
  simp only [mem_inter, mem_sdiff]
  tauto

/-- The warped-contour second-difference identity is exact for every finite survivor bank. -/
theorem bankReciprocalPrimeCell_signedMass_eq_secondDifference
    (s : Finset ℕ) (m k : ℕ) (hk : 0 < k) :
    (∑ p ∈ bankLowerReciprocalPrimeCell s m k, (1 : ℝ) / (p : ℝ)) -
        ∑ p ∈ bankUpperReciprocalPrimeCell s m k, (1 : ℝ) / (p : ℝ) =
      reciprocalCellSecondDifference (bankPrimeReciprocalCumulative s) m k := by
  have hlowmid : reciprocalCellLow m k ≤ reciprocalCellMid m k := by
    rw [reciprocalCellLow, reciprocalCellMid]
    apply (Nat.le_div_iff_mul_le (by omega)).mpr
    have hdiv := Nat.div_mul_le_self m (k + 1)
    nlinarith
  have hmidhigh : reciprocalCellMid m k ≤ reciprocalCellHigh m k := by
    rw [reciprocalCellMid, reciprocalCellHigh]
    apply (Nat.le_div_iff_mul_le hk).mpr
    have hdiv := Nat.div_mul_le_self (2 * m) (2 * k + 1)
    nlinarith
  rw [bankLowerReciprocalPrimeCell_eq_sdiff s m k hk,
    bankUpperReciprocalPrimeCell_eq_sdiff s m k hk,
    bankPrimeReciprocalCumulative_sdiff s hmidhigh,
    bankPrimeReciprocalCumulative_sdiff s hlowmid,
    reciprocalCellSecondDifference]
  ring

/-- The signed digit ledger on a bank-restricted reciprocal cell is its lower mass minus its upper
mass. -/
theorem bankReciprocalPrimeCell_signedLedger_eq_sub
    (s : Finset ℕ) (m k : ℕ) :
    ∑ p ∈ s ∩ reciprocalPrimeCell m k,
        (1 : ℝ) / (p : ℝ) * quotientDigitSign m p =
      (∑ p ∈ bankLowerReciprocalPrimeCell s m k, (1 : ℝ) / (p : ℝ)) -
        ∑ p ∈ bankUpperReciprocalPrimeCell s m k, (1 : ℝ) / (p : ℝ) := by
  classical
  have hlower : bankLowerReciprocalPrimeCell s m k =
      (s ∩ reciprocalPrimeCell m k).filter fun p ↦ 2 * (m % p) < p := by
    ext p
    simp [bankLowerReciprocalPrimeCell, lowerReciprocalPrimeCell]
    tauto
  have hupper : bankUpperReciprocalPrimeCell s m k =
      (s ∩ reciprocalPrimeCell m k).filter fun p ↦ ¬2 * (m % p) < p := by
    ext p
    simp [bankUpperReciprocalPrimeCell, upperReciprocalPrimeCell]
    tauto
  rw [hlower, hupper, sum_filter, sum_filter, ← sum_sub_distrib]
  apply sum_congr rfl
  intro p _
  rw [quotientDigitSign]
  by_cases hlower : 2 * (m % p) < p <;> simp [hlower]

/-- Prime rails in a bank whose first `j+1` dynamic cells have survived. -/
noncomputable def dynamicSurvivingPrimeBank (s : Finset ℕ) (n j : ℕ) : Finset ℕ := by
  classical
  exact s.filter fun p ↦ DynamicClosedOrbit p n (j + 1)

/-- One fixed quotient-prefix fiber of the dynamic survivor bank. -/
noncomputable def dynamicPrefixPrimeBank
    (s : Finset ℕ) (n j m : ℕ) : Finset ℕ := by
  classical
  exact (dynamicSurvivingPrimeBank s n j).filter fun p ↦ quotientPrefix n j p = m

/-- The Boolean closure weight turns the dynamic ledger into a literal survivor-bank sum. -/
theorem dynamicBankSignedLedger_eq_survivingSum (s : Finset ℕ) (n j : ℕ) :
    dynamicBankSignedLedger s n j =
      ∑ p ∈ dynamicSurvivingPrimeBank s n j,
        (1 : ℝ) / (p : ℝ) * dynamicSquareSign p n j := by
  classical
  rw [dynamicBankSignedLedger, dynamicSurvivingPrimeBank, sum_filter]
  apply sum_congr rfl
  intro p _
  rw [dynamicClosureWeight_eq_ite]
  by_cases horbit : DynamicClosedOrbit p n (j + 1) <;> simp [horbit]

/-- The Boolean dynamic energy is exactly the harmonic mass of the surviving prime bank. -/
theorem dynamicBankEnergy_eq_survivingPrimeHarmonicMass
    (s : Finset ℕ) (n j : ℕ) :
    dynamicBankEnergy s n j = primeHarmonicMass (dynamicSurvivingPrimeBank s n j) := by
  classical
  rw [dynamicBankEnergy, primeHarmonicMass, dynamicSurvivingPrimeBank, sum_filter]
  apply sum_congr rfl
  intro p _
  rw [dynamicClosureWeight_eq_ite]
  by_cases horbit : DynamicClosedOrbit p n (j + 1) <;> simp [horbit]

/-- Quotient-prefix fibers partition the survivor bank without harmonic-mass loss. -/
theorem sum_dynamicPrefixPrimeBank_primeHarmonicMass
    (s : Finset ℕ) (n j : ℕ) :
    ∑ m ∈ range (n + 1), primeHarmonicMass (dynamicPrefixPrimeBank s n j m) =
      primeHarmonicMass (dynamicSurvivingPrimeBank s n j) := by
  classical
  have hmaps : ∀ p ∈ dynamicSurvivingPrimeBank s n j,
      quotientPrefix n j p ∈ range (n + 1) := by
    intro p _
    exact mem_range.mpr ((Nat.div_le_self n (p ^ (j + 1))).trans_lt (Nat.lt_succ_self n))
  rw [primeHarmonicMass]
  calc
    (∑ m ∈ range (n + 1),
        primeHarmonicMass (dynamicPrefixPrimeBank s n j m)) =
      ∑ m ∈ range (n + 1),
        ∑ p ∈ dynamicSurvivingPrimeBank s n j with quotientPrefix n j p = m,
          (1 : ℝ) / (p : ℝ) := by
            apply sum_congr rfl
            intro m _
            rfl
    _ = ∑ p ∈ dynamicSurvivingPrimeBank s n j, (1 : ℝ) / (p : ℝ) := by
      exact Finset.sum_fiberwise_of_maps_to hmaps _

/-- On a bank of primes, the dynamic sign on every survivor is exactly its next quotient-digit
sign. -/
theorem dynamicBankSignedLedger_eq_survivingQuotientSum
    {s : Finset ℕ} {n j : ℕ} (hprimes : s ⊆ n.primesLE) :
    dynamicBankSignedLedger s n j =
      ∑ p ∈ dynamicSurvivingPrimeBank s n j,
        (1 : ℝ) / (p : ℝ) * quotientDigitSign (quotientPrefix n j p) p := by
  rw [dynamicBankSignedLedger_eq_survivingSum]
  apply sum_congr rfl
  intro p hp
  have hp' := mem_filter.mp hp
  have hpprime := Nat.prime_of_mem_primesLE (hprimes hp'.1)
  have hprevious := hp'.2 j (by omega)
  rw [dynamicSquareSign_eq_quotientDigitSign hpprime.one_lt hprevious]

/-- The exceptional reciprocal cell `k=0`, where the quotient prefix is smaller than the prime. -/
noncomputable def dynamicPrefixBoundaryPrimeBank
    (s : Finset ℕ) (n j m : ℕ) : Finset ℕ := by
  classical
  exact (dynamicPrefixPrimeBank s n j m).filter fun p ↦ m < p

/-- Positive reciprocal cells `k≥1`, equivalently the part of a prefix bank with `p≤m`. -/
noncomputable def dynamicPrefixInteriorPrimeBank
    (s : Finset ℕ) (n j m : ℕ) : Finset ℕ := by
  classical
  exact (dynamicPrefixPrimeBank s n j m).filter fun p ↦ p ≤ m

/-- Signed contribution of the non-telescoping `k=0` prefix boundary. -/
noncomputable def dynamicPrefixBoundaryLedger
    (s : Finset ℕ) (n j m : ℕ) : ℝ :=
  ∑ p ∈ dynamicPrefixBoundaryPrimeBank s n j m,
    (1 : ℝ) / (p : ℝ) * quotientDigitSign m p

/-- Exact atomic/diffuse split of a fixed quotient-prefix fiber. -/
theorem dynamicPrefixPrimeBank_sum_eq_boundary_add_interior
    (s : Finset ℕ) (n j m : ℕ) :
    (∑ p ∈ dynamicPrefixPrimeBank s n j m,
        (1 : ℝ) / (p : ℝ) * quotientDigitSign m p) =
      dynamicPrefixBoundaryLedger s n j m +
        ∑ p ∈ dynamicPrefixInteriorPrimeBank s n j m,
          (1 : ℝ) / (p : ℝ) * quotientDigitSign m p := by
  classical
  rw [dynamicPrefixBoundaryLedger, dynamicPrefixBoundaryPrimeBank,
    dynamicPrefixInteriorPrimeBank]
  have hsplit := Finset.sum_filter_add_sum_filter_not
    (dynamicPrefixPrimeBank s n j m) (fun p ↦ m < p)
    (fun p ↦ (1 : ℝ) / (p : ℝ) * quotientDigitSign m p)
  simpa [not_lt] using hsplit.symm

/-- The interior of a fixed prefix fiber is partitioned exactly by positive reciprocal cells. -/
theorem dynamicPrefixInteriorPrimeBank_eq_sum_cells
    {s : Finset ℕ} {n j m : ℕ} (hprimes : s ⊆ n.primesLE) :
    (∑ p ∈ dynamicPrefixInteriorPrimeBank s n j m,
        (1 : ℝ) / (p : ℝ) * quotientDigitSign m p) =
      ∑ k ∈ Ico 1 (m + 1),
        reciprocalCellSecondDifference
          (bankPrimeReciprocalCumulative (dynamicPrefixPrimeBank s n j m)) m k := by
  classical
  have hmaps : ∀ p ∈ dynamicPrefixInteriorPrimeBank s n j m,
      quotientCellIndex m p ∈ Ico 1 (m + 1) := by
    intro p hp
    have hinterior := mem_filter.mp hp
    have hpfiber := mem_filter.mp hinterior.1
    have hpsurvive := mem_filter.mp hpfiber.1
    have hpprime := Nat.prime_of_mem_primesLE (hprimes hpsurvive.1)
    have hlower : 1 ≤ m / p := (Nat.one_le_div_iff hpprime.pos).mpr hinterior.2
    have hupper : m / p < m + 1 := (Nat.div_le_self m p).trans_lt (Nat.lt_succ_self m)
    exact mem_Ico.mpr ⟨hlower, hupper⟩
  calc
    (∑ p ∈ dynamicPrefixInteriorPrimeBank s n j m,
        (1 : ℝ) / (p : ℝ) * quotientDigitSign m p) =
      ∑ k ∈ Ico 1 (m + 1),
        ∑ p ∈ dynamicPrefixInteriorPrimeBank s n j m with quotientCellIndex m p = k,
          (1 : ℝ) / (p : ℝ) * quotientDigitSign m p := by
            symm
            exact Finset.sum_fiberwise_of_maps_to hmaps _
    _ = ∑ k ∈ Ico 1 (m + 1),
        ∑ p ∈ (dynamicPrefixPrimeBank s n j m ∩ reciprocalPrimeCell m k),
          (1 : ℝ) / (p : ℝ) * quotientDigitSign m p := by
            apply sum_congr rfl
            intro k _
            apply sum_congr
            · ext p
              constructor
              · intro hp
                have hp' := mem_filter.mp hp
                have hinterior := mem_filter.mp hp'.1
                have hpfiber := mem_filter.mp hinterior.1
                have hpsurvive := mem_filter.mp hpfiber.1
                have hpprime := Nat.prime_of_mem_primesLE (hprimes hpsurvive.1)
                exact mem_inter.mpr ⟨hinterior.1,
                  mem_filter.mpr ⟨Nat.mem_primesLE.mpr ⟨hinterior.2, hpprime⟩, hp'.2⟩⟩
              · intro hp
                have hp' := mem_inter.mp hp
                have hcell := mem_filter.mp hp'.2
                exact mem_filter.mpr ⟨mem_filter.mpr ⟨hp'.1,
                  (Nat.mem_primesLE.mp hcell.1).1⟩, hcell.2⟩
            · intro p _
              rfl
    _ = ∑ k ∈ Ico 1 (m + 1),
        reciprocalCellSecondDifference
          (bankPrimeReciprocalCumulative (dynamicPrefixPrimeBank s n j m)) m k := by
            apply sum_congr rfl
            intro k hk
            have hkpos : 0 < k := (mem_Ico.mp hk).1
            rw [bankReciprocalPrimeCell_signedLedger_eq_sub]
            exact bankReciprocalPrimeCell_signedMass_eq_secondDifference
              (dynamicPrefixPrimeBank s n j m) m k hkpos

/-- Recursive warped-contour formula on one prefix fiber: one explicit `k=0` boundary packet plus
the bank-restricted second differences of every complete reciprocal cell. -/
theorem dynamicPrefixPrimeBank_eq_boundary_add_secondDifferences
    {s : Finset ℕ} {n j m : ℕ} (hprimes : s ⊆ n.primesLE) :
    (∑ p ∈ dynamicPrefixPrimeBank s n j m,
        (1 : ℝ) / (p : ℝ) * quotientDigitSign m p) =
      dynamicPrefixBoundaryLedger s n j m +
        ∑ k ∈ Ico 1 (m + 1),
          reciprocalCellSecondDifference
            (bankPrimeReciprocalCumulative (dynamicPrefixPrimeBank s n j m)) m k := by
  rw [dynamicPrefixPrimeBank_sum_eq_boundary_add_interior,
    dynamicPrefixInteriorPrimeBank_eq_sum_cells hprimes]

/-- The exact recursively warped ledger: each prefix contributes one `k=0` boundary packet and a
chain of complete-cell second differences of its own survivor-bank cumulative potential. -/
noncomputable def recursiveWarpedLedger (s : Finset ℕ) (n j : ℕ) : ℝ :=
  ∑ m ∈ range (n + 1),
    (dynamicPrefixBoundaryLedger s n j m +
      ∑ k ∈ Ico 1 (m + 1),
        reciprocalCellSecondDifference
          (bankPrimeReciprocalCumulative (dynamicPrefixPrimeBank s n j m)) m k)

/-- Absolute mass of all exceptional `k=0` packets in a recursively warped ledger. -/
noncomputable def recursiveWarpedBoundaryMass (s : Finset ℕ) (n j : ℕ) : ℝ :=
  ∑ m ∈ range (n + 1), |dynamicPrefixBoundaryLedger s n j m|

/-- Warped variation of the complete-cell second differences of the evolving survivor bank. -/
noncomputable def recursiveWarpedInteriorVariation (s : Finset ℕ) (n j : ℕ) : ℝ :=
  ∑ m ∈ range (n + 1),
    ∑ k ∈ Ico 1 (m + 1),
      |reciprocalCellSecondDifference
        (bankPrimeReciprocalCumulative (dynamicPrefixPrimeBank s n j m)) m k|

/-!
The next target unfolds to a finite unsigned statement: each complete reciprocal cell contributes
the absolute difference of its lower and upper reciprocal-prime masses.  The lower and upper
halves partition the cell, the cells partition the interior of one quotient-prefix fiber, and the
prefix fibers partition the surviving bank.  Two compiler-level decompositions were tried:

1. rewrite the second difference as `lowerMass - upperMass`, apply `abs_sub`, then sum the exact
   cell and prefix partitions;
2. recombine the Mellin sampling and clock adapters before taking absolute values, using
   `mellinCellReconstruction_eq_secondDifference` as the first line.

The first route gives the unconditional warped-variation contraction below.  The second route is
kept for the remaining sampling/quantization ledger, where premature triangle inequalities lose
the carrier cancellation.
-/

/-- One complete warped cell has no more absolute imbalance than its unsigned reciprocal mass. -/
theorem abs_bankReciprocalPrimeCell_secondDifference_le_mass
    (s : Finset ℕ) (m k : ℕ) (hk : 0 < k) :
    |reciprocalCellSecondDifference (bankPrimeReciprocalCumulative s) m k| ≤
      ∑ p ∈ s ∩ reciprocalPrimeCell m k, (1 : ℝ) / (p : ℝ) := by
  classical
  let lowerMass : ℝ :=
    ∑ p ∈ bankLowerReciprocalPrimeCell s m k, (1 : ℝ) / (p : ℝ)
  let upperMass : ℝ :=
    ∑ p ∈ bankUpperReciprocalPrimeCell s m k, (1 : ℝ) / (p : ℝ)
  have hlower : 0 ≤ lowerMass := by
    dsimp only [lowerMass]
    exact sum_nonneg fun _ _ ↦ by positivity
  have hupper : 0 ≤ upperMass := by
    dsimp only [upperMass]
    exact sum_nonneg fun _ _ ↦ by positivity
  have hcell : lowerMass + upperMass =
      ∑ p ∈ s ∩ reciprocalPrimeCell m k, (1 : ℝ) / (p : ℝ) := by
    dsimp only [lowerMass, upperMass]
    rw [bankLowerReciprocalPrimeCell, bankUpperReciprocalPrimeCell,
      lowerReciprocalPrimeCell, upperReciprocalPrimeCell]
    have hsplit := Finset.sum_filter_add_sum_filter_not
      (s ∩ reciprocalPrimeCell m k) (fun p ↦ 2 * (m % p) < p)
      (fun p ↦ (1 : ℝ) / (p : ℝ))
    simpa only [inter_filter] using hsplit
  have hdiff := bankReciprocalPrimeCell_signedMass_eq_secondDifference s m k hk
  rw [← hdiff]
  change |lowerMass - upperMass| ≤ _
  rw [← hcell]
  exact (abs_sub lowerMass upperMass).trans_eq
    (by rw [abs_of_nonneg hlower, abs_of_nonneg hupper])

/-- The positive reciprocal cells are an unsigned harmonic partition of one prefix interior. -/
theorem dynamicPrefixInteriorPrimeBank_mass_eq_sum_cells
    {s : Finset ℕ} {n j m : ℕ} (hprimes : s ⊆ n.primesLE) :
    (∑ p ∈ dynamicPrefixInteriorPrimeBank s n j m, (1 : ℝ) / (p : ℝ)) =
      ∑ k ∈ Ico 1 (m + 1),
        ∑ p ∈ dynamicPrefixPrimeBank s n j m ∩ reciprocalPrimeCell m k,
          (1 : ℝ) / (p : ℝ) := by
  classical
  have hmaps : ∀ p ∈ dynamicPrefixInteriorPrimeBank s n j m,
      quotientCellIndex m p ∈ Ico 1 (m + 1) := by
    intro p hp
    have hinterior := mem_filter.mp hp
    have hpfiber := mem_filter.mp hinterior.1
    have hpsurvive := mem_filter.mp hpfiber.1
    have hpprime := Nat.prime_of_mem_primesLE (hprimes hpsurvive.1)
    have hlower : 1 ≤ m / p := (Nat.one_le_div_iff hpprime.pos).mpr hinterior.2
    have hupper : m / p < m + 1 :=
      (Nat.div_le_self m p).trans_lt (Nat.lt_succ_self m)
    exact mem_Ico.mpr ⟨hlower, hupper⟩
  calc
    (∑ p ∈ dynamicPrefixInteriorPrimeBank s n j m, (1 : ℝ) / (p : ℝ)) =
        ∑ k ∈ Ico 1 (m + 1),
          ∑ p ∈ dynamicPrefixInteriorPrimeBank s n j m with quotientCellIndex m p = k,
            (1 : ℝ) / (p : ℝ) := by
              symm
              exact Finset.sum_fiberwise_of_maps_to hmaps _
    _ = ∑ k ∈ Ico 1 (m + 1),
        ∑ p ∈ dynamicPrefixPrimeBank s n j m ∩ reciprocalPrimeCell m k,
          (1 : ℝ) / (p : ℝ) := by
            apply sum_congr rfl
            intro k _
            apply sum_congr
            · ext p
              constructor
              · intro hp
                have hp' := mem_filter.mp hp
                have hinterior := mem_filter.mp hp'.1
                have hpfiber := mem_filter.mp hinterior.1
                have hpsurvive := mem_filter.mp hpfiber.1
                have hpprime := Nat.prime_of_mem_primesLE (hprimes hpsurvive.1)
                exact mem_inter.mpr ⟨hinterior.1,
                  mem_filter.mpr ⟨Nat.mem_primesLE.mpr ⟨hinterior.2, hpprime⟩, hp'.2⟩⟩
              · intro hp
                have hp' := mem_inter.mp hp
                have hcell := mem_filter.mp hp'.2
                exact mem_filter.mpr ⟨mem_filter.mpr ⟨hp'.1,
                  (Nat.mem_primesLE.mp hcell.1).1⟩, hcell.2⟩
            · intro p _
              rfl

/-- Exact warped-cell contraction: all complete-cell variation is charged once to the current
survivor energy; neither primes nor quotient-prefix fibers are duplicated. -/
theorem recursiveWarpedInteriorVariation_le_dynamicBankEnergy
    {s : Finset ℕ} {n j : ℕ} (hprimes : s ⊆ n.primesLE) :
    recursiveWarpedInteriorVariation s n j ≤ dynamicBankEnergy s n j := by
  rw [recursiveWarpedInteriorVariation,
    dynamicBankEnergy_eq_survivingPrimeHarmonicMass]
  calc
    (∑ m ∈ range (n + 1),
        ∑ k ∈ Ico 1 (m + 1),
          |reciprocalCellSecondDifference
            (bankPrimeReciprocalCumulative (dynamicPrefixPrimeBank s n j m)) m k|) ≤
      ∑ m ∈ range (n + 1),
        ∑ k ∈ Ico 1 (m + 1),
          ∑ p ∈ dynamicPrefixPrimeBank s n j m ∩ reciprocalPrimeCell m k,
            (1 : ℝ) / (p : ℝ) := by
              apply sum_le_sum
              intro m _
              apply sum_le_sum
              intro k hk
              exact abs_bankReciprocalPrimeCell_secondDifference_le_mass
                (dynamicPrefixPrimeBank s n j m) m k (mem_Ico.mp hk).1
    _ = ∑ m ∈ range (n + 1),
        primeHarmonicMass (dynamicPrefixInteriorPrimeBank s n j m) := by
          apply sum_congr rfl
          intro m _
          rw [primeHarmonicMass,
            dynamicPrefixInteriorPrimeBank_mass_eq_sum_cells hprimes]
    _ ≤ ∑ m ∈ range (n + 1),
        primeHarmonicMass (dynamicPrefixPrimeBank s n j m) := by
          apply sum_le_sum
          intro m _
          rw [primeHarmonicMass, primeHarmonicMass]
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · exact filter_subset _ _
          · intro p _ _
            positivity
    _ = primeHarmonicMass (dynamicSurvivingPrimeBank s n j) :=
      sum_dynamicPrefixPrimeBank_primeHarmonicMass s n j

/-! ## Full Mellin normalization

The cumulative survivor potential is now divided by a positive logarithmic clock at every cutoff.
The shift `max x 2` removes the artificial singularities at the integer endpoints `0` and `1`
while agreeing with `log x` on every prime cutoff.  Exact reconstruction requires both normalized
curvature and the two clock-gradient adapters; discarding those adapters would change the ledger.
-/

/-- Positive logarithmic clock on every natural cutoff, equal to `log x` for `2 ≤ x`. -/
noncomputable def mellinClock (x : ℕ) : ℝ :=
  Real.log ((Nat.max x 2 : ℕ) : ℝ)

theorem mellinClock_pos (x : ℕ) : 0 < mellinClock x := by
  rw [mellinClock]
  apply Real.log_pos
  exact_mod_cast (lt_of_lt_of_le Nat.one_lt_two (Nat.le_max_right x 2))

theorem mellinClock_ne_zero (x : ℕ) : mellinClock x ≠ 0 := (mellinClock_pos x).ne'

theorem log_two_le_mellinClock (x : ℕ) :
    Real.log 2 ≤ mellinClock x := by
  rw [mellinClock]
  apply Real.log_le_log (by norm_num)
  exact_mod_cast Nat.le_max_right x 2

/-- The shifted logarithmic clock preserves the natural order of cutoff points. -/
theorem mellinClock_mono {x y : ℕ} (hxy : x ≤ y) :
    mellinClock x ≤ mellinClock y := by
  rw [mellinClock, mellinClock]
  apply Real.log_le_log (by positivity)
  exact_mod_cast max_le_max hxy (le_refl 2)

/-- Prime harmonic mass with the local Mellin clock retained.  This is the summable carrier
measure produced by scaling both reciprocal mass and contour position. -/
noncomputable def primeMellinMass (s : Finset ℕ) : ℝ :=
  ∑ p ∈ s, ((1 : ℝ) / (p : ℝ)) / mellinClock p

/-- Derivative of reciprocal harmonic mass after the logarithmic Mellin conversion. -/
theorem deriv_mellinReciprocal {x : ℝ} (hx : 1 < x) :
    deriv (fun t : ℝ ↦ t⁻¹ / Real.log t) x =
      -(Real.log x + 1) / (x ^ 2 * Real.log x ^ 2) := by
  have hx0 : x ≠ 0 := by linarith
  have hx1 : x ≠ 1 := by linarith
  have hxm1 : x ≠ -1 := by linarith
  rw [show (fun t : ℝ ↦ t⁻¹ / Real.log t) =
      (fun t : ℝ ↦ t⁻¹ * (Real.log t)⁻¹) by
        funext t
        simp [div_eq_mul_inv]]
  change deriv ((fun t : ℝ ↦ t⁻¹) * (fun t : ℝ ↦ (Real.log t)⁻¹)) x = _
  rw [deriv_mul (differentiableAt_inv hx0)
    (Real.differentiableAt_inv_log hx0 hx1 hxm1), deriv_inv',
      Real.deriv_inv_log_apply]
  field_simp
  ring

/-- Mellin-scaled reciprocal-prime mass on one natural interval. -/
noncomputable def primeMellinIoc (a b : ℕ) : ℝ :=
  ∑ p ∈ Ioc a b with p.Prime, ((1 : ℝ) / (p : ℝ)) / Real.log p

theorem primeMellinMass_nonneg (s : Finset ℕ) : 0 ≤ primeMellinMass s := by
  rw [primeMellinMass]
  exact sum_nonneg fun _ _ ↦ div_nonneg (by positivity) (mellinClock_pos _).le

/-- Mellin prime mass is monotone under restriction of the prime bank. -/
theorem primeMellinMass_mono {s t : Finset ℕ} (hst : s ⊆ t) :
    primeMellinMass s ≤ primeMellinMass t := by
  rw [primeMellinMass, primeMellinMass]
  exact Finset.sum_le_sum_of_subset_of_nonneg hst (by
    intro p _ _
    exact div_nonneg (by positivity) (mellinClock_pos p).le)

/-- Difference between the discrete upper-endpoint clock and its continuous quotient clock. -/
noncomputable def mellinHighClockQuantizationError (m k : ℕ) : ℝ :=
  mellinClock (reciprocalCellHigh m k) -
    Real.log (quotientCellZeroEndpoint (m : ℝ) (k : ℝ))

/-- Difference between the discrete midpoint clock and its continuous harmonic midpoint clock. -/
noncomputable def mellinMidClockQuantizationError (m k : ℕ) : ℝ :=
  mellinClock (reciprocalCellMid m k) -
    Real.log (quotientCellMidpoint (m : ℝ) (k : ℝ))

/-- Difference between the discrete lower-endpoint clock and its continuous quotient clock. -/
noncomputable def mellinLowClockQuantizationError (m k : ℕ) : ℝ :=
  mellinClock (reciprocalCellLow m k) -
    Real.log (quotientCellOneEndpoint (m : ℝ) (k : ℝ))

/-- Exact floor adapter for a logarithmic reciprocal cell.  The discrete clock second difference
is the continuous reflected residual plus the second difference of its three quantization errors. -/
theorem mellinClock_secondDifference_eq_residual_add_quantization
    {m k : ℕ} (hm : 0 < m) (hk : 0 < k) :
    mellinClock (reciprocalCellHigh m k) -
        2 * mellinClock (reciprocalCellMid m k) +
          mellinClock (reciprocalCellLow m k) =
      harmonicContourResidual (k : ℝ) +
        (mellinHighClockQuantizationError m k -
          2 * mellinMidClockQuantizationError m k +
            mellinLowClockQuantizationError m k) := by
  have hcontinuous := quotientCell_logClockDefect_eq_harmonicContourResidual
    (m := (m : ℝ)) (k := (k : ℝ)) (by exact_mod_cast hm) (by exact_mod_cast hk)
  simp only [mellinHighClockQuantizationError, mellinMidClockQuantizationError,
    mellinLowClockQuantizationError]
  linarith

/-- Dimensionless base-`p` location of `n` on the global Mellin carrier. -/
noncomputable def mellinRailCoordinate (n p : ℕ) : ℝ :=
  Real.log (n : ℝ) / Real.log (p : ℝ)

/-- Dimensionless location of the active quotient prefix in the same base-`p` carrier. -/
noncomputable def mellinPrefixCoordinate (n j p : ℕ) : ℝ :=
  mellinClock (quotientPrefix n j p) / Real.log (p : ℝ)

/-- Logarithmic terminal distance from the root threshold `p^(r+1)=2*n`. -/
noncomputable def terminalMellinDrift (n r p : ℕ) : ℝ :=
  ((r + 1 : ℕ) : ℝ) * Real.log (p : ℝ) - Real.log ((2 * n : ℕ) : ℝ)

/-- The multiplicative terminal threshold and its Mellin drift are exactly equivalent. -/
theorem terminalMellinDrift_pos_iff {n r p : ℕ} (hn : 0 < n) (hp : 0 < p) :
    0 < terminalMellinDrift n r p ↔ 2 * n < p ^ (r + 1) := by
  rw [terminalMellinDrift, sub_pos, ← Real.log_pow,
    Real.log_lt_log_iff (by positivity) (by positivity)]
  norm_cast

/-- The coherent power rail has exactly integral Mellin depth. -/
theorem mellinRailCoordinate_three_pow (r : ℕ) :
    mellinRailCoordinate (3 ^ r) 3 = r := by
  rw [mellinRailCoordinate, Nat.cast_pow, Real.log_pow]
  field_simp [Real.log_ne_zero_of_pos_of_ne_one (by norm_num : (0 : ℝ) < 3) (by norm_num)]

/-- Dimensionless survivor potential on the logarithmic carrier. -/
noncomputable def normalizedBankPrimeCarrier (s : Finset ℕ) (x : ℕ) : ℝ :=
  bankPrimeReciprocalCumulative s x / mellinClock x

theorem normalizedBankPrimeCarrier_nonneg (s : Finset ℕ) (x : ℕ) :
    0 ≤ normalizedBankPrimeCarrier s x := by
  rw [normalizedBankPrimeCarrier]
  exact div_nonneg (bankPrimeReciprocalCumulative_nonneg s x) (mellinClock_pos x).le

/-- Every normalized survivor potential is controlled by its whole bank mass at the minimal
Mellin clock `log 2`. -/
theorem normalizedBankPrimeCarrier_le_mass_div_log_two (s : Finset ℕ) (x : ℕ) :
    normalizedBankPrimeCarrier s x ≤
      primeHarmonicMass s / Real.log 2 := by
  have hmass0 : 0 ≤ primeHarmonicMass s := by
    rw [primeHarmonicMass]
    exact sum_nonneg fun _ _ ↦ by positivity
  rw [normalizedBankPrimeCarrier]
  calc
    bankPrimeReciprocalCumulative s x / mellinClock x ≤
        primeHarmonicMass s / mellinClock x :=
      div_le_div_of_nonneg_right
        (bankPrimeReciprocalCumulative_le_primeHarmonicMass s x)
        (mellinClock_pos x).le
    _ ≤ primeHarmonicMass s / Real.log 2 :=
      div_le_div_of_nonneg_left hmass0 (Real.log_pos (by norm_num))
        (log_two_le_mellinClock x)

/-- Fully local harmonic scaling: every cumulative contribution keeps the clock of its own
prime cutoff, rather than paying the global worst-case denominator `log 2`. -/
theorem normalizedBankPrimeCarrier_le_primeMellinMass (s : Finset ℕ) (x : ℕ) :
    normalizedBankPrimeCarrier s x ≤ primeMellinMass s := by
  rw [normalizedBankPrimeCarrier, bankPrimeReciprocalCumulative, primeMellinMass,
    Finset.sum_div]
  calc
    (∑ p ∈ s ∩ x.primesLE, ((1 : ℝ) / (p : ℝ)) / mellinClock x) ≤
        ∑ p ∈ s ∩ x.primesLE, ((1 : ℝ) / (p : ℝ)) / mellinClock p := by
          apply sum_le_sum
          intro p hp
          have hpx : p ≤ x := (Nat.mem_primesLE.mp (mem_inter.mp hp).2).1
          exact div_le_div_of_nonneg_left (by positivity) (mellinClock_pos p)
            (mellinClock_mono hpx)
    _ ≤ ∑ p ∈ s, ((1 : ℝ) / (p : ℝ)) / mellinClock p :=
      Finset.sum_le_sum_of_subset_of_nonneg inter_subset_left (by
        intro p _ _
        exact div_nonneg (by positivity) (mellinClock_pos p).le)

/-- The exact quotient-prefix partition after retaining every prime's local Mellin clock. -/
theorem sum_dynamicPrefixPrimeBank_primeMellinMass
    (s : Finset ℕ) (n j : ℕ) :
    ∑ m ∈ range (n + 1), primeMellinMass (dynamicPrefixPrimeBank s n j m) =
      primeMellinMass (dynamicSurvivingPrimeBank s n j) := by
  classical
  have hmaps : ∀ p ∈ dynamicSurvivingPrimeBank s n j,
      quotientPrefix n j p ∈ range (n + 1) := by
    intro p _
    exact mem_range.mpr ((Nat.div_le_self n (p ^ (j + 1))).trans_lt (Nat.lt_succ_self n))
  rw [primeMellinMass]
  calc
    (∑ m ∈ range (n + 1),
        primeMellinMass (dynamicPrefixPrimeBank s n j m)) =
      ∑ m ∈ range (n + 1),
        ∑ p ∈ dynamicSurvivingPrimeBank s n j with quotientPrefix n j p = m,
          ((1 : ℝ) / (p : ℝ)) / mellinClock p := by
            apply sum_congr rfl
            intro m _
            rfl
    _ = ∑ p ∈ dynamicSurvivingPrimeBank s n j,
        ((1 : ℝ) / (p : ℝ)) / mellinClock p := by
      exact Finset.sum_fiberwise_of_maps_to hmaps _

/-- Lossless normalization: multiplying by the local Mellin clock recovers the cumulative mass. -/
theorem mellinClock_mul_normalizedBankPrimeCarrier (s : Finset ℕ) (x : ℕ) :
    mellinClock x * normalizedBankPrimeCarrier s x = bankPrimeReciprocalCumulative s x := by
  rw [normalizedBankPrimeCarrier]
  field_simp [mellinClock_ne_zero]

/-- Product-rule correction caused by changing logarithmic scale across one reciprocal cell. -/
noncomputable def mellinCellGradientAdapter (s : Finset ℕ) (m k : ℕ) : ℝ :=
  (mellinClock (reciprocalCellHigh m k) - mellinClock (reciprocalCellMid m k)) *
      normalizedBankPrimeCarrier s (reciprocalCellHigh m k) +
    (mellinClock (reciprocalCellLow m k) - mellinClock (reciprocalCellMid m k)) *
      normalizedBankPrimeCarrier s (reciprocalCellLow m k)

/-- The part of the Mellin adapter caused by changes in the sampled survivor potential rather
than by curvature of the logarithmic clock itself. -/
noncomputable def mellinCellSamplingAdapter (s : Finset ℕ) (m k : ℕ) : ℝ :=
  (mellinClock (reciprocalCellHigh m k) - mellinClock (reciprocalCellMid m k)) *
      (normalizedBankPrimeCarrier s (reciprocalCellHigh m k) -
        normalizedBankPrimeCarrier s (reciprocalCellMid m k)) +
    (mellinClock (reciprocalCellLow m k) - mellinClock (reciprocalCellMid m k)) *
      (normalizedBankPrimeCarrier s (reciprocalCellLow m k) -
        normalizedBankPrimeCarrier s (reciprocalCellMid m k))

/-- Pure clock-curvature part of the Mellin adapter. -/
noncomputable def mellinCellClockCurvature (s : Finset ℕ) (m k : ℕ) : ℝ :=
  normalizedBankPrimeCarrier s (reciprocalCellMid m k) *
    (mellinClock (reciprocalCellHigh m k) -
      2 * mellinClock (reciprocalCellMid m k) +
        mellinClock (reciprocalCellLow m k))

/-- Continuous reflected-residual part of the clock curvature. -/
noncomputable def mellinCellContinuousClockCurvature
    (s : Finset ℕ) (m k : ℕ) : ℝ :=
  normalizedBankPrimeCarrier s (reciprocalCellMid m k) *
    harmonicContourResidual (k : ℝ)

/-- One quotient packet has at most one quarter-unit of continuous Mellin clock curvature,
scaled only by the total harmonic mass of its prime bank. -/
theorem sum_Ico_abs_mellinCellContinuousClockCurvature_le
    (s : Finset ℕ) (m : ℕ) :
    ∑ k ∈ Ico 1 (m + 1), |mellinCellContinuousClockCurvature s m k| ≤
      (primeHarmonicMass s / Real.log 2) * ((1 : ℝ) / 4) := by
  have hmass0 : 0 ≤ primeHarmonicMass s := by
    rw [primeHarmonicMass]
    exact sum_nonneg fun _ _ ↦ by positivity
  have hscale0 : 0 ≤ primeHarmonicMass s / Real.log 2 :=
    div_nonneg hmass0 (Real.log_pos (by norm_num)).le
  calc
    (∑ k ∈ Ico 1 (m + 1), |mellinCellContinuousClockCurvature s m k|) =
        ∑ k ∈ Ico 1 (m + 1),
          normalizedBankPrimeCarrier s (reciprocalCellMid m k) *
            harmonicContourResidual (k : ℝ) := by
              apply sum_congr rfl
              intro k hk
              rw [mellinCellContinuousClockCurvature, abs_of_nonneg]
              exact mul_nonneg (normalizedBankPrimeCarrier_nonneg _ _)
                (harmonicContourResidual_nonneg_le
                  (show (0 : ℝ) < (k : ℝ) by exact_mod_cast (mem_Ico.mp hk).1)).1
    _ ≤ ∑ k ∈ Ico 1 (m + 1),
        (primeHarmonicMass s / Real.log 2) * harmonicContourResidual (k : ℝ) := by
          apply sum_le_sum
          intro k hk
          exact mul_le_mul_of_nonneg_right
            (normalizedBankPrimeCarrier_le_mass_div_log_two s (reciprocalCellMid m k))
            (harmonicContourResidual_nonneg_le
              (show (0 : ℝ) < (k : ℝ) by exact_mod_cast (mem_Ico.mp hk).1)).1
    _ = (primeHarmonicMass s / Real.log 2) *
        ∑ k ∈ Ico 1 (m + 1), harmonicContourResidual (k : ℝ) := by
          rw [Finset.mul_sum]
    _ ≤ (primeHarmonicMass s / Real.log 2) * ((1 : ℝ) / 4) :=
      mul_le_mul_of_nonneg_left (sum_Ico_harmonicContourResidual_le_quarter m) hscale0

/-- Fully harmonically scaled packet bound.  Retaining each prime's own Mellin clock replaces
the coarse harmonic bank mass by the summable measure `1/(p log p)`. -/
theorem sum_Ico_abs_mellinCellContinuousClockCurvature_le_primeMellinMass
    (s : Finset ℕ) (m : ℕ) :
    ∑ k ∈ Ico 1 (m + 1), |mellinCellContinuousClockCurvature s m k| ≤
      primeMellinMass s * ((1 : ℝ) / 4) := by
  have hmass0 : 0 ≤ primeMellinMass s := primeMellinMass_nonneg s
  calc
    (∑ k ∈ Ico 1 (m + 1), |mellinCellContinuousClockCurvature s m k|) =
        ∑ k ∈ Ico 1 (m + 1),
          normalizedBankPrimeCarrier s (reciprocalCellMid m k) *
            harmonicContourResidual (k : ℝ) := by
              apply sum_congr rfl
              intro k hk
              rw [mellinCellContinuousClockCurvature, abs_of_nonneg]
              exact mul_nonneg (normalizedBankPrimeCarrier_nonneg _ _)
                (harmonicContourResidual_nonneg_le
                  (show (0 : ℝ) < (k : ℝ) by exact_mod_cast (mem_Ico.mp hk).1)).1
    _ ≤ ∑ k ∈ Ico 1 (m + 1),
        primeMellinMass s * harmonicContourResidual (k : ℝ) := by
          apply sum_le_sum
          intro k hk
          exact mul_le_mul_of_nonneg_right
            (normalizedBankPrimeCarrier_le_primeMellinMass s (reciprocalCellMid m k))
            (harmonicContourResidual_nonneg_le
              (show (0 : ℝ) < (k : ℝ) by exact_mod_cast (mem_Ico.mp hk).1)).1
    _ = primeMellinMass s *
        ∑ k ∈ Ico 1 (m + 1), harmonicContourResidual (k : ℝ) := by
          rw [Finset.mul_sum]
    _ ≤ primeMellinMass s * ((1 : ℝ) / 4) :=
      mul_le_mul_of_nonneg_left (sum_Ico_harmonicContourResidual_le_quarter m) hmass0

/-- Integer-floor quantization part of the clock curvature. -/
noncomputable def mellinCellClockQuantizationCurvature
    (s : Finset ℕ) (m k : ℕ) : ℝ :=
  normalizedBankPrimeCarrier s (reciprocalCellMid m k) *
    (mellinHighClockQuantizationError m k -
      2 * mellinMidClockQuantizationError m k +
        mellinLowClockQuantizationError m k)

/-- Exact split of discrete clock curvature into the reflected continuous carrier and integer
floor quantization. -/
theorem mellinCellClockCurvature_eq_continuous_add_quantization
    (s : Finset ℕ) {m k : ℕ} (hm : 0 < m) (hk : 0 < k) :
    mellinCellClockCurvature s m k =
      mellinCellContinuousClockCurvature s m k +
        mellinCellClockQuantizationCurvature s m k := by
  simp only [mellinCellClockCurvature, mellinCellContinuousClockCurvature,
    mellinCellClockQuantizationCurvature]
  rw [mellinClock_secondDifference_eq_residual_add_quantization hm hk]
  ring

/-- Exact separation of arithmetic sampling from logarithmic carrier curvature. -/
theorem mellinCellGradientAdapter_eq_sampling_add_clockCurvature
    (s : Finset ℕ) (m k : ℕ) :
    mellinCellGradientAdapter s m k =
      mellinCellSamplingAdapter s m k + mellinCellClockCurvature s m k := by
  simp only [mellinCellGradientAdapter, mellinCellSamplingAdapter,
    mellinCellClockCurvature]
  ring

/-- Fully scaled cell ledger: normalized curvature transported at the midpoint clock plus both
clock-gradient adapters. -/
noncomputable def mellinCellReconstruction (s : Finset ℕ) (m k : ℕ) : ℝ :=
  mellinClock (reciprocalCellMid m k) *
      reciprocalCellSecondDifference (normalizedBankPrimeCarrier s) m k +
    mellinCellGradientAdapter s m k

/-- Exact discrete Mellin product rule.  This is the lossless adapter between the raw cumulative
cell ledger and its completely logarithmic normalization. -/
theorem mellinCellReconstruction_eq_secondDifference (s : Finset ℕ) (m k : ℕ) :
    mellinCellReconstruction s m k =
      reciprocalCellSecondDifference (bankPrimeReciprocalCumulative s) m k := by
  simp only [mellinCellReconstruction, mellinCellGradientAdapter,
    reciprocalCellSecondDifference]
  rw [← mellinClock_mul_normalizedBankPrimeCarrier s (reciprocalCellHigh m k),
    ← mellinClock_mul_normalizedBankPrimeCarrier s (reciprocalCellMid m k),
    ← mellinClock_mul_normalizedBankPrimeCarrier s (reciprocalCellLow m k)]
  ring

/-- Reverse product-rule estimate on one cell: full Mellin variation is the raw signed-cell
variation plus at most two copies of the scale-gradient adapter. -/
theorem mellinCell_components_le_secondDifference_add_two_adapters
    (s : Finset ℕ) (m k : ℕ) :
    |mellinClock (reciprocalCellMid m k) *
        reciprocalCellSecondDifference (normalizedBankPrimeCarrier s) m k| +
      |mellinCellGradientAdapter s m k| ≤
      |reciprocalCellSecondDifference (bankPrimeReciprocalCumulative s) m k| +
        |mellinCellGradientAdapter s m k| + |mellinCellGradientAdapter s m k| := by
  have hreconstruct := mellinCellReconstruction_eq_secondDifference s m k
  rw [mellinCellReconstruction] at hreconstruct
  have hcurvature :
      mellinClock (reciprocalCellMid m k) *
          reciprocalCellSecondDifference (normalizedBankPrimeCarrier s) m k =
        reciprocalCellSecondDifference (bankPrimeReciprocalCumulative s) m k -
          mellinCellGradientAdapter s m k := by
    linarith
  rw [hcurvature]
  linarith [abs_sub
    (reciprocalCellSecondDifference (bankPrimeReciprocalCumulative s) m k)
    (mellinCellGradientAdapter s m k)]

/-- Absolute normalized-curvature contribution of all complete cells. -/
noncomputable def recursiveMellinCurvatureVariation (s : Finset ℕ) (n j : ℕ) : ℝ :=
  ∑ m ∈ range (n + 1),
    ∑ k ∈ Ico 1 (m + 1),
      |mellinClock (reciprocalCellMid m k) *
        reciprocalCellSecondDifference
          (normalizedBankPrimeCarrier (dynamicPrefixPrimeBank s n j m)) m k|

/-- Absolute scale-gradient cost of the full Mellin conversion. -/
noncomputable def recursiveMellinAdapterVariation (s : Finset ℕ) (n j : ℕ) : ℝ :=
  ∑ m ∈ range (n + 1),
    ∑ k ∈ Ico 1 (m + 1),
      |mellinCellGradientAdapter (dynamicPrefixPrimeBank s n j m) m k|

/-- Recursive variation of only the survivor-sampling component of the Mellin adapter. -/
noncomputable def recursiveMellinSamplingAdapterVariation
    (s : Finset ℕ) (n j : ℕ) : ℝ :=
  ∑ m ∈ range (n + 1),
    ∑ k ∈ Ico 1 (m + 1),
      |mellinCellSamplingAdapter (dynamicPrefixPrimeBank s n j m) m k|

/-- Recursive variation of only the logarithmic clock-curvature component. -/
noncomputable def recursiveMellinClockCurvatureVariation
    (s : Finset ℕ) (n j : ℕ) : ℝ :=
  ∑ m ∈ range (n + 1),
    ∑ k ∈ Ico 1 (m + 1),
      |mellinCellClockCurvature (dynamicPrefixPrimeBank s n j m) m k|

/-- Recursive continuous reflected-residual clock variation. -/
noncomputable def recursiveMellinContinuousClockCurvatureVariation
    (s : Finset ℕ) (n j : ℕ) : ℝ :=
  ∑ m ∈ range (n + 1),
    ∑ k ∈ Ico 1 (m + 1),
      |mellinCellContinuousClockCurvature (dynamicPrefixPrimeBank s n j m) m k|

/-- The complete continuous clock ledger is a fixed fraction of the surviving dynamic energy.
This is the harmonic-scale contraction supplied by the triangular contour primitive. -/
theorem recursiveMellinContinuousClockCurvatureVariation_le_dynamicBankEnergy
    (s : Finset ℕ) (n j : ℕ) :
    recursiveMellinContinuousClockCurvatureVariation s n j ≤
      (dynamicBankEnergy s n j / Real.log 2) * ((1 : ℝ) / 4) := by
  rw [recursiveMellinContinuousClockCurvatureVariation]
  calc
    (∑ m ∈ range (n + 1),
        ∑ k ∈ Ico 1 (m + 1),
          |mellinCellContinuousClockCurvature
            (dynamicPrefixPrimeBank s n j m) m k|) ≤
      ∑ m ∈ range (n + 1),
        (primeHarmonicMass (dynamicPrefixPrimeBank s n j m) / Real.log 2) *
          ((1 : ℝ) / 4) := by
            apply sum_le_sum
            intro m _
            exact sum_Ico_abs_mellinCellContinuousClockCurvature_le
              (dynamicPrefixPrimeBank s n j m) m
    _ = ((∑ m ∈ range (n + 1),
        primeHarmonicMass (dynamicPrefixPrimeBank s n j m)) / Real.log 2) *
          ((1 : ℝ) / 4) := by
            rw [← Finset.sum_mul, ← Finset.sum_div]
    _ = (dynamicBankEnergy s n j / Real.log 2) * ((1 : ℝ) / 4) := by
      rw [sum_dynamicPrefixPrimeBank_primeHarmonicMass,
        dynamicBankEnergy_eq_survivingPrimeHarmonicMass]

/-- Fully scaled recursive curvature is controlled by the summable Mellin mass of the ambient
prime bank, uniformly in the quotient depth and in all prefix fibers. -/
theorem recursiveMellinContinuousClockCurvatureVariation_le_primeMellinMass
    (s : Finset ℕ) (n j : ℕ) :
    recursiveMellinContinuousClockCurvatureVariation s n j ≤
      primeMellinMass s * ((1 : ℝ) / 4) := by
  rw [recursiveMellinContinuousClockCurvatureVariation]
  calc
    (∑ m ∈ range (n + 1),
        ∑ k ∈ Ico 1 (m + 1),
          |mellinCellContinuousClockCurvature
            (dynamicPrefixPrimeBank s n j m) m k|) ≤
      ∑ m ∈ range (n + 1),
        primeMellinMass (dynamicPrefixPrimeBank s n j m) * ((1 : ℝ) / 4) := by
          apply sum_le_sum
          intro m _
          exact sum_Ico_abs_mellinCellContinuousClockCurvature_le_primeMellinMass
            (dynamicPrefixPrimeBank s n j m) m
    _ = primeMellinMass (dynamicSurvivingPrimeBank s n j) * ((1 : ℝ) / 4) := by
      rw [← Finset.sum_mul, sum_dynamicPrefixPrimeBank_primeMellinMass]
    _ ≤ primeMellinMass s * ((1 : ℝ) / 4) := by
      apply mul_le_mul_of_nonneg_right _ (by norm_num)
      apply primeMellinMass_mono
      intro p hp
      exact (mem_filter.mp hp).1

/-- Recursive integer-floor clock-quantization variation. -/
noncomputable def recursiveMellinClockQuantizationVariation
    (s : Finset ℕ) (n j : ℕ) : ℝ :=
  ∑ m ∈ range (n + 1),
    ∑ k ∈ Ico 1 (m + 1),
      |mellinCellClockQuantizationCurvature (dynamicPrefixPrimeBank s n j m) m k|

/-- Recursive discrete clock curvature is controlled by the continuous residual and its explicit
integer-floor quantization error. -/
theorem recursiveMellinClockCurvatureVariation_le_continuous_add_quantization
    (s : Finset ℕ) (n j : ℕ) :
    recursiveMellinClockCurvatureVariation s n j ≤
      recursiveMellinContinuousClockCurvatureVariation s n j +
        recursiveMellinClockQuantizationVariation s n j := by
  rw [recursiveMellinClockCurvatureVariation,
    recursiveMellinContinuousClockCurvatureVariation,
    recursiveMellinClockQuantizationVariation, ← sum_add_distrib]
  apply sum_le_sum
  intro m _
  rw [← sum_add_distrib]
  apply sum_le_sum
  intro k hk
  have hkpos : 0 < k := (mem_Ico.mp hk).1
  have hmpos : 0 < m := by
    have hklt : k < m + 1 := (mem_Ico.mp hk).2
    omega
  rw [mellinCellClockCurvature_eq_continuous_add_quantization
    (dynamicPrefixPrimeBank s n j m) hmpos hkpos]
  exact abs_add_le _ _

/-- The exact adapter split remains subadditive after taking recursive total variation. -/
theorem recursiveMellinAdapterVariation_le_sampling_add_clockCurvature
    (s : Finset ℕ) (n j : ℕ) :
    recursiveMellinAdapterVariation s n j ≤
      recursiveMellinSamplingAdapterVariation s n j +
        recursiveMellinClockCurvatureVariation s n j := by
  rw [recursiveMellinAdapterVariation, recursiveMellinSamplingAdapterVariation,
    recursiveMellinClockCurvatureVariation, ← sum_add_distrib]
  apply sum_le_sum
  intro m _
  rw [← sum_add_distrib]
  apply sum_le_sum
  intro k _
  rw [mellinCellGradientAdapter_eq_sampling_add_clockCurvature]
  exact abs_add_le _ _

/-- Full harmonic scaling cannot hide raw variation: after restoring the scale-gradient adapters,
the original complete-cell variation is bounded by the sum of the two Mellin components. -/
theorem recursiveWarpedInteriorVariation_le_mellinComponents
    (s : Finset ℕ) (n j : ℕ) :
    recursiveWarpedInteriorVariation s n j ≤
      recursiveMellinCurvatureVariation s n j +
        recursiveMellinAdapterVariation s n j := by
  rw [recursiveWarpedInteriorVariation, recursiveMellinCurvatureVariation,
    recursiveMellinAdapterVariation, ← sum_add_distrib]
  apply sum_le_sum
  intro m _
  rw [← sum_add_distrib]
  apply sum_le_sum
  intro k _
  rw [← mellinCellReconstruction_eq_secondDifference
    (dynamicPrefixPrimeBank s n j m) m k, mellinCellReconstruction]
  exact abs_add_le _ _

/-- The full recursive Mellin norm differs from raw warped variation only by the explicitly
isolated double adapter cost. -/
theorem mellinComponents_le_recursiveWarpedInteriorVariation_add_two_adapters
    (s : Finset ℕ) (n j : ℕ) :
    recursiveMellinCurvatureVariation s n j +
        recursiveMellinAdapterVariation s n j ≤
      recursiveWarpedInteriorVariation s n j +
        recursiveMellinAdapterVariation s n j +
          recursiveMellinAdapterVariation s n j := by
  rw [recursiveMellinCurvatureVariation, recursiveMellinAdapterVariation,
    recursiveWarpedInteriorVariation, ← sum_add_distrib]
  calc
    _ = ∑ m ∈ range (n + 1),
        ∑ k ∈ Ico 1 (m + 1),
          (|mellinClock (reciprocalCellMid m k) *
              reciprocalCellSecondDifference
                (normalizedBankPrimeCarrier (dynamicPrefixPrimeBank s n j m)) m k| +
            |mellinCellGradientAdapter (dynamicPrefixPrimeBank s n j m) m k|) := by
          apply sum_congr rfl
          intro m _
          rw [sum_add_distrib]
    _ ≤ ∑ m ∈ range (n + 1),
        ∑ k ∈ Ico 1 (m + 1),
          (|reciprocalCellSecondDifference
              (bankPrimeReciprocalCumulative (dynamicPrefixPrimeBank s n j m)) m k| +
            |mellinCellGradientAdapter (dynamicPrefixPrimeBank s n j m) m k| +
            |mellinCellGradientAdapter (dynamicPrefixPrimeBank s n j m) m k|) := by
          apply sum_le_sum
          intro m _
          apply sum_le_sum
          intro k _
          exact mellinCell_components_le_secondDifference_add_two_adapters
            (dynamicPrefixPrimeBank s n j m) m k
    _ = (∑ m ∈ range (n + 1),
          ∑ k ∈ Ico 1 (m + 1),
            |reciprocalCellSecondDifference
              (bankPrimeReciprocalCumulative (dynamicPrefixPrimeBank s n j m)) m k|) +
        (∑ m ∈ range (n + 1),
          ∑ k ∈ Ico 1 (m + 1),
            |mellinCellGradientAdapter (dynamicPrefixPrimeBank s n j m) m k|) +
        ∑ m ∈ range (n + 1),
          ∑ k ∈ Ico 1 (m + 1),
            |mellinCellGradientAdapter (dynamicPrefixPrimeBank s n j m) m k| := by
          simp only [sum_add_distrib]

/-- The entire recursive ledger with every complete cell expressed on the normalized Mellin
carrier.  Boundary packets remain explicit until their terminal root-drift conversion. -/
noncomputable def fullyMellinReconstructedLedger (s : Finset ℕ) (n j : ℕ) : ℝ :=
  ∑ m ∈ range (n + 1),
    (dynamicPrefixBoundaryLedger s n j m +
      ∑ k ∈ Ico 1 (m + 1),
        mellinCellReconstruction (dynamicPrefixPrimeBank s n j m) m k)

/-- Lossless whole-ledger Mellin adapter. -/
theorem fullyMellinReconstructedLedger_eq_recursiveWarpedLedger
    (s : Finset ℕ) (n j : ℕ) :
    fullyMellinReconstructedLedger s n j = recursiveWarpedLedger s n j := by
  rw [fullyMellinReconstructedLedger, recursiveWarpedLedger]
  apply sum_congr rfl
  intro m _
  congr 1
  apply sum_congr rfl
  intro k _
  exact mellinCellReconstruction_eq_secondDifference (dynamicPrefixPrimeBank s n j m) m k

/-- Exact variation adapter: a recursive signed ledger is bounded by its explicit boundary mass
plus the warped variation of its complete-cell survivor potentials. -/
theorem abs_recursiveWarpedLedger_le_boundary_add_variation
    (s : Finset ℕ) (n j : ℕ) :
    |recursiveWarpedLedger s n j| ≤
      recursiveWarpedBoundaryMass s n j + recursiveWarpedInteriorVariation s n j := by
  rw [recursiveWarpedLedger, recursiveWarpedBoundaryMass, recursiveWarpedInteriorVariation]
  calc
    |∑ m ∈ range (n + 1),
        (dynamicPrefixBoundaryLedger s n j m +
          ∑ k ∈ Ico 1 (m + 1),
            reciprocalCellSecondDifference
              (bankPrimeReciprocalCumulative (dynamicPrefixPrimeBank s n j m)) m k)| ≤
      ∑ m ∈ range (n + 1),
        |dynamicPrefixBoundaryLedger s n j m +
          ∑ k ∈ Ico 1 (m + 1),
            reciprocalCellSecondDifference
              (bankPrimeReciprocalCumulative (dynamicPrefixPrimeBank s n j m)) m k| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ m ∈ range (n + 1),
        (|dynamicPrefixBoundaryLedger s n j m| +
          ∑ k ∈ Ico 1 (m + 1),
            |reciprocalCellSecondDifference
              (bankPrimeReciprocalCumulative (dynamicPrefixPrimeBank s n j m)) m k|) := by
          apply sum_le_sum
          intro m _
          exact (abs_add_le _ _).trans (add_le_add_right (Finset.abs_sum_le_sum_abs _ _) _)
    _ = (∑ m ∈ range (n + 1), |dynamicPrefixBoundaryLedger s n j m|) +
        ∑ m ∈ range (n + 1),
          ∑ k ∈ Ico 1 (m + 1),
            |reciprocalCellSecondDifference
              (bankPrimeReciprocalCumulative (dynamicPrefixPrimeBank s n j m)) m k| := by
          rw [sum_add_distrib]

/-- Full Mellin variation bound, including every clock-gradient correction. -/
theorem abs_fullyMellinReconstructedLedger_le
    (s : Finset ℕ) (n j : ℕ) :
    |fullyMellinReconstructedLedger s n j| ≤
      recursiveWarpedBoundaryMass s n j +
        (recursiveMellinCurvatureVariation s n j +
          recursiveMellinAdapterVariation s n j) := by
  rw [fullyMellinReconstructedLedger_eq_recursiveWarpedLedger]
  exact (abs_recursiveWarpedLedger_le_boundary_add_variation s n j).trans
    (add_le_add_right (recursiveWarpedInteriorVariation_le_mellinComponents s n j) _)

/-- Exact recursive harmonic conversion of one dynamic signed ledger. -/
theorem dynamicBankSignedLedger_eq_recursiveWarpedLedger
    {s : Finset ℕ} {n j : ℕ} (hprimes : s ⊆ n.primesLE) :
    dynamicBankSignedLedger s n j = recursiveWarpedLedger s n j := by
  classical
  rw [dynamicBankSignedLedger_eq_survivingQuotientSum hprimes, recursiveWarpedLedger]
  have hmaps : ∀ p ∈ dynamicSurvivingPrimeBank s n j,
      quotientPrefix n j p ∈ range (n + 1) := by
    intro p _
    exact mem_range.mpr ((Nat.div_le_self n (p ^ (j + 1))).trans_lt (Nat.lt_succ_self n))
  calc
    (∑ p ∈ dynamicSurvivingPrimeBank s n j,
        (1 : ℝ) / (p : ℝ) * quotientDigitSign (quotientPrefix n j p) p) =
      ∑ m ∈ range (n + 1),
        ∑ p ∈ dynamicSurvivingPrimeBank s n j with quotientPrefix n j p = m,
          (1 : ℝ) / (p : ℝ) * quotientDigitSign (quotientPrefix n j p) p := by
            symm
            exact Finset.sum_fiberwise_of_maps_to hmaps _
    _ = ∑ m ∈ range (n + 1),
        ∑ p ∈ dynamicPrefixPrimeBank s n j m,
          (1 : ℝ) / (p : ℝ) * quotientDigitSign m p := by
            apply sum_congr rfl
            intro m _
            apply sum_congr rfl
            intro p hp
            rw [(mem_filter.mp hp).2]
    _ = ∑ m ∈ range (n + 1),
        (dynamicPrefixBoundaryLedger s n j m +
          ∑ k ∈ Ico 1 (m + 1),
            reciprocalCellSecondDifference
              (bankPrimeReciprocalCumulative (dynamicPrefixPrimeBank s n j m)) m k) := by
            apply sum_congr rfl
            intro m _
            exact dynamicPrefixPrimeBank_eq_boundary_add_secondDifferences hprimes

/-- The raw depth band is a prime sub-bank of `n.primesLE`. -/
theorem railBand_subset_primesLE (n r : ℕ) : railBand n r ⊆ n.primesLE := by
  intro p hp
  exact (mem_filter.mp hp).1

/-- Before the terminal digit of a depth-`r` rail, the quotient prefix is at least the prime, so
the exceptional reciprocal cell `k=0` cannot occur. -/
theorem railBand_le_quotientPrefix {p n r j : ℕ} (hrail : p ∈ railBand n r)
    (hj : j + 1 < r) :
    p ≤ quotientPrefix n j p := by
  have hpprime := Nat.prime_of_mem_primesLE ((mem_filter.mp hrail).1)
  have hlog : Nat.log p n = r := (mem_filter.mp hrail).2
  have hnpos : 0 < n := hpprime.pos.trans_le
    (Nat.le_of_mem_primesLE ((mem_filter.mp hrail).1))
  have hpowr : p ^ r ≤ n := by
    rw [← hlog]
    exact Nat.pow_log_le_self p hnpos.ne'
  rw [quotientPrefix]
  apply (Nat.le_div_iff_mul_le (pow_pos hpprime.pos _)).mpr
  calc
    p * p ^ (j + 1) = p ^ (j + 2) := by
      simp only [pow_succ']
    _ ≤ p ^ r := Nat.pow_le_pow_right hpprime.pos (by omega)
    _ ≤ n := hpowr

/-- Every nonterminal dynamic prefix has an empty `k=0` boundary bank. -/
theorem railBand_dynamicPrefixBoundaryPrimeBank_eq_empty
    {n r j m : ℕ} (hj : j + 1 < r) :
    dynamicPrefixBoundaryPrimeBank (railBand n r) n j m = ∅ := by
  classical
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro p hpmem
  have hp := mem_filter.mp hpmem
  have hprefix := mem_filter.mp hp.1
  have hsurvive := mem_filter.mp hprefix.1
  have hle := railBand_le_quotientPrefix hsurvive.1 hj
  rw [hprefix.2] at hle
  omega

/-- The nonterminal `k=0` boundary is empty for every sub-bank of a fixed depth rail. -/
theorem dynamicPrefixBoundaryPrimeBank_eq_empty_of_subset_railBand
    {s : Finset ℕ} {n r j m : ℕ} (hs : s ⊆ railBand n r) (hj : j + 1 < r) :
    dynamicPrefixBoundaryPrimeBank s n j m = ∅ := by
  classical
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro p hpmem
  have hp := mem_filter.mp hpmem
  have hprefix := mem_filter.mp hp.1
  have hsurvive := mem_filter.mp hprefix.1
  have hle := railBand_le_quotientPrefix (hs hsurvive.1) hj
  rw [hprefix.2] at hle
  omega

/-- Consequently every nonterminal recursive prefix has zero boundary ledger. -/
theorem railBand_dynamicPrefixBoundaryLedger_eq_zero
    {n r j m : ℕ} (hj : j + 1 < r) :
    dynamicPrefixBoundaryLedger (railBand n r) n j m = 0 := by
  rw [dynamicPrefixBoundaryLedger,
    railBand_dynamicPrefixBoundaryPrimeBank_eq_empty hj]
  simp

/-- Every nonterminal prefix boundary ledger of a depth-band sub-bank vanishes. -/
theorem dynamicPrefixBoundaryLedger_eq_zero_of_subset_railBand
    {s : Finset ℕ} {n r j m : ℕ} (hs : s ⊆ railBand n r) (hj : j + 1 < r) :
    dynamicPrefixBoundaryLedger s n j m = 0 := by
  rw [dynamicPrefixBoundaryLedger,
    dynamicPrefixBoundaryPrimeBank_eq_empty_of_subset_railBand hs hj]
  simp

/-- At the terminal digit, the quotient prefix is strictly smaller than the prime. -/
theorem railBand_quotientPrefix_lt_terminal {p n r j : ℕ} (hrail : p ∈ railBand n r)
    (hj : j + 1 = r) :
    quotientPrefix n j p < p := by
  have hpprime := Nat.prime_of_mem_primesLE ((mem_filter.mp hrail).1)
  have hlog : Nat.log p n = r := (mem_filter.mp hrail).2
  have hnpos : 0 < n := hpprime.pos.trans_le
    (Nat.le_of_mem_primesLE ((mem_filter.mp hrail).1))
  have hnlt : n < p ^ (r + 1) := by
    rw [← hlog]
    exact Nat.lt_pow_succ_log_self hpprime.one_lt n
  rw [quotientPrefix, hj]
  apply (Nat.div_lt_iff_lt_mul (pow_pos hpprime.pos _)).mpr
  calc
    n < p ^ (r + 1) := hnlt
    _ = p * p ^ r := by rw [pow_succ']

/-- The terminal prefix has no positive reciprocal-cell interior. -/
theorem railBand_dynamicPrefixInteriorPrimeBank_eq_empty
    {n r j m : ℕ} (hj : j + 1 = r) :
    dynamicPrefixInteriorPrimeBank (railBand n r) n j m = ∅ := by
  classical
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro p hpmem
  have hp := mem_filter.mp hpmem
  have hprefix := mem_filter.mp hp.1
  have hsurvive := mem_filter.mp hprefix.1
  have hlt := railBand_quotientPrefix_lt_terminal hsurvive.1 hj
  rw [hprefix.2] at hlt
  omega

/-- Thus a terminal prefix ledger is exactly its single `k=0` boundary packet. -/
theorem railBand_dynamicPrefixPrimeBank_terminal_eq_boundary
    {n r j m : ℕ} (hj : j + 1 = r) :
    (∑ p ∈ dynamicPrefixPrimeBank (railBand n r) n j m,
        (1 : ℝ) / (p : ℝ) * quotientDigitSign m p) =
      dynamicPrefixBoundaryLedger (railBand n r) n j m := by
  rw [dynamicPrefixPrimeBank_sum_eq_boundary_add_interior,
    railBand_dynamicPrefixInteriorPrimeBank_eq_empty hj]
  simp

/-- On a depth-`r` rail the terminal dynamic sign is the single geometric threshold
`2*n < p^(r+1)`. -/
theorem railBand_dynamicSquareSign_terminal {p n r j : ℕ} (hrail : p ∈ railBand n r)
    (hj : j + 1 = r) :
    dynamicSquareSign p n j = if 2 * n < p ^ (r + 1) then 1 else -1 := by
  have hpprime := Nat.prime_of_mem_primesLE ((mem_filter.mp hrail).1)
  have hlog : Nat.log p n = r := (mem_filter.mp hrail).2
  have hnlt : n < p ^ (r + 1) := by
    rw [← hlog]
    exact Nat.lt_pow_succ_log_self hpprime.one_lt n
  have hmod : n % p ^ (r + 1) = n := Nat.mod_eq_of_lt hnlt
  have hiff :
      harmonizedCellPhase p n r < harmonizedCircumference p / 2 ↔
        2 * n < p ^ (r + 1) := by
    rw [harmonizedCellPhase_lt_half_iff (n := n) (j := r) hpprime.pos, hmod]
  rw [dynamicSquareSign, hj]
  by_cases hphase : harmonizedCellPhase p n r < harmonizedCircumference p / 2
  · rw [if_pos hphase, if_pos (hiff.mp hphase)]
  · rw [if_neg hphase, if_neg (fun h ↦ hphase (hiff.mpr h))]

/-- Fully logarithmic form of the terminal square-wave sign. -/
theorem railBand_dynamicSquareSign_terminal_mellin
    {p n r j : ℕ} (hrail : p ∈ railBand n r) (hj : j + 1 = r) :
    dynamicSquareSign p n j = if 0 < terminalMellinDrift n r p then 1 else -1 := by
  have hpprime := Nat.prime_of_mem_primesLE ((mem_filter.mp hrail).1)
  have hnpos : 0 < n := hpprime.pos.trans_le
    (Nat.le_of_mem_primesLE ((mem_filter.mp hrail).1))
  rw [railBand_dynamicSquareSign_terminal hrail hj]
  have hiff := terminalMellinDrift_pos_iff (r := r) hnpos hpprime.pos
  by_cases hthreshold : 2 * n < p ^ (r + 1)
  · rw [if_pos hthreshold, if_pos (hiff.mpr hthreshold)]
  · rw [if_neg hthreshold, if_neg (fun h ↦ hthreshold (hiff.mp h))]

/-- On coherent powers the terminal Mellin distance is constant rather than depth-decaying. -/
theorem terminalMellinDrift_three_pow (r : ℕ) :
    terminalMellinDrift (3 ^ r) r 3 = Real.log 3 - Real.log 2 := by
  rw [terminalMellinDrift]
  simp only [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat, Nat.cast_mul, Nat.cast_pow]
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by positivity), Real.log_pow]
  ring

theorem terminalMellinDrift_three_pow_pos (r : ℕ) :
    0 < terminalMellinDrift (3 ^ r) r 3 := by
  rw [terminalMellinDrift_three_pow]
  exact sub_pos.mpr (Real.log_lt_log (by norm_num) (by norm_num))

/-- The terminal ledger is the reciprocal mass imbalance of the prior survivor bank across the
single root threshold `p^(r+1)=2*n`. -/
theorem railBand_dynamicBankSignedLedger_terminal_eq_threshold
    {n r j : ℕ} (hj : j + 1 = r) :
    dynamicBankSignedLedger (railBand n r) n j =
      ∑ p ∈ dynamicSurvivingPrimeBank (railBand n r) n j,
        (1 : ℝ) / (p : ℝ) * (if 2 * n < p ^ (r + 1) then 1 else -1) := by
  rw [dynamicBankSignedLedger_eq_survivingSum]
  apply sum_congr rfl
  intro p hp
  have hsurvive := mem_filter.mp hp
  rw [railBand_dynamicSquareSign_terminal hsurvive.1 hj]

/-- Every nonterminal recursive ledger consists only of complete-cell second differences. -/
theorem railBand_recursiveWarpedLedger_nonterminal
    {n r j : ℕ} (hj : j + 1 < r) :
    recursiveWarpedLedger (railBand n r) n j =
      ∑ m ∈ range (n + 1),
        ∑ k ∈ Ico 1 (m + 1),
          reciprocalCellSecondDifference
            (bankPrimeReciprocalCumulative
              (dynamicPrefixPrimeBank (railBand n r) n j m)) m k := by
  rw [recursiveWarpedLedger]
  apply sum_congr rfl
  intro m _
  rw [railBand_dynamicPrefixBoundaryLedger_eq_zero hj, zero_add]

/-- The total exceptional boundary mass vanishes before the terminal digit. -/
theorem railBand_recursiveWarpedBoundaryMass_nonterminal_eq_zero
    {n r j : ℕ} (hj : j + 1 < r) :
    recursiveWarpedBoundaryMass (railBand n r) n j = 0 := by
  rw [recursiveWarpedBoundaryMass]
  apply sum_eq_zero
  intro m _
  rw [railBand_dynamicPrefixBoundaryLedger_eq_zero hj, abs_zero]

/-- The total exceptional boundary mass vanishes on every nonterminal depth-band sub-bank. -/
theorem recursiveWarpedBoundaryMass_nonterminal_eq_zero_of_subset_railBand
    {s : Finset ℕ} {n r j : ℕ} (hs : s ⊆ railBand n r) (hj : j + 1 < r) :
    recursiveWarpedBoundaryMass s n j = 0 := by
  rw [recursiveWarpedBoundaryMass]
  apply sum_eq_zero
  intro m _
  rw [dynamicPrefixBoundaryLedger_eq_zero_of_subset_railBand hs hj, abs_zero]

/-- On every nonterminal depth, the recursive signed ledger is controlled solely by the warped
variation of the evolving survivor-bank cumulative potentials. -/
theorem abs_railBand_recursiveWarpedLedger_nonterminal_le_variation
    {n r j : ℕ} (hj : j + 1 < r) :
    |recursiveWarpedLedger (railBand n r) n j| ≤
      recursiveWarpedInteriorVariation (railBand n r) n j := by
  have h := abs_recursiveWarpedLedger_le_boundary_add_variation (railBand n r) n j
  rw [railBand_recursiveWarpedBoundaryMass_nonterminal_eq_zero hj, zero_add] at h
  exact h

/-- Dwell-scaled nonterminal ledger bound.  This is the exact landing point for a warped-variation
estimate: the factor `2^-(r-j)` is already outside the survivor-bank variation. -/
theorem railBand_nonterminal_dwell_ledger_le_warpedVariation
    {n r j : ℕ} (hj : j + 1 < r) :
    |((1 : ℝ) / 2) ^ (r - j) * dynamicBankSignedLedger (railBand n r) n j| ≤
      ((1 : ℝ) / 2) ^ (r - j) *
        recursiveWarpedInteriorVariation (railBand n r) n j := by
  have hdwell : 0 ≤ ((1 : ℝ) / 2) ^ (r - j) := by positivity
  rw [dynamicBankSignedLedger_eq_recursiveWarpedLedger (railBand_subset_primesLE n r),
    abs_mul, abs_of_nonneg hdwell]
  exact mul_le_mul_of_nonneg_left
    (abs_railBand_recursiveWarpedLedger_nonterminal_le_variation hj) hdwell

/-- After full harmonic scaling, the same nonterminal dwell ledger is controlled by normalized
Mellin curvature plus the exact clock-gradient adapter cost. -/
theorem railBand_nonterminal_dwell_ledger_le_fullMellinVariation
    {n r j : ℕ} (hj : j + 1 < r) :
    |((1 : ℝ) / 2) ^ (r - j) * dynamicBankSignedLedger (railBand n r) n j| ≤
      ((1 : ℝ) / 2) ^ (r - j) *
        (recursiveMellinCurvatureVariation (railBand n r) n j +
          recursiveMellinAdapterVariation (railBand n r) n j) := by
  have hdwell : 0 ≤ ((1 : ℝ) / 2) ^ (r - j) := by positivity
  exact (railBand_nonterminal_dwell_ledger_le_warpedVariation hj).trans
    (mul_le_mul_of_nonneg_left
      (recursiveWarpedInteriorVariation_le_mellinComponents (railBand n r) n j) hdwell)

/-- Removing the outer dwell exposes the depth-independent Mellin variation estimate on every
nonterminal sub-bank. -/
theorem abs_dynamicBankSignedLedger_le_fullMellinVariation_of_subset_railBand
    {s : Finset ℕ} {n r j : ℕ} (hs : s ⊆ railBand n r) (hj : j + 1 < r) :
    |dynamicBankSignedLedger s n j| ≤
      recursiveMellinCurvatureVariation s n j +
        recursiveMellinAdapterVariation s n j := by
  have hprimes : s ⊆ n.primesLE :=
    hs.trans (railBand_subset_primesLE n r)
  rw [dynamicBankSignedLedger_eq_recursiveWarpedLedger hprimes,
    ← fullyMellinReconstructedLedger_eq_recursiveWarpedLedger]
  have h := abs_fullyMellinReconstructedLedger_le s n j
  rw [recursiveWarpedBoundaryMass_nonterminal_eq_zero_of_subset_railBand hs hj,
    zero_add] at h
  exact h

/-- Full Mellin variation bound for every nonterminal sub-bank of a fixed depth rail. -/
theorem nonterminal_dwell_ledger_le_fullMellinVariation_of_subset_railBand
    {s : Finset ℕ} {n r j : ℕ} (hs : s ⊆ railBand n r) (hj : j + 1 < r) :
    |((1 : ℝ) / 2) ^ (r - j) * dynamicBankSignedLedger s n j| ≤
      ((1 : ℝ) / 2) ^ (r - j) *
        (recursiveMellinCurvatureVariation s n j +
          recursiveMellinAdapterVariation s n j) := by
  have hdwell : 0 ≤ ((1 : ℝ) / 2) ^ (r - j) := by positivity
  rw [abs_mul, abs_of_nonneg hdwell]
  exact mul_le_mul_of_nonneg_left
    (abs_dynamicBankSignedLedger_le_fullMellinVariation_of_subset_railBand hs hj) hdwell

/-- The harmonic-diffuse nonterminal ledger lands directly in the full Mellin variation norm. -/
theorem harmonicDiffuse_nonterminal_dwell_ledger_le_fullMellinVariation
    {n r j : ℕ} (hj : j + 1 < r) :
    |((1 : ℝ) / 2) ^ (r - j) *
        dynamicBankSignedLedger (harmonicDiffuseRailBand n r) n j| ≤
      ((1 : ℝ) / 2) ^ (r - j) *
        (recursiveMellinCurvatureVariation (harmonicDiffuseRailBand n r) n j +
          recursiveMellinAdapterVariation (harmonicDiffuseRailBand n r) n j) := by
  exact nonterminal_dwell_ledger_le_fullMellinVariation_of_subset_railBand
    (harmonicDiffuseRailBand_subset_railBand n r) hj

/-- Preterminal stopping removes the coherent terminal packet: every ledger left by the
`r - 1` unrolling is a complete-cell Mellin variation term. -/
theorem harmonicDiffuseDepthBand_mass_le_preterminalFullMellin
    {n r : ℕ} (hr : 0 < r) :
    primeHarmonicMass (harmonicDiffuseDepthBand n r) ≤
      ((1 : ℝ) / 2) ^ (r - 1) *
          dynamicBankEnergy (harmonicDiffuseRailBand n r) n 0 +
        ∑ j ∈ range (r - 1), ((1 : ℝ) / 2) ^ (r - 1 - j) *
          (recursiveMellinCurvatureVariation (harmonicDiffuseRailBand n r) n j +
            recursiveMellinAdapterVariation (harmonicDiffuseRailBand n r) n j) := by
  calc
    primeHarmonicMass (harmonicDiffuseDepthBand n r) ≤
        dynamicBankEnergy (harmonicDiffuseRailBand n r) n (r - 1) :=
      primeHarmonicMass_harmonicDiffuseDepthBand_le_preterminal hr
    _ = ((1 : ℝ) / 2) ^ (r - 1) *
          dynamicBankEnergy (harmonicDiffuseRailBand n r) n 0 +
        ∑ j ∈ range (r - 1), ((1 : ℝ) / 2) ^ (r - 1 - j) *
          dynamicBankSignedLedger (harmonicDiffuseRailBand n r) n j :=
      dynamicBankEnergy_eq_vanishingDwell (harmonicDiffuseRailBand n r) n (r - 1)
    _ ≤ ((1 : ℝ) / 2) ^ (r - 1) *
          dynamicBankEnergy (harmonicDiffuseRailBand n r) n 0 +
        ∑ j ∈ range (r - 1), ((1 : ℝ) / 2) ^ (r - 1 - j) *
          (recursiveMellinCurvatureVariation (harmonicDiffuseRailBand n r) n j +
            recursiveMellinAdapterVariation (harmonicDiffuseRailBand n r) n j) := by
      apply add_le_add_right
      apply sum_le_sum
      intro j hj
      have hjlt : j + 1 < r := by
        have hjpred : j < r - 1 := mem_range.mp hj
        omega
      have hdwell : 0 ≤ ((1 : ℝ) / 2) ^ (r - 1 - j) := by positivity
      have hledger :=
        abs_dynamicBankSignedLedger_le_fullMellinVariation_of_subset_railBand
          (harmonicDiffuseRailBand_subset_railBand n r) hjlt
      calc
        ((1 : ℝ) / 2) ^ (r - 1 - j) *
            dynamicBankSignedLedger (harmonicDiffuseRailBand n r) n j ≤
            |((1 : ℝ) / 2) ^ (r - 1 - j) *
              dynamicBankSignedLedger (harmonicDiffuseRailBand n r) n j| :=
          le_abs_self _
        _ = ((1 : ℝ) / 2) ^ (r - 1 - j) *
            |dynamicBankSignedLedger (harmonicDiffuseRailBand n r) n j| := by
          rw [abs_mul, abs_of_nonneg hdwell]
        _ ≤ ((1 : ℝ) / 2) ^ (r - 1 - j) *
            (recursiveMellinCurvatureVariation (harmonicDiffuseRailBand n r) n j +
              recursiveMellinAdapterVariation (harmonicDiffuseRailBand n r) n j) :=
          mul_le_mul_of_nonneg_left hledger hdwell

/-- Summed preterminal estimate over all occupied logarithmic depths.  The right side contains no
terminal threshold ledger. -/
theorem sum_harmonicDiffuseDepthBand_mass_le_preterminalFullMellin (n : ℕ) :
    ∑ r ∈ occupiedDepths n,
        primeHarmonicMass (harmonicDiffuseDepthBand n r) ≤
      ∑ r ∈ occupiedDepths n,
        (((1 : ℝ) / 2) ^ (r - 1) *
            dynamicBankEnergy (harmonicDiffuseRailBand n r) n 0 +
          ∑ j ∈ range (r - 1), ((1 : ℝ) / 2) ^ (r - 1 - j) *
            (recursiveMellinCurvatureVariation (harmonicDiffuseRailBand n r) n j +
              recursiveMellinAdapterVariation (harmonicDiffuseRailBand n r) n j)) := by
  apply sum_le_sum
  intro r hr
  exact harmonicDiffuseDepthBand_mass_le_preterminalFullMellin
    (occupiedDepth_pos hr)

/-- Raw terminal energy also stops one cell early; the terminal-packet removal is independent of
the harmonic atomic/diffuse split. -/
theorem dynamicBankEnergy_railBand_terminal_le_preterminal
    {n r : ℕ} (hr : 0 < r) :
    dynamicBankEnergy (railBand n r) n r ≤
      dynamicBankEnergy (railBand n r) n (r - 1) := by
  have hpos : ∀ p ∈ railBand n r, 0 < p := by
    intro p hp
    exact (Nat.prime_of_mem_primesLE (mem_filter.mp hp).1).pos
  have hstep := dynamicBankEnergy_succ_le_of_positive_primes
    (s := railBand n r) (n := n) (j := r - 1) hpos
  simpa [Nat.sub_add_cancel hr] using hstep

/-- Every closed depth-band mass is bounded by the corresponding raw preterminal energy. -/
theorem primeHarmonicMass_depthBand_le_preterminal
    {n r : ℕ} (hr : 0 < r) :
    primeHarmonicMass (depthBand n r) ≤
      dynamicBankEnergy (railBand n r) n (r - 1) := by
  rw [← dynamicBankEnergy_railBand_terminal_eq_depthBandMass]
  exact dynamicBankEnergy_railBand_terminal_le_preterminal hr

/-- Direct raw-band preterminal estimate: all remaining ledger terms are nonterminal full-Mellin
curvature and adapter variation. -/
theorem depthBand_mass_le_preterminalFullMellin
    {n r : ℕ} (hr : 0 < r) :
    primeHarmonicMass (depthBand n r) ≤
      ((1 : ℝ) / 2) ^ (r - 1) * dynamicBankEnergy (railBand n r) n 0 +
        ∑ j ∈ range (r - 1), ((1 : ℝ) / 2) ^ (r - 1 - j) *
          (recursiveMellinCurvatureVariation (railBand n r) n j +
            recursiveMellinAdapterVariation (railBand n r) n j) := by
  calc
    primeHarmonicMass (depthBand n r) ≤
        dynamicBankEnergy (railBand n r) n (r - 1) :=
      primeHarmonicMass_depthBand_le_preterminal hr
    _ = ((1 : ℝ) / 2) ^ (r - 1) * dynamicBankEnergy (railBand n r) n 0 +
        ∑ j ∈ range (r - 1), ((1 : ℝ) / 2) ^ (r - 1 - j) *
          dynamicBankSignedLedger (railBand n r) n j :=
      dynamicBankEnergy_eq_vanishingDwell (railBand n r) n (r - 1)
    _ ≤ ((1 : ℝ) / 2) ^ (r - 1) * dynamicBankEnergy (railBand n r) n 0 +
        ∑ j ∈ range (r - 1), ((1 : ℝ) / 2) ^ (r - 1 - j) *
          (recursiveMellinCurvatureVariation (railBand n r) n j +
            recursiveMellinAdapterVariation (railBand n r) n j) := by
      apply add_le_add_right
      apply sum_le_sum
      intro j hj
      have hjlt : j + 1 < r := by
        have hjpred : j < r - 1 := mem_range.mp hj
        omega
      have hdwell : 0 ≤ ((1 : ℝ) / 2) ^ (r - 1 - j) := by positivity
      have hledger :=
        abs_dynamicBankSignedLedger_le_fullMellinVariation_of_subset_railBand
          (s := railBand n r) (Subset.rfl) hjlt
      calc
        ((1 : ℝ) / 2) ^ (r - 1 - j) *
            dynamicBankSignedLedger (railBand n r) n j ≤
            |((1 : ℝ) / 2) ^ (r - 1 - j) *
              dynamicBankSignedLedger (railBand n r) n j| :=
          le_abs_self _
        _ = ((1 : ℝ) / 2) ^ (r - 1 - j) *
            |dynamicBankSignedLedger (railBand n r) n j| := by
          rw [abs_mul, abs_of_nonneg hdwell]
        _ ≤ ((1 : ℝ) / 2) ^ (r - 1 - j) *
            (recursiveMellinCurvatureVariation (railBand n r) n j +
              recursiveMellinAdapterVariation (railBand n r) n j) :=
          mul_le_mul_of_nonneg_left hledger hdwell

/-- Global preterminal full-Mellin reduction of the complete Erdős-377 mass.  No terminal
threshold, signed square-wave, or atomic/diffuse term survives on the right. -/
theorem erdos377Mass_le_sum_preterminalFullMellin (n : ℕ) :
    erdos377Mass n ≤
      ∑ r ∈ occupiedDepths n,
        (((1 : ℝ) / 2) ^ (r - 1) * dynamicBankEnergy (railBand n r) n 0 +
          ∑ j ∈ range (r - 1), ((1 : ℝ) / 2) ^ (r - 1 - j) *
            (recursiveMellinCurvatureVariation (railBand n r) n j +
              recursiveMellinAdapterVariation (railBand n r) n j)) := by
  rw [erdos377Mass_eq_sum_depthBandMass]
  apply sum_le_sum
  intro r hr
  exact depthBand_mass_le_preterminalFullMellin (occupiedDepth_pos hr)

/-- The terminal recursive ledger is exactly the survivor imbalance across the single root
threshold. -/
theorem railBand_recursiveWarpedLedger_terminal_eq_threshold
    {n r j : ℕ} (hj : j + 1 = r) :
    recursiveWarpedLedger (railBand n r) n j =
      ∑ p ∈ dynamicSurvivingPrimeBank (railBand n r) n j,
        (1 : ℝ) / (p : ℝ) * (if 2 * n < p ^ (r + 1) then 1 else -1) := by
  rw [← dynamicBankSignedLedger_eq_recursiveWarpedLedger (railBand_subset_primesLE n r)]
  exact railBand_dynamicBankSignedLedger_terminal_eq_threshold hj

/-- Global recursive warped-contour identity.  The complete-cell terms are now exact Stieltjes
second differences on the evolving survivor bank; every failure of telescoping is isolated in the
explicit `k=0` boundary ledger. -/
theorem erdos377Mass_eq_sum_recursiveWarpedDwell (n : ℕ) :
    erdos377Mass n =
      ∑ r ∈ occupiedDepths n,
        (((1 : ℝ) / 2) ^ r * dynamicBankEnergy (railBand n r) n 0 +
          ∑ j ∈ range r, ((1 : ℝ) / 2) ^ (r - j) *
            recursiveWarpedLedger (railBand n r) n j) := by
  rw [erdos377Mass_eq_sum_vanishingDwell]
  apply sum_congr rfl
  intro r _
  congr 1
  apply sum_congr rfl
  intro j _
  rw [dynamicBankSignedLedger_eq_recursiveWarpedLedger (railBand_subset_primesLE n r)]

/-- Global identity with every complete cell on the dimensionless Mellin carrier. -/
theorem erdos377Mass_eq_sum_fullyMellinDwell (n : ℕ) :
    erdos377Mass n =
      ∑ r ∈ occupiedDepths n,
        (((1 : ℝ) / 2) ^ r * dynamicBankEnergy (railBand n r) n 0 +
          ∑ j ∈ range r, ((1 : ℝ) / 2) ^ (r - j) *
            fullyMellinReconstructedLedger (railBand n r) n j) := by
  rw [erdos377Mass_eq_sum_recursiveWarpedDwell]
  apply sum_congr rfl
  intro r _
  congr 1
  apply sum_congr rfl
  intro j _
  rw [fullyMellinReconstructedLedger_eq_recursiveWarpedLedger]

/-- Fully Mellin-scaled global identity after separating harmonically concentrated atoms from
the diffuse prime banks. -/
theorem erdos377Mass_eq_sum_harmonicAtomicDiffuseFullyMellinDwell (n : ℕ) :
    erdos377Mass n =
      ∑ r ∈ occupiedDepths n,
        ((((1 : ℝ) / 2) ^ r * dynamicBankEnergy (harmonicAtomicRailBand n r) n 0 +
            ∑ j ∈ range r, ((1 : ℝ) / 2) ^ (r - j) *
              fullyMellinReconstructedLedger (harmonicAtomicRailBand n r) n j) +
          (((1 : ℝ) / 2) ^ r * dynamicBankEnergy (harmonicDiffuseRailBand n r) n 0 +
            ∑ j ∈ range r, ((1 : ℝ) / 2) ^ (r - j) *
              fullyMellinReconstructedLedger (harmonicDiffuseRailBand n r) n j)) := by
  rw [erdos377Mass_eq_sum_harmonicAtomicDiffuseDwell]
  apply sum_congr rfl
  intro r _
  have hatomicPrimes : harmonicAtomicRailBand n r ⊆ n.primesLE :=
    (harmonicAtomicRailBand_subset_railBand n r).trans (railBand_subset_primesLE n r)
  have hdiffusePrimes : harmonicDiffuseRailBand n r ⊆ n.primesLE :=
    (harmonicDiffuseRailBand_subset_railBand n r).trans (railBand_subset_primesLE n r)
  congr 1
  · congr 1
    apply sum_congr rfl
    intro j _
    rw [dynamicBankSignedLedger_eq_recursiveWarpedLedger hatomicPrimes,
      fullyMellinReconstructedLedger_eq_recursiveWarpedLedger]
  · congr 1
    apply sum_congr rfl
    intro j _
    rw [dynamicBankSignedLedger_eq_recursiveWarpedLedger hdiffusePrimes,
      fullyMellinReconstructedLedger_eq_recursiveWarpedLedger]

/-- The coherent terminal survivor ledger remains exactly one reciprocal atom after every
coordinate and carrier has been Mellin normalized. -/
theorem three_pow_terminal_dynamicBankSignedLedger_eq_one_third
    {r : ℕ} (hr : 2 ≤ r) :
    dynamicBankSignedLedger (railBand (3 ^ r) r) (3 ^ r) (r - 1) = (1 : ℝ) / 3 := by
  rw [railBand_three_pow hr, dynamicBankSignedLedger]
  simp only [sum_singleton]
  have hsub : r - 1 + 1 = r := by omega
  have hclosure : dynamicClosureWeight 3 (3 ^ r) (r - 1) = 1 := by
    rw [dynamicClosureWeight, hsub]
    exact three_pow_dynamicSurvivalWeight_eq_one (le_rfl)
  have hrail : 3 ∈ railBand (3 ^ r) r := by
    rw [railBand_three_pow hr]
    simp
  have hsign : dynamicSquareSign 3 (3 ^ r) (r - 1) = 1 := by
    rw [railBand_dynamicSquareSign_terminal_mellin hrail hsub,
      if_pos (terminalMellinDrift_three_pow_pos r)]
  rw [hclosure, hsign]
  norm_num

/-- No uniform geometric decay can be assigned to the fully harmonized terminal ledger: the
coherent power rail remains a fixed reciprocal atom at every depth. -/
theorem not_exists_uniformTerminalMellinDecay :
    ¬ ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℕ, 2 ≤ r →
      |dynamicBankSignedLedger (railBand (3 ^ r) r) (3 ^ r) (r - 1)| ≤
        C * ((1 : ℝ) / 2) ^ r := by
  rintro ⟨C, hC, hdecay⟩
  by_cases hCzero : C = 0
  · have h := hdecay 2 (by omega)
    rw [three_pow_terminal_dynamicBankSignedLedger_eq_one_third (by omega),
      abs_of_pos (by norm_num), hCzero] at h
    norm_num at h
  · have hCpos : 0 < C := lt_of_le_of_ne hC (Ne.symm hCzero)
    have hthreshold : 0 < (1 : ℝ) / (3 * (C + 1)) := by positivity
    obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one hthreshold (by norm_num : (1 : ℝ) / 2 < 1)
    let K := k + 2
    have hK : 2 ≤ K := by simp [K]
    have hpow : ((1 : ℝ) / 2) ^ K ≤ ((1 : ℝ) / 2) ^ k := by
      rw [show K = k + 2 by rfl, pow_add]
      norm_num
    have hCdecay : C * ((1 : ℝ) / 2) ^ K < (1 : ℝ) / 3 := calc
      C * ((1 : ℝ) / 2) ^ K ≤ C * ((1 : ℝ) / 2) ^ k :=
        mul_le_mul_of_nonneg_left hpow hC
      _ < C * ((1 : ℝ) / (3 * (C + 1))) := mul_lt_mul_of_pos_left hk hCpos
      _ < (1 : ℝ) / 3 := by
        rw [div_eq_mul_inv]
        field_simp
        linarith
    have h := hdecay K hK
    rw [three_pow_terminal_dynamicBankSignedLedger_eq_one_third hK,
      abs_of_pos (by norm_num)] at h
    linarith

/-! ## Uniform entrance via Abel--Chebyshev scaling -/

/-- Reciprocal-prime mass on one natural interval. -/
noncomputable def primeReciprocalIoc (a b : ℕ) : ℝ :=
  ∑ p ∈ Ioc a b with p.Prime, (1 : ℝ) / (p : ℝ)

/-- Exact Abel conversion of reciprocal-prime mass to the prime-counting staircase. -/
theorem primeReciprocalIoc_eq_abel {a b : ℕ} (ha : 0 < a) (hab : a ≤ b) :
    primeReciprocalIoc a b =
      (1 : ℝ) / b * Nat.primeCounting b -
        (1 : ℝ) / a * Nat.primeCounting a +
          ∫ t in Set.Ioc (a : ℝ) b, (Nat.primeCounting ⌊t⌋₊ : ℝ) / t ^ 2 := by
  let c : ℕ → ℝ := fun k ↦ if k.Prime then 1 else 0
  have hcount (m : ℕ) :
      ∑ k ∈ Icc 0 m, c k = (Nat.primeCounting m : ℝ) := by
    rw [← Nat.primesLE_card_eq_primeCounting, Nat.primesLE_eq_filter_Icc_zero]
    simp [c]
  have habel := sum_mul_eq_sub_sub_integral_mul'
    (c := c) (f := fun x : ℝ ↦ (1 : ℝ) / x) hab (by
      intro t ht
      have ht0 : t ≠ 0 := by
        have hat : (0 : ℝ) < a := by exact_mod_cast ha
        exact ne_of_gt (hat.trans_le ht.1)
      simpa [one_div] using (hasDerivAt_inv ht0).differentiableAt) (by
      rw [show (fun x : ℝ ↦ (1 : ℝ) / x) = (fun x : ℝ ↦ x⁻¹) by
        funext x
        simp, deriv_inv']
      refine ContinuousOn.integrableOn_Icc ?_
      intro t ht
      have ht0 : t ≠ 0 := by
        have hat : (0 : ℝ) < a := by exact_mod_cast ha
        exact ne_of_gt (hat.trans_le ht.1)
      have hcont : ContinuousAt (fun x : ℝ ↦ -((x ^ 2)⁻¹)) t :=
        ((continuousAt_id.pow 2).inv₀ (pow_ne_zero 2 ht0)).neg
      exact hcont.continuousWithinAt)
  simp_rw [hcount] at habel
  rw [show (fun x : ℝ ↦ (1 : ℝ) / x) = (fun x : ℝ ↦ x⁻¹) by
    funext x
    simp] at habel
  simp only [deriv_inv'] at habel
  simp_rw [neg_mul] at habel
  rw [MeasureTheory.integral_neg] at habel
  rw [primeReciprocalIoc]
  simpa [c, sum_filter, div_eq_mul_inv,
    mul_comm, mul_left_comm, mul_assoc] using habel

/-- The negative lower endpoint in Abel summation can be discarded. -/
theorem primeReciprocalIoc_le_abel {a b : ℕ} (ha : 0 < a) (hab : a ≤ b) :
    primeReciprocalIoc a b ≤
      (Nat.primeCounting b : ℝ) / b +
        ∫ t in Set.Ioc (a : ℝ) b, (Nat.primeCounting ⌊t⌋₊ : ℝ) / t ^ 2 := by
  rw [primeReciprocalIoc_eq_abel ha hab]
  have hnonneg :
      0 ≤ (1 : ℝ) / a * (Nat.primeCounting a : ℝ) := by positivity
  have hdrop :
      (1 : ℝ) / b * (Nat.primeCounting b : ℝ) -
          (1 : ℝ) / a * (Nat.primeCounting a : ℝ) +
            ∫ t in Set.Ioc (a : ℝ) b,
              (Nat.primeCounting ⌊t⌋₊ : ℝ) / t ^ 2 ≤
        (1 : ℝ) / b * (Nat.primeCounting b : ℝ) +
          ∫ t in Set.Ioc (a : ℝ) b,
            (Nat.primeCounting ⌊t⌋₊ : ℝ) / t ^ 2 := by
    linarith
  simpa [div_eq_mul_inv, mul_comm] using hdrop

/-- Pointwise Chebyshev majorant for the prime-counting staircase. -/
theorem primeCounting_floor_le_chebyshev {t : ℝ} (ht : 1 < t) :
    (Nat.primeCounting ⌊t⌋₊ : ℝ) ≤
      Real.log 4 * t / Real.log √t + √t := by
  exact Chebyshev.pi_le_log4_mul_div ht

/-- Chebyshev after the Abel/Mellin density has been applied. -/
theorem primeCounting_floor_div_sq_le_chebyshev {t : ℝ} (ht : 1 < t) :
    (Nat.primeCounting ⌊t⌋₊ : ℝ) / t ^ 2 ≤
      (Real.log 4 * t / Real.log √t + √t) / t ^ 2 := by
  exact div_le_div_of_nonneg_right (primeCounting_floor_le_chebyshev ht) (sq_nonneg t)

/-- The explicit Chebyshev estimate on the common harmonic/Mellin scale. -/
theorem primeCounting_floor_le_mellinKernel {t : ℝ} (ht : 1 < t) :
    (Nat.primeCounting ⌊t⌋₊ : ℝ) ≤
      (2 * Real.log 4 + 2) * t / Real.log t := by
  have ht0 : 0 < t := zero_lt_one.trans ht
  have hlogpos : 0 < Real.log t := Real.log_pos ht
  have hlogle : Real.log t ≤ 2 * √t := by
    have h := Real.log_le_rpow_div ht0.le (show (0 : ℝ) < 1 / 2 by norm_num)
    simpa [Real.sqrt_eq_rpow, mul_comm] using h
  have hsqrtlog : √t * Real.log t ≤ 2 * t := by
    nlinarith [Real.sq_sqrt ht0.le, Real.sqrt_nonneg t]
  have htail : √t ≤ 2 * t / Real.log t := by
    exact (le_div_iff₀ hlogpos).2 (by simpa [mul_comm] using hsqrtlog)
  have hmain :
      Real.log 4 * t / Real.log √t = 2 * Real.log 4 * t / Real.log t := by
    rw [Real.log_sqrt ht0.le]
    field_simp
  calc
    (Nat.primeCounting ⌊t⌋₊ : ℝ) ≤
        Real.log 4 * t / Real.log √t + √t := primeCounting_floor_le_chebyshev ht
    _ = 2 * Real.log 4 * t / Real.log t + √t := by rw [hmain]
    _ ≤ 2 * Real.log 4 * t / Real.log t + 2 * t / Real.log t :=
      add_le_add (le_refl _) htail
    _ = (2 * Real.log 4 + 2) * t / Real.log t := by ring

/-- After Abel differentiation, the Chebyshev bound is exactly the `dt/(t log t)` kernel. -/
theorem primeCounting_floor_div_sq_le_mellinKernel {t : ℝ} (ht : 1 < t) :
    (Nat.primeCounting ⌊t⌋₊ : ℝ) / t ^ 2 ≤
      (2 * Real.log 4 + 2) * (t⁻¹ / Real.log t) := by
  have ht0 : t ≠ 0 := (zero_lt_one.trans ht).ne'
  calc
    (Nat.primeCounting ⌊t⌋₊ : ℝ) / t ^ 2 ≤
        ((2 * Real.log 4 + 2) * t / Real.log t) / t ^ 2 := by
      exact div_le_div_of_nonneg_right (primeCounting_floor_le_mellinKernel ht) (sq_nonneg t)
    _ = (2 * Real.log 4 + 2) * (t⁻¹ / Real.log t) := by field_simp

/-- The prime-counting staircase is bounded by its ambient natural interval. -/
theorem primeCounting_le_self (m : ℕ) : Nat.primeCounting m ≤ m := by
  rw [← Nat.primesLE_card_eq_primeCounting, Nat.primesLE_eq_filter_Ioc_zero]
  simpa using Finset.card_filter_le (s := Ioc 0 m) Nat.Prime

/-- After division by the Mellin density `t²`, the elementary counting bound is `1/t`. -/
theorem primeCounting_floor_div_sq_le_inv {t : ℝ} (ht : 0 < t) :
    (Nat.primeCounting ⌊t⌋₊ : ℝ) / t ^ 2 ≤ 1 / t := by
  have hcount : (Nat.primeCounting ⌊t⌋₊ : ℝ) ≤ t := by
    calc
      (Nat.primeCounting ⌊t⌋₊ : ℝ) ≤ (⌊t⌋₊ : ℝ) := by
        exact_mod_cast primeCounting_le_self ⌊t⌋₊
      _ ≤ t := Nat.floor_le ht.le
  calc
    (Nat.primeCounting ⌊t⌋₊ : ℝ) / t ^ 2 ≤ t / t ^ 2 := by gcongr
    _ = 1 / t := by field_simp

/-- Exact Abel conversion after scaling both the reciprocal weight and its logarithmic clock. -/
theorem primeMellinIoc_eq_abel {a b : ℕ} (ha : 2 ≤ a) (hab : a ≤ b) :
    primeMellinIoc a b =
      (Nat.primeCounting b : ℝ) / ((b : ℝ) * Real.log b) -
        (Nat.primeCounting a : ℝ) / ((a : ℝ) * Real.log a) +
          ∫ t in Set.Ioc (a : ℝ) b,
            (Nat.primeCounting ⌊t⌋₊ : ℝ) *
              (Real.log t + 1) / (t ^ 2 * Real.log t ^ 2) := by
  let c : ℕ → ℝ := fun k ↦ if k.Prime then 1 else 0
  let f : ℝ → ℝ := fun t ↦ t⁻¹ / Real.log t
  have hcount (m : ℕ) :
      ∑ k ∈ Icc 0 m, c k = (Nat.primeCounting m : ℝ) := by
    rw [← Nat.primesLE_card_eq_primeCounting, Nat.primesLE_eq_filter_Icc_zero]
    simp [c]
  have hdiff : ∀ t ∈ Set.Icc (a : ℝ) b, DifferentiableAt ℝ f t := by
    intro t ht
    have ht1 : 1 < t := lt_of_lt_of_le (by exact_mod_cast (show 1 < a by omega)) ht.1
    have ht0 : t ≠ 0 := (zero_lt_one.trans ht1).ne'
    have htlog : Real.log t ≠ 0 := (Real.log_pos ht1).ne'
    exact (differentiableAt_inv ht0).div
      (Real.differentiableAt_log ht0) htlog
  have hderiv (t : ℝ) (ht : 1 < t) :
      deriv f t = -(Real.log t + 1) / (t ^ 2 * Real.log t ^ 2) := by
    change deriv (fun u : ℝ ↦ u⁻¹ / Real.log u) t = _
    exact deriv_mellinReciprocal ht
  have hint : MeasureTheory.IntegrableOn (deriv f) (Set.Icc (a : ℝ) b) := by
    refine ContinuousOn.integrableOn_Icc ?_
    intro t ht
    have ht1 : 1 < t := lt_of_lt_of_le (by exact_mod_cast (show 1 < a by omega)) ht.1
    have ht0 : t ≠ 0 := (zero_lt_one.trans ht1).ne'
    have htlog : Real.log t ≠ 0 := (Real.log_pos ht1).ne'
    have hg : ContinuousWithinAt
        (fun y : ℝ ↦ -(Real.log y + 1) / (y ^ 2 * Real.log y ^ 2))
        (Set.Icc (a : ℝ) b) t := by
      exact (((Real.continuousAt_log ht0).add continuousAt_const).neg.div₀
        ((continuousAt_id.pow 2).mul ((Real.continuousAt_log ht0).pow 2))
        (mul_ne_zero (pow_ne_zero 2 ht0) (pow_ne_zero 2 htlog))).continuousWithinAt
    exact hg.congr (fun y hy ↦ by
      have hy1 : 1 < y := lt_of_lt_of_le
        (by exact_mod_cast (show 1 < a by omega)) hy.1
      exact hderiv y hy1) (hderiv t ht1)
  have habel := sum_mul_eq_sub_sub_integral_mul' c hab hdiff hint
  simp_rw [hcount] at habel
  have hint_eq :
      (∫ t in Set.Ioc (a : ℝ) b,
        deriv f t * (Nat.primeCounting ⌊t⌋₊ : ℝ)) =
      -∫ t in Set.Ioc (a : ℝ) b,
        (Nat.primeCounting ⌊t⌋₊ : ℝ) *
          (Real.log t + 1) / (t ^ 2 * Real.log t ^ 2) := by
    rw [← MeasureTheory.integral_neg]
    apply MeasureTheory.integral_congr_ae
    exact (MeasureTheory.ae_restrict_iff' measurableSet_Ioc).2 <|
      Filter.Eventually.of_forall fun t ht ↦ by
        have haR : (1 : ℝ) < a := by exact_mod_cast (show 1 < a by omega)
        change deriv f t * (Nat.primeCounting ⌊t⌋₊ : ℝ) = _
        rw [hderiv t (haR.trans ht.1)]
        ring
  rw [hint_eq] at habel
  rw [primeMellinIoc]
  simp only [f] at habel
  simpa [c, sum_filter, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using habel

/-- Abel--Chebyshev summability of the fully scaled prime carrier above the prime `2`. -/
theorem primeMellinIoc_two_le_uniform {b : ℕ} (hb : 2 ≤ b) :
    primeMellinIoc 2 b ≤
      (1 + 3 * (2 * Real.log 4 + 2)) / Real.log 2 := by
  have htwoR : (1 : ℝ) < 2 := by norm_num
  have hbR : (1 : ℝ) < b := by exact_mod_cast (show 1 < b by omega)
  have hbpos : (0 : ℝ) < b := zero_lt_one.trans hbR
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogb : 0 < Real.log b := Real.log_pos hbR
  have hA : 0 ≤ 2 * Real.log 4 + 2 := by positivity
  have hendpoint :
      (Nat.primeCounting b : ℝ) / ((b : ℝ) * Real.log b) ≤
        1 / Real.log 2 := by
    calc
      (Nat.primeCounting b : ℝ) / ((b : ℝ) * Real.log b) ≤
          (b : ℝ) / ((b : ℝ) * Real.log b) := by
            apply div_le_div_of_nonneg_right _ (mul_nonneg hbpos.le hlogb.le)
            exact_mod_cast primeCounting_le_self b
      _ = 1 / Real.log b := by field_simp
      _ ≤ 1 / Real.log 2 := by
        exact one_div_le_one_div_of_le hlog2
          (Real.log_le_log (by norm_num) (by exact_mod_cast hb))
  have hlowerNonneg :
      0 ≤ (Nat.primeCounting 2 : ℝ) / ((2 : ℝ) * Real.log 2) := by positivity
  have hfactor {t : ℝ} (ht : (2 : ℝ) ≤ t) : Real.log t + 1 ≤ 3 * Real.log t := by
    have hlogmono : Real.log 2 ≤ Real.log t := Real.log_le_log (by norm_num) ht
    have hlog2half : (1 : ℝ) / 2 < Real.log 2 := by
      exact (by norm_num : (1 : ℝ) / 2 < 0.6931471803).trans Real.log_two_gt_d9
    linarith
  have hkernelIntegrable :
      MeasureTheory.IntegrableOn
        (fun t : ℝ ↦ 3 * (2 * Real.log 4 + 2) * (t⁻¹ / Real.log t ^ 2))
        (Set.Ioc (2 : ℝ) b) := by
    exact ((integrableOn_inv_div_log_sq_Ioi htwoR).mono_set
      (by intro t ht; exact ht.1)).const_mul _
  have hintegral :
      (∫ t in Set.Ioc (2 : ℝ) b,
        (Nat.primeCounting ⌊t⌋₊ : ℝ) * (Real.log t + 1) /
          (t ^ 2 * Real.log t ^ 2)) ≤
      ∫ t in Set.Ioc (2 : ℝ) b,
        3 * (2 * Real.log 4 + 2) * (t⁻¹ / Real.log t ^ 2) := by
    refine MeasureTheory.setIntegral_mono_of_nonneg ?_ ?_ hkernelIntegrable
    · intro t ht
      have ht1 : (1 : ℝ) < t := by linarith [ht.1]
      exact div_nonneg
        (mul_nonneg (by positivity) (by linarith [Real.log_pos ht1]))
        (mul_nonneg (sq_nonneg t) (sq_nonneg (Real.log t)))
    · intro t ht
      have ht2 : (2 : ℝ) ≤ t := ht.1.le
      have ht1 : (1 : ℝ) < t := by linarith
      have ht0 : t ≠ 0 := (zero_lt_one.trans ht1).ne'
      have hlog0 : Real.log t ≠ 0 := (Real.log_pos ht1).ne'
      have hcount := primeCounting_floor_le_mellinKernel ht1
      calc
        (Nat.primeCounting ⌊t⌋₊ : ℝ) * (Real.log t + 1) /
            (t ^ 2 * Real.log t ^ 2) ≤
          ((2 * Real.log 4 + 2) * t / Real.log t) * (3 * Real.log t) /
            (t ^ 2 * Real.log t ^ 2) := by
              apply div_le_div_of_nonneg_right
              · calc
                  (Nat.primeCounting ⌊t⌋₊ : ℝ) * (Real.log t + 1) ≤
                      ((2 * Real.log 4 + 2) * t / Real.log t) *
                        (Real.log t + 1) :=
                    mul_le_mul_of_nonneg_right hcount (by linarith [Real.log_pos ht1])
                  _ ≤ ((2 * Real.log 4 + 2) * t / Real.log t) *
                      (3 * Real.log t) :=
                    mul_le_mul_of_nonneg_left (hfactor ht2)
                      (div_nonneg (mul_nonneg hA (zero_lt_one.trans ht1).le)
                        (Real.log_pos ht1).le)
              · exact mul_nonneg (sq_nonneg t) (sq_nonneg (Real.log t))
        _ = 3 * (2 * Real.log 4 + 2) * (t⁻¹ / Real.log t ^ 2) := by
          field_simp
  have hkernelIntegral :
      (∫ t in Set.Ioc (2 : ℝ) b,
        3 * (2 * Real.log 4 + 2) * (t⁻¹ / Real.log t ^ 2)) ≤
      3 * (2 * Real.log 4 + 2) / Real.log 2 := by
    rw [← intervalIntegral.integral_of_le (by exact_mod_cast hb),
      intervalIntegral.integral_const_mul, integral_inv_div_log_sq htwoR hbR]
    have hinvlogb : 0 ≤ (Real.log b)⁻¹ := inv_nonneg.mpr hlogb.le
    calc
      3 * (2 * Real.log 4 + 2) * ((Real.log 2)⁻¹ - (Real.log b)⁻¹) ≤
          3 * (2 * Real.log 4 + 2) * (Real.log 2)⁻¹ := by
            nlinarith [hA]
      _ = 3 * (2 * Real.log 4 + 2) / Real.log 2 := by
        rw [div_eq_mul_inv]
  rw [primeMellinIoc_eq_abel (by norm_num) hb]
  calc
    (Nat.primeCounting b : ℝ) / ((b : ℝ) * Real.log b) -
          (Nat.primeCounting 2 : ℝ) / ((2 : ℝ) * Real.log 2) +
        ∫ t in Set.Ioc (2 : ℝ) b,
          (Nat.primeCounting ⌊t⌋₊ : ℝ) * (Real.log t + 1) /
            (t ^ 2 * Real.log t ^ 2) ≤
      1 / Real.log 2 + 3 * (2 * Real.log 4 + 2) / Real.log 2 := by
        linarith [hintegral.trans hkernelIntegral]
    _ = (1 + 3 * (2 * Real.log 4 + 2)) / Real.log 2 := by ring

/-- Split off the first prime before applying the Abel bound. -/
theorem primeMellinMass_primesLE_eq_two_add_Ioc {n : ℕ} (hn : 2 ≤ n) :
    primeMellinMass n.primesLE =
      (1 : ℝ) / (2 * Real.log 2) + primeMellinIoc 2 n := by
  have hset : n.primesLE =
      (insert 2 ((Finset.Ioc 2 n).filter Nat.Prime) : Finset ℕ) := by
    ext p
    simp only [Nat.mem_primesLE, Finset.mem_insert, Finset.mem_filter, Finset.mem_Ioc]
    constructor
    · rintro ⟨hpn, hpprime⟩
      by_cases hp2 : p = 2
      · exact Or.inl hp2
      · have hpge : 2 ≤ p := hpprime.two_le
        exact Or.inr ⟨⟨by omega, hpn⟩, hpprime⟩
    · rintro (rfl | ⟨⟨_, hpn⟩, hpprime⟩)
      · exact ⟨hn, Nat.prime_two⟩
      · exact ⟨hpn, hpprime⟩
  have hnot : 2 ∉ (Finset.Ioc 2 n).filter Nat.Prime := by simp
  rw [primeMellinMass, hset, sum_insert hnot, primeMellinIoc]
  congr 1
  · simp [mellinClock]
    ring
  · apply sum_congr rfl
    intro p hp
    have hpprime : p.Prime := (mem_filter.mp hp).2
    simp [mellinClock, Nat.max_eq_left hpprime.two_le]

/-- Uniform summability of the fully harmonized prime carrier `1/(p log p)`. -/
theorem primeMellinMass_primesLE_uniform (n : ℕ) :
    primeMellinMass n.primesLE ≤
      (2 + 3 * (2 * Real.log 4 + 2)) / Real.log 2 := by
  by_cases hn : 2 ≤ n
  · rw [primeMellinMass_primesLE_eq_two_add_Ioc hn]
    have hioc := primeMellinIoc_two_le_uniform hn
    have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    calc
      (1 : ℝ) / (2 * Real.log 2) + primeMellinIoc 2 n ≤
          1 / Real.log 2 +
            (1 + 3 * (2 * Real.log 4 + 2)) / Real.log 2 := by
              apply add_le_add _ hioc
              apply (div_le_div_iff₀ (mul_pos (by norm_num) hlog2) hlog2).2
              nlinarith [hlog2]
      _ = (2 + 3 * (2 * Real.log 4 + 2)) / Real.log 2 := by ring
  · have hempty : n.primesLE = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro p hp
      have hmem := Nat.mem_primesLE.mp hp
      exact hn (hmem.2.two_le.trans hmem.1)
    rw [hempty, primeMellinMass]
    have hpos : 0 ≤ (2 + 3 * (2 * Real.log 4 + 2)) / Real.log 2 := by positivity
    simpa using hpos

/-- Abel plus harmonic scaling: reciprocal-prime mass costs only logarithmic width. -/
theorem primeReciprocalIoc_le_one_add_log_ratio {a b : ℕ}
    (ha : 0 < a) (hab : a ≤ b) :
    primeReciprocalIoc a b ≤ 1 + Real.log ((b : ℝ) / a) := by
  have har : (0 : ℝ) < a := by exact_mod_cast ha
  have hbr : (0 : ℝ) < b := by
    exact har.trans_le (by exact_mod_cast hab)
  have hbne : (b : ℝ) ≠ 0 := ne_of_gt hbr
  have hendpoint : (Nat.primeCounting b : ℝ) / b ≤ 1 := by
    calc
      (Nat.primeCounting b : ℝ) / b ≤ (b : ℝ) / b := by
        gcongr
        exact_mod_cast primeCounting_le_self b
      _ = 1 := by field_simp
  have hintegrable :
      MeasureTheory.IntegrableOn (fun t : ℝ ↦ 1 / t) (Set.Ioc (a : ℝ) b) := by
    refine (ContinuousOn.integrableOn_Icc ?_).mono_set Set.Ioc_subset_Icc_self
    intro t ht
    have ht0 : t ≠ 0 := ne_of_gt (har.trans_le ht.1)
    exact (continuousAt_const.div continuousAt_id ht0).continuousWithinAt
  have hintegral :
      (∫ t in Set.Ioc (a : ℝ) b,
          (Nat.primeCounting ⌊t⌋₊ : ℝ) / t ^ 2) ≤
        ∫ t in Set.Ioc (a : ℝ) b, 1 / t := by
    refine MeasureTheory.setIntegral_mono_of_nonneg ?_ ?_ hintegrable
    · intro t ht
      positivity
    · intro t ht
      exact primeCounting_floor_div_sq_le_inv (har.trans_le ht.1.le)
  calc
    primeReciprocalIoc a b ≤
        (Nat.primeCounting b : ℝ) / b +
          ∫ t in Set.Ioc (a : ℝ) b,
            (Nat.primeCounting ⌊t⌋₊ : ℝ) / t ^ 2 :=
      primeReciprocalIoc_le_abel ha hab
    _ ≤ 1 + ∫ t in Set.Ioc (a : ℝ) b, 1 / t := add_le_add hendpoint hintegral
    _ = 1 + Real.log ((b : ℝ) / a) := by
      rw [← intervalIntegral.integral_of_le (by exact_mod_cast hab),
        integral_one_div_of_pos har hbr]

/-- Reciprocal-prime mass on a Mellin interval is bounded by its log--log width. -/
theorem primeReciprocalIoc_le_one_add_mellinWidth {a b : ℕ}
    (ha : 2 ≤ a) (hab : a ≤ b) :
    primeReciprocalIoc a b ≤
      1 + (2 * Real.log 4 + 2) *
        (Real.log (Real.log b) - Real.log (Real.log a)) := by
  have hapos : 0 < a := by omega
  have har : (1 : ℝ) < a := by exact_mod_cast ha
  have hbr : (1 : ℝ) < b := har.trans_le (by exact_mod_cast hab)
  have hendpoint : (Nat.primeCounting b : ℝ) / b ≤ 1 := by
    calc
      (Nat.primeCounting b : ℝ) / b ≤ (b : ℝ) / b := by
        gcongr
        exact_mod_cast primeCounting_le_self b
      _ = 1 := by field_simp
  have hkernelIntegrable :
      MeasureTheory.IntegrableOn
        (fun t : ℝ ↦ (2 * Real.log 4 + 2) * (t⁻¹ / Real.log t))
        (Set.Ioc (a : ℝ) b) := by
    refine (ContinuousOn.integrableOn_Icc ?_).mono_set Set.Ioc_subset_Icc_self
    intro t ht
    have ht1 : (1 : ℝ) < t := har.trans_le ht.1
    have ht0 : t ≠ 0 := (zero_lt_one.trans ht1).ne'
    have hlog0 : Real.log t ≠ 0 := (Real.log_pos ht1).ne'
    have hinv : ContinuousAt (fun x : ℝ ↦ x⁻¹) t := continuousAt_id.inv₀ ht0
    have hlog : ContinuousAt (fun x : ℝ ↦ Real.log x) t := Real.continuousAt_log ht0
    exact (continuousAt_const.mul (hinv.div₀ hlog hlog0)).continuousWithinAt
  have hintegral :
      (∫ t in Set.Ioc (a : ℝ) b,
          (Nat.primeCounting ⌊t⌋₊ : ℝ) / t ^ 2) ≤
        ∫ t in Set.Ioc (a : ℝ) b,
          (2 * Real.log 4 + 2) * (t⁻¹ / Real.log t) := by
    refine MeasureTheory.setIntegral_mono_of_nonneg ?_ ?_ hkernelIntegrable
    · intro t ht
      positivity
    · intro t ht
      exact primeCounting_floor_div_sq_le_mellinKernel (har.trans ht.1)
  calc
    primeReciprocalIoc a b ≤
        (Nat.primeCounting b : ℝ) / b +
          ∫ t in Set.Ioc (a : ℝ) b,
            (Nat.primeCounting ⌊t⌋₊ : ℝ) / t ^ 2 :=
      primeReciprocalIoc_le_abel hapos hab
    _ ≤ 1 + ∫ t in Set.Ioc (a : ℝ) b,
        (2 * Real.log 4 + 2) * (t⁻¹ / Real.log t) := add_le_add hendpoint hintegral
    _ = 1 + (2 * Real.log 4 + 2) *
        (Real.log (Real.log b) - Real.log (Real.log a)) := by
      rw [← intervalIntegral.integral_of_le (by exact_mod_cast hab),
        intervalIntegral.integral_const_mul, integral_inv_div_log har hbr]

/-- Exact power window underlying one logarithmic rail band. -/
theorem railBand_pow_le_and_lt_pow {p n r : ℕ} (hp : p ∈ railBand n r) :
    p ^ r ≤ n ∧ n < p ^ (r + 1) := by
  have hpLE : p ∈ n.primesLE := (mem_filter.mp hp).1
  have hpPrime : p.Prime := Nat.prime_of_mem_primesLE hpLE
  have hnne : n ≠ 0 :=
    (hpPrime.pos.trans_le (Nat.le_of_mem_primesLE hpLE)).ne'
  exact (Nat.log_eq_iff (Or.inr ⟨hpPrime.one_lt, hnne⟩)).mp (mem_filter.mp hp).2

/-- Two primes on the same rail band are trapped between crossed consecutive powers. -/
theorem sameRailBand_crossed_power_window {p q n r : ℕ}
    (hp : p ∈ railBand n r) (hq : q ∈ railBand n r) :
    q ^ r < p ^ (r + 1) := by
  exact (railBand_pow_le_and_lt_pow hq).1.trans_lt
    (railBand_pow_le_and_lt_pow hp).2

/-- The crossed power window becomes a depth-independent logarithmic/Mellin window. -/
theorem sameRailBand_mellin_window {p q n r : ℕ}
    (hp : p ∈ railBand n r) (hq : q ∈ railBand n r) :
    (r : ℝ) * Real.log q < ((r + 1 : ℕ) : ℝ) * Real.log p := by
  have hpPrime : p.Prime := Nat.prime_of_mem_primesLE (mem_filter.mp hp).1
  have hqPrime : q.Prime := Nat.prime_of_mem_primesLE (mem_filter.mp hq).1
  have hpow := sameRailBand_crossed_power_window hp hq
  have hcast : (q : ℝ) ^ r < (p : ℝ) ^ (r + 1) := by
    exact_mod_cast hpow
  have hqpos : (0 : ℝ) < q := by exact_mod_cast hqPrime.pos
  have hppos : (0 : ℝ) < p := by exact_mod_cast hpPrime.pos
  have hlog := Real.strictMonoOn_log (pow_pos hqpos r) (pow_pos hppos (r + 1)) hcast
  simpa only [Real.log_pow] using hlog

/-- Every positive-depth rail band has logarithmic endpoint ratio below two. -/
theorem sameRailBand_log_lt_two_mul {p q n r : ℕ}
    (hr : 0 < r) (hp : p ∈ railBand n r) (hq : q ∈ railBand n r) :
    Real.log q < 2 * Real.log p := by
  have hpPrime : p.Prime := Nat.prime_of_mem_primesLE (mem_filter.mp hp).1
  have hlogp : 0 < Real.log p := Real.log_pos (by exact_mod_cast hpPrime.one_lt)
  have hrreal : (0 : ℝ) < r := by exact_mod_cast hr
  have hcoeffNat : r + 1 ≤ 2 * r := by omega
  have hcoeff : (((r + 1 : ℕ) : ℝ)) ≤ 2 * (r : ℝ) := by
    exact_mod_cast hcoeffNat
  have hupper : (((r + 1 : ℕ) : ℝ)) * Real.log p ≤
      (2 * (r : ℝ)) * Real.log p :=
    mul_le_mul_of_nonneg_right hcoeff hlogp.le
  have hwindow := (sameRailBand_mellin_window hp hq).trans_le hupper
  nlinarith

/-- The log--log width of every positive-depth rail band is strictly below `log 2`. -/
theorem sameRailBand_mellinWidth_lt_log_two {p q n r : ℕ}
    (hr : 0 < r) (hp : p ∈ railBand n r) (hq : q ∈ railBand n r) :
    Real.log (Real.log q) - Real.log (Real.log p) < Real.log 2 := by
  have hpPrime : p.Prime := Nat.prime_of_mem_primesLE (mem_filter.mp hp).1
  have hqPrime : q.Prime := Nat.prime_of_mem_primesLE (mem_filter.mp hq).1
  have hlogp : 0 < Real.log p := Real.log_pos (by exact_mod_cast hpPrime.one_lt)
  have hlogq : 0 < Real.log q := Real.log_pos (by exact_mod_cast hqPrime.one_lt)
  have hratio : Real.log q / Real.log p < 2 :=
    (div_lt_iff₀ hlogp).2 (sameRailBand_log_lt_two_mul hr hp hq)
  have hlog := Real.strictMonoOn_log (div_pos hlogq hlogp) (by norm_num) hratio
  rwa [Real.log_div hlogq.ne' hlogp.ne'] at hlog

/-- A nonempty raw rail bank is controlled by the full prime interval from its minimum to maximum. -/
theorem primeHarmonicMass_railBand_le_min_add_Ioc {n r : ℕ}
    (hs : (railBand n r).Nonempty) :
    primeHarmonicMass (railBand n r) ≤
      (1 : ℝ) / ((railBand n r).min' hs : ℝ) +
        primeReciprocalIoc ((railBand n r).min' hs) ((railBand n r).max' hs) := by
  let s := railBand n r
  let a := s.min' hs
  let b := s.max' hs
  have haMem : a ∈ s := s.min'_mem hs
  have hsplit := Finset.sum_erase_add s (fun p : ℕ ↦ (1 : ℝ) / (p : ℝ)) haMem
  have hsub : s.erase a ⊆ (Ioc a b).filter Nat.Prime := by
    intro p hp
    have hpS : p ∈ s := Finset.mem_of_mem_erase hp
    have hpa : a < p := s.min'_lt_of_mem_erase_min' hs hp
    have hpb : p ≤ b := s.le_max' p hpS
    have hpPrime : p.Prime := Nat.prime_of_mem_primesLE (mem_filter.mp hpS).1
    exact mem_filter.mpr ⟨mem_Ioc.mpr ⟨hpa, hpb⟩, hpPrime⟩
  have hsum :
      ∑ p ∈ s.erase a, (1 : ℝ) / (p : ℝ) ≤
        ∑ p ∈ (Ioc a b).filter Nat.Prime, (1 : ℝ) / (p : ℝ) := by
    exact Finset.sum_le_sum_of_subset_of_nonneg hsub (by
      intro p hp hnot
      positivity)
  rw [primeHarmonicMass]
  change (∑ p ∈ s, (1 : ℝ) / (p : ℝ)) ≤ _
  change _ ≤ (1 : ℝ) / (a : ℝ) + primeReciprocalIoc a b
  rw [← hsplit]
  unfold primeReciprocalIoc
  simpa [sum_filter, add_comm] using add_le_add_left hsum ((1 : ℝ) / (a : ℝ))

/-- Uniform reciprocal-prime budget for every positive-depth logarithmic rail band. -/
theorem primeHarmonicMass_railBand_le_uniform {n r : ℕ} (hr : 0 < r) :
    primeHarmonicMass (railBand n r) ≤
      2 + (2 * Real.log 4 + 2) * Real.log 2 := by
  by_cases hs : (railBand n r).Nonempty
  · let a := (railBand n r).min' hs
    let b := (railBand n r).max' hs
    have haMem : a ∈ railBand n r := (railBand n r).min'_mem hs
    have hbMem : b ∈ railBand n r := (railBand n r).max'_mem hs
    have haPrime : a.Prime := Nat.prime_of_mem_primesLE (mem_filter.mp haMem).1
    have ha2 : 2 ≤ a := haPrime.two_le
    have hab : a ≤ b := (railBand n r).min'_le_max' hs
    have hwidth :
        Real.log (Real.log b) - Real.log (Real.log a) ≤ Real.log 2 :=
      (sameRailBand_mellinWidth_lt_log_two hr haMem hbMem).le
    have hK : 0 ≤ 2 * Real.log 4 + 2 := by
      have : 0 < Real.log (4 : ℝ) := Real.log_pos (by norm_num)
      positivity
    have hIoc : primeReciprocalIoc a b ≤
        1 + (2 * Real.log 4 + 2) * Real.log 2 :=
      (primeReciprocalIoc_le_one_add_mellinWidth ha2 hab).trans
        (add_le_add_right (mul_le_mul_of_nonneg_left hwidth hK) 1)
    have hapos : (0 : ℝ) < a := by exact_mod_cast haPrime.pos
    have hmin : (1 : ℝ) / a ≤ 1 := by
      exact (div_le_iff₀ hapos).2 (by simpa using (show (1 : ℝ) ≤ a by exact_mod_cast haPrime.one_le))
    exact (primeHarmonicMass_railBand_le_min_add_Ioc hs).trans (by
      change (1 : ℝ) / a + primeReciprocalIoc a b ≤ _
      linarith)
  · have hempty : railBand n r = ∅ := not_nonempty_iff_eq_empty.mp hs
    rw [hempty, primeHarmonicMass]
    positivity

/-- The complete preterminal entrance ledger has one absolute geometric budget. -/
theorem preterminalEntrance_uniform :
    ∃ C : ℝ, ∀ n : ℕ,
      ∑ r ∈ occupiedDepths n,
        ((1 : ℝ) / 2) ^ (r - 1) *
          dynamicBankEnergy (railBand n r) n 0 ≤ C := by
  let M : ℝ := 2 + (2 * Real.log 4 + 2) * Real.log 2
  refine ⟨4 * M, ?_⟩
  intro n
  have hM : 0 ≤ M := by
    dsimp [M]
    have hlog4 : 0 < Real.log (4 : ℝ) := Real.log_pos (by norm_num)
    have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
    positivity
  have hsummable : Summable (fun r : ℕ ↦ 2 * M * ((1 : ℝ) / 2) ^ r) :=
    summable_geometric_two.mul_left (2 * M)
  have htsum : (∑' r : ℕ, 2 * M * ((1 : ℝ) / 2) ^ r) = 4 * M := by
    have hsum := hasSum_geometric_two.mul_left (2 * M)
    calc
      (∑' r : ℕ, 2 * M * ((1 : ℝ) / 2) ^ r) = (2 * M) * 2 := hsum.tsum_eq
      _ = 4 * M := by ring
  calc
    ∑ r ∈ occupiedDepths n,
        ((1 : ℝ) / 2) ^ (r - 1) *
          dynamicBankEnergy (railBand n r) n 0 ≤
        ∑ r ∈ occupiedDepths n, 2 * M * ((1 : ℝ) / 2) ^ r := by
      apply sum_le_sum
      intro r hr
      have hrpos := occupiedDepth_pos hr
      have hdwell : 0 ≤ ((1 : ℝ) / 2) ^ (r - 1) := by positivity
      have hband : primeHarmonicMass (railBand n r) ≤ M := by
        simpa [M] using primeHarmonicMass_railBand_le_uniform (n := n) hrpos
      have hsub : r - 1 + 1 = r := Nat.sub_add_cancel (by omega)
      have hpowsucc :
          ((1 : ℝ) / 2) ^ r = ((1 : ℝ) / 2) ^ (r - 1) * ((1 : ℝ) / 2) := by
        calc
          ((1 : ℝ) / 2) ^ r = ((1 : ℝ) / 2) ^ (r - 1 + 1) := by rw [hsub]
          _ = ((1 : ℝ) / 2) ^ (r - 1) * ((1 : ℝ) / 2) := by rw [pow_succ]
      have hweight : ((1 : ℝ) / 2) ^ (r - 1) =
          2 * ((1 : ℝ) / 2) ^ r := by
        calc
          ((1 : ℝ) / 2) ^ (r - 1) =
              2 * (((1 : ℝ) / 2) ^ (r - 1) * ((1 : ℝ) / 2)) := by ring
          _ = 2 * ((1 : ℝ) / 2) ^ r := by rw [← hpowsucc]
      calc
        ((1 : ℝ) / 2) ^ (r - 1) *
            dynamicBankEnergy (railBand n r) n 0 ≤
            ((1 : ℝ) / 2) ^ (r - 1) * primeHarmonicMass (railBand n r) :=
          mul_le_mul_of_nonneg_left
            (dynamicBankEnergy_le_primeHarmonicMass (railBand n r) n 0) hdwell
        _ ≤ ((1 : ℝ) / 2) ^ (r - 1) * M :=
          mul_le_mul_of_nonneg_left hband hdwell
        _ = 2 * M * ((1 : ℝ) / 2) ^ r := by rw [hweight]; ring
    _ ≤ ∑' r : ℕ, 2 * M * ((1 : ℝ) / 2) ^ r :=
      hsummable.sum_le_tsum (occupiedDepths n) (fun r _ ↦ by positivity)
    _ = 4 * M := htsum

/-- The remaining fully scaled preterminal norm after the entrance term has been removed. -/
noncomputable def preterminalMellinVariation (n : ℕ) : ℝ :=
  ∑ r ∈ occupiedDepths n,
    ∑ j ∈ range (r - 1), ((1 : ℝ) / 2) ^ (r - 1 - j) *
      (recursiveMellinCurvatureVariation (railBand n r) n j +
        recursiveMellinAdapterVariation (railBand n r) n j)

/-- One depth band's dwell-weighted complete-cell variation. -/
noncomputable def depthPreterminalWarpedVariation (n r : ℕ) : ℝ :=
  ∑ j ∈ range (r - 1), ((1 : ℝ) / 2) ^ (r - 1 - j) *
    recursiveWarpedInteriorVariation (railBand n r) n j

/-- One depth band's stopping-time survivor envelope. -/
noncomputable def depthPreterminalSurvivorEnergy (n r : ℕ) : ℝ :=
  ∑ j ∈ range (r - 1), ((1 : ℝ) / 2) ^ (r - 1 - j) *
    dynamicBankEnergy (railBand n r) n j

/-!
The next two decompositions deliberately change the summation axis.

* The stopping-kernel route first interchanges the cell and prime sums.  Its executable first
  line is `primePreterminalStoppingKernel`; the resulting pointwise kernel is bounded by one.
* The compensated-ledger route first keeps every signed square-wave term, sums those terms over
  all occupied depths, and only then asks for a global estimate.  Its executable first line is
  `preterminalSignedWarpedLedger` below.

These are independent of the depth-wise variation estimate: neither inserts an absolute value
before the cross-depth recombination.
-/

/-- Prime-wise stopping kernel obtained by commuting a depth band's cell and prime sums. -/
noncomputable def primePreterminalStoppingKernel (p n r : ℕ) : ℝ :=
  ∑ j ∈ range (r - 1), ((1 : ℝ) / 2) ^ (r - 1 - j) *
    dynamicClosureWeight p n j

/-- The prime-wise stopping kernel is nonnegative. -/
theorem primePreterminalStoppingKernel_nonneg (p n r : ℕ) :
    0 ≤ primePreterminalStoppingKernel p n r := by
  rw [primePreterminalStoppingKernel]
  apply sum_nonneg
  intro j _
  exact mul_nonneg (by positivity) (dynamicClosureWeight_nonneg p n j)

/-- The geometrically weighted stopping kernel never charges one prime more than once. -/
theorem primePreterminalStoppingKernel_le_one (p n r : ℕ) :
    primePreterminalStoppingKernel p n r ≤ 1 := by
  rw [primePreterminalStoppingKernel]
  calc
    ∑ j ∈ range (r - 1), ((1 : ℝ) / 2) ^ (r - 1 - j) *
        dynamicClosureWeight p n j ≤
        ∑ j ∈ range (r - 1), ((1 : ℝ) / 2) ^ (r - 1 - j) * 1 := by
          apply sum_le_sum
          intro j _
          exact mul_le_mul_of_nonneg_left (dynamicClosureWeight_le_one p n j) (by positivity)
    _ = ∑ j ∈ range (r - 1), ((1 : ℝ) / 2) ^ (r - 1 - j) := by simp
    _ ≤ 1 := sum_range_preterminal_half_pow_le_one r

/-- Exact prime-wise disintegration of one depth band's preterminal survivor energy. -/
theorem depthPreterminalSurvivorEnergy_eq_primeStoppingKernel (n r : ℕ) :
    depthPreterminalSurvivorEnergy n r =
      ∑ p ∈ railBand n r, (1 : ℝ) / (p : ℝ) *
        primePreterminalStoppingKernel p n r := by
  simp only [depthPreterminalSurvivorEnergy, primePreterminalStoppingKernel]
  simp_rw [dynamicBankEnergy]
  calc
    ∑ j ∈ range (r - 1), ((1 : ℝ) / 2) ^ (r - 1 - j) *
        ∑ p ∈ railBand n r,
          (1 : ℝ) / (p : ℝ) * dynamicClosureWeight p n j =
        ∑ j ∈ range (r - 1), ∑ p ∈ railBand n r,
          ((1 : ℝ) / 2) ^ (r - 1 - j) *
            ((1 : ℝ) / (p : ℝ) * dynamicClosureWeight p n j) := by
              apply sum_congr rfl
              intro j _
              rw [Finset.mul_sum]
    _ = ∑ p ∈ railBand n r, ∑ j ∈ range (r - 1),
          ((1 : ℝ) / 2) ^ (r - 1 - j) *
            ((1 : ℝ) / (p : ℝ) * dynamicClosureWeight p n j) := by
              rw [Finset.sum_comm]
    _ = ∑ p ∈ railBand n r, (1 : ℝ) / (p : ℝ) *
          ∑ j ∈ range (r - 1), ((1 : ℝ) / 2) ^ (r - 1 - j) *
            dynamicClosureWeight p n j := by
              apply sum_congr rfl
              intro p _
              rw [Finset.mul_sum]
              apply sum_congr rfl
              intro j _
              ring

/-- The stopping transform removes all repeated cell charging inside one depth band. -/
theorem depthPreterminalSurvivorEnergy_le_primeHarmonicMass (n r : ℕ) :
    depthPreterminalSurvivorEnergy n r ≤ primeHarmonicMass (railBand n r) := by
  rw [depthPreterminalSurvivorEnergy_eq_primeStoppingKernel, primeHarmonicMass]
  apply sum_le_sum
  intro p hp
  have hrecip : 0 ≤ (1 : ℝ) / (p : ℝ) := by positivity
  simpa only [mul_one] using mul_le_mul_of_nonneg_left
    (primePreterminalStoppingKernel_le_one p n r) hrecip

/-- Signed cross-depth warped ledger, retained before any triangle inequality is applied. -/
noncomputable def preterminalSignedWarpedLedger (n : ℕ) : ℝ :=
  ∑ r ∈ occupiedDepths n,
    ∑ j ∈ range (r - 1), ((1 : ℝ) / 2) ^ (r - 1 - j) *
      recursiveWarpedLedger (railBand n r) n j

/-- One depth band is controlled by its entrance energy and its exact signed warped ledger. -/
theorem depthBand_mass_le_entrance_add_signedWarped
    {n r : ℕ} (hr : 0 < r) :
    primeHarmonicMass (depthBand n r) ≤
      ((1 : ℝ) / 2) ^ (r - 1) * dynamicBankEnergy (railBand n r) n 0 +
        ∑ j ∈ range (r - 1), ((1 : ℝ) / 2) ^ (r - 1 - j) *
          recursiveWarpedLedger (railBand n r) n j := by
  calc
    primeHarmonicMass (depthBand n r) ≤
        dynamicBankEnergy (railBand n r) n (r - 1) :=
      primeHarmonicMass_depthBand_le_preterminal hr
    _ = ((1 : ℝ) / 2) ^ (r - 1) * dynamicBankEnergy (railBand n r) n 0 +
        ∑ j ∈ range (r - 1), ((1 : ℝ) / 2) ^ (r - 1 - j) *
          dynamicBankSignedLedger (railBand n r) n j :=
      dynamicBankEnergy_eq_vanishingDwell (railBand n r) n (r - 1)
    _ = ((1 : ℝ) / 2) ^ (r - 1) * dynamicBankEnergy (railBand n r) n 0 +
        ∑ j ∈ range (r - 1), ((1 : ℝ) / 2) ^ (r - 1 - j) *
          recursiveWarpedLedger (railBand n r) n j := by
            congr 1
            apply sum_congr rfl
            intro j _
            rw [dynamicBankSignedLedger_eq_recursiveWarpedLedger
              (railBand_subset_primesLE n r)]

/-- Global exact compensation: cell signs are recombined across depths before taking norms. -/
theorem erdos377Mass_le_preterminalEntrance_add_signedWarpedLedger (n : ℕ) :
    erdos377Mass n ≤
      (∑ r ∈ occupiedDepths n,
        ((1 : ℝ) / 2) ^ (r - 1) * dynamicBankEnergy (railBand n r) n 0) +
        preterminalSignedWarpedLedger n := by
  rw [erdos377Mass_eq_sum_depthBandMass, preterminalSignedWarpedLedger]
  calc
    ∑ r ∈ occupiedDepths n, primeHarmonicMass (depthBand n r) ≤
        ∑ r ∈ occupiedDepths n,
          (((1 : ℝ) / 2) ^ (r - 1) * dynamicBankEnergy (railBand n r) n 0 +
            ∑ j ∈ range (r - 1), ((1 : ℝ) / 2) ^ (r - 1 - j) *
              recursiveWarpedLedger (railBand n r) n j) := by
                apply sum_le_sum
                intro r hr
                exact depthBand_mass_le_entrance_add_signedWarped (occupiedDepth_pos hr)
    _ = (∑ r ∈ occupiedDepths n,
          ((1 : ℝ) / 2) ^ (r - 1) * dynamicBankEnergy (railBand n r) n 0) +
        ∑ r ∈ occupiedDepths n,
          ∑ j ∈ range (r - 1), ((1 : ℝ) / 2) ^ (r - 1 - j) *
            recursiveWarpedLedger (railBand n r) n j := by
              rw [sum_add_distrib]

/-- Uniform entrance discharge with the compensated signed ledger left as the sole target. -/
theorem erdos377Mass_le_uniformEntrance_add_signedWarpedLedger :
    ∃ C : ℝ, ∀ n : ℕ,
      erdos377Mass n ≤ C + preterminalSignedWarpedLedger n := by
  rcases preterminalEntrance_uniform with ⟨C, hC⟩
  refine ⟨C, ?_⟩
  intro n
  exact (erdos377Mass_le_preterminalEntrance_add_signedWarpedLedger n).trans
    (add_le_add_left (hC n) _)

/-- The same compensated ledger with every cell transported onto the Mellin carrier. -/
noncomputable def preterminalSignedFullyMellinLedger (n : ℕ) : ℝ :=
  ∑ r ∈ occupiedDepths n,
    ∑ j ∈ range (r - 1), ((1 : ℝ) / 2) ^ (r - 1 - j) *
      fullyMellinReconstructedLedger (railBand n r) n j

/-- Harmonic conversion is lossless after the signed cross-depth recombination. -/
theorem preterminalSignedFullyMellinLedger_eq_signedWarpedLedger (n : ℕ) :
    preterminalSignedFullyMellinLedger n = preterminalSignedWarpedLedger n := by
  rw [preterminalSignedFullyMellinLedger, preterminalSignedWarpedLedger]
  apply sum_congr rfl
  intro r _
  apply sum_congr rfl
  intro j _
  rw [fullyMellinReconstructedLedger_eq_recursiveWarpedLedger]

/-- Fully harmonized compensated reduction. -/
theorem erdos377Mass_le_uniformEntrance_add_signedFullyMellinLedger :
    ∃ C : ℝ, ∀ n : ℕ,
      erdos377Mass n ≤ C + preterminalSignedFullyMellinLedger n := by
  rcases erdos377Mass_le_uniformEntrance_add_signedWarpedLedger with ⟨C, hC⟩
  refine ⟨C, ?_⟩
  intro n
  rw [preterminalSignedFullyMellinLedger_eq_signedWarpedLedger]
  exact hC n

/-- Ambient primes whose logarithmic depth is occupied by at least one closed rail. -/
noncomputable def occupiedRawPrimeBank (n : ℕ) : Finset ℕ := by
  classical
  exact n.primesLE.filter fun p ↦ railDepth p n ∈ occupiedDepths n

/-- The single global bank surviving every carry gate except the terminal gate. -/
noncomputable def preterminalClosedPrimeBank (n : ℕ) : Finset ℕ := by
  classical
  exact (occupiedRawPrimeBank n).filter fun p ↦
    DynamicClosedOrbit p n (railDepth p n)

/-- Collapsing the depth fibers turns all preterminal energies into one harmonic prime bank. -/
theorem sum_occupiedDepths_preterminalEnergy_eq_primeHarmonicMass (n : ℕ) :
    ∑ r ∈ occupiedDepths n,
      dynamicBankEnergy (railBand n r) n (r - 1) =
        primeHarmonicMass (preterminalClosedPrimeBank n) := by
  classical
  let u := occupiedRawPrimeBank n
  have hmaps : ∀ p ∈ u, railDepth p n ∈ occupiedDepths n := by
    intro p hp
    exact (mem_filter.mp hp).2
  have hfiber (r : ℕ) (hr : r ∈ occupiedDepths n) :
      u.filter (fun p ↦ railDepth p n = r) = railBand n r := by
    ext p
    simp only [u, occupiedRawPrimeBank, railBand, mem_filter]
    constructor
    · rintro ⟨⟨hpn, _⟩, hdepth⟩
      exact ⟨hpn, hdepth⟩
    · rintro ⟨hpn, hdepth⟩
      refine ⟨⟨hpn, ?_⟩, hdepth⟩
      rw [hdepth]
      exact hr
  simp only [dynamicBankEnergy]
  calc
    ∑ r ∈ occupiedDepths n,
        ∑ p ∈ railBand n r,
          (1 : ℝ) / (p : ℝ) * dynamicClosureWeight p n (r - 1) =
        ∑ r ∈ occupiedDepths n,
          ∑ p ∈ u with railDepth p n = r,
            (1 : ℝ) / (p : ℝ) *
              dynamicClosureWeight p n (railDepth p n - 1) := by
                apply sum_congr rfl
                intro r hr
                rw [hfiber r hr]
                apply sum_congr rfl
                intro p hp
                rw [(mem_filter.mp hp).2]
    _ = ∑ p ∈ u, (1 : ℝ) / (p : ℝ) *
          dynamicClosureWeight p n (railDepth p n - 1) := by
            exact Finset.sum_fiberwise_of_maps_to hmaps _
    _ = primeHarmonicMass (preterminalClosedPrimeBank n) := by
      rw [primeHarmonicMass]
      simp only [preterminalClosedPrimeBank, u]
      rw [sum_filter]
      apply sum_congr rfl
      intro p hp
      have hdepthMem : railDepth p n ∈ occupiedDepths n :=
        (mem_filter.mp hp).2
      have hdepthPos : 0 < railDepth p n := occupiedDepth_pos hdepthMem
      have hsub : railDepth p n - 1 + 1 = railDepth p n :=
        Nat.sub_add_cancel hdepthPos
      rw [dynamicClosureWeight_eq_ite]
      simp only [hsub]
      split <;> simp_all

/-- The complete Erdős mass embeds into the one-step-short global survivor bank. -/
theorem erdos377Mass_le_preterminalClosedPrimeBankMass (n : ℕ) :
    erdos377Mass n ≤ primeHarmonicMass (preterminalClosedPrimeBank n) := by
  rw [erdos377Mass_eq_sum_depthBandMass,
    ← sum_occupiedDepths_preterminalEnergy_eq_primeHarmonicMass]
  apply sum_le_sum
  intro r hr
  exact primeHarmonicMass_depthBand_le_preterminal (occupiedDepth_pos hr)

/-- The compensated signed ledger is exactly global preterminal mass minus entrance mass. -/
theorem preterminalSignedWarpedLedger_eq_preterminalMass_sub_entrance (n : ℕ) :
    preterminalSignedWarpedLedger n =
      primeHarmonicMass (preterminalClosedPrimeBank n) -
        ∑ r ∈ occupiedDepths n,
          ((1 : ℝ) / 2) ^ (r - 1) * dynamicBankEnergy (railBand n r) n 0 := by
  have hrecurrence :
      (∑ r ∈ occupiedDepths n,
        dynamicBankEnergy (railBand n r) n (r - 1)) =
        (∑ r ∈ occupiedDepths n,
          ((1 : ℝ) / 2) ^ (r - 1) * dynamicBankEnergy (railBand n r) n 0) +
          preterminalSignedWarpedLedger n := by
    rw [preterminalSignedWarpedLedger, ← sum_add_distrib]
    apply sum_congr rfl
    intro r _
    rw [dynamicBankEnergy_eq_vanishingDwell]
    congr 1
    apply sum_congr rfl
    intro j _
    rw [dynamicBankSignedLedger_eq_recursiveWarpedLedger
      (railBand_subset_primesLE n r)]
  rw [sum_occupiedDepths_preterminalEnergy_eq_primeHarmonicMass] at hrecurrence
  linarith

/-- On a raw depth rail, one additional closed cell is exactly the original carry-free test. -/
theorem railBand_dynamicClosedOrbit_succ_iff_carryFree
    {p n r : ℕ} (hrail : p ∈ railBand n r) :
    DynamicClosedOrbit p n (r + 1) ↔ CarryFree p n := by
  have hpPrime := Nat.prime_of_mem_primesLE (mem_filter.mp hrail).1
  have hlog := railBand_log_two_mul_lt_depth_add_two hrail
  calc
    DynamicClosedOrbit p n (r + 1) ↔ CarryFreeThrough p n (r + 2) :=
      dynamicClosedOrbit_iff_carryFreeThrough hpPrime.pos
    _ ↔ ¬p ∣ (2 * n).choose n :=
      (prime_not_dvd_centralBinom_iff_carryFreeThrough hpPrime hlog).symm
    _ ↔ CarryFree p n := prime_not_dvd_centralBinom_iff_carryFree hpPrime

/-- A preterminal survivor passes the last carry gate exactly above the terminal root threshold. -/
theorem preterminalClosedPrime_carryFree_iff_terminalThreshold
    {p n : ℕ} (hp : p ∈ preterminalClosedPrimeBank n) :
    CarryFree p n ↔ 2 * n < p ^ (railDepth p n + 1) := by
  have hp' := mem_filter.mp hp
  have hpRaw := mem_filter.mp hp'.1
  have hpPrime := Nat.prime_of_mem_primesLE hpRaw.1
  have hrail : p ∈ railBand n (railDepth p n) :=
    mem_filter.mpr ⟨hpRaw.1, rfl⟩
  have hnlt : n < p ^ (railDepth p n + 1) := by
    exact Nat.lt_pow_succ_log_self hpPrime.one_lt n
  have hmod : n % p ^ (railDepth p n + 1) = n := Nat.mod_eq_of_lt hnlt
  have hphase :
      harmonizedCellPhase p n (railDepth p n) < harmonizedCircumference p / 2 ↔
        2 * n < p ^ (railDepth p n + 1) := by
    rw [harmonizedCellPhase_lt_half_iff
      (n := n) (j := railDepth p n) hpPrime.pos, hmod]
  rw [← railBand_dynamicClosedOrbit_succ_iff_carryFree hrail]
  constructor
  · intro horbit
    exact hphase.mp (horbit (railDepth p n) (Nat.lt_succ_self _))
  · intro hthreshold j hj
    by_cases hjlt : j < railDepth p n
    · exact hp'.2 j hjlt
    · have hjeq : j = railDepth p n := by omega
      rw [hjeq]
      exact hphase.mpr hthreshold

/-- Preterminal survivors that fail precisely at the terminal root gate. -/
noncomputable def terminalFailurePrimeBank (n : ℕ) : Finset ℕ := by
  classical
  exact preterminalClosedPrimeBank n \ carryFreePrimes n

/-- Terminal failures occupy the thin power window `n < p^(r+1) ≤ 2n`. -/
theorem mem_terminalFailurePrimeBank_iff {p n : ℕ} :
    p ∈ terminalFailurePrimeBank n ↔
      p ∈ preterminalClosedPrimeBank n ∧
        p ^ (railDepth p n + 1) ≤ 2 * n := by
  classical
  rw [terminalFailurePrimeBank, mem_sdiff]
  constructor
  · rintro ⟨hp, hnotCarryFreePrime⟩
    refine ⟨hp, ?_⟩
    have hpRaw := (mem_filter.mp (mem_filter.mp hp).1).1
    have hnotFree : ¬CarryFree p n := by
      intro hfree
      exact hnotCarryFreePrime (mem_filter.mpr ⟨hpRaw, hfree⟩)
    exact not_lt.mp (fun hthreshold ↦
      hnotFree ((preterminalClosedPrime_carryFree_iff_terminalThreshold hp).mpr hthreshold))
  · rintro ⟨hp, hthreshold⟩
    refine ⟨hp, ?_⟩
    intro hpCarryFree
    have hfree : CarryFree p n := (mem_filter.mp hpCarryFree).2
    have hterminal :=
      (preterminalClosedPrime_carryFree_iff_terminalThreshold hp).mp hfree
    omega

/-- Explicit two-sided terminal root window. -/
theorem terminalFailurePrime_power_window {p n : ℕ}
    (hp : p ∈ terminalFailurePrimeBank n) :
    n < p ^ (railDepth p n + 1) ∧
      p ^ (railDepth p n + 1) ≤ 2 * n := by
  have hpData := mem_terminalFailurePrimeBank_iff.mp hp
  have hpPrime := Nat.prime_of_mem_primesLE
    (mem_filter.mp (mem_filter.mp hpData.1).1).1
  exact ⟨Nat.lt_pow_succ_log_self hpPrime.one_lt n, hpData.2⟩

/-- Every original closed rail survives the one-step-short global bank. -/
theorem carryFreePrimes_subset_preterminalClosedPrimeBank (n : ℕ) :
    carryFreePrimes n ⊆ preterminalClosedPrimeBank n := by
  intro p hp
  have hpData := mem_filter.mp hp
  have hdepthMem : railDepth p n ∈ occupiedDepths n := by
    rw [occupiedDepths]
    exact mem_image.mpr ⟨p, hp, rfl⟩
  have hrail : p ∈ railBand n (railDepth p n) :=
    mem_filter.mpr ⟨hpData.1, rfl⟩
  have horbitSucc : DynamicClosedOrbit p n (railDepth p n + 1) :=
    (railBand_dynamicClosedOrbit_succ_iff_carryFree hrail).mpr hpData.2
  rw [preterminalClosedPrimeBank]
  exact mem_filter.mpr ⟨mem_filter.mpr ⟨hpData.1, hdepthMem⟩,
    fun j hj ↦ horbitSucc j (hj.trans (Nat.lt_succ_self _))⟩

/-- Exact root-packet split of the global preterminal bank. -/
theorem preterminalClosedPrimeBank_eq_carryFree_union_terminalFailure (n : ℕ) :
    preterminalClosedPrimeBank n =
      carryFreePrimes n ∪ terminalFailurePrimeBank n := by
  rw [terminalFailurePrimeBank, union_sdiff_of_subset
    (carryFreePrimes_subset_preterminalClosedPrimeBank n)]

/-- The global preterminal mass is original mass plus the thin terminal-root packet mass. -/
theorem preterminalClosedPrimeBankMass_eq_erdos377Mass_add_terminalFailureMass (n : ℕ) :
    primeHarmonicMass (preterminalClosedPrimeBank n) =
      erdos377Mass n + primeHarmonicMass (terminalFailurePrimeBank n) := by
  have hdisjoint : Disjoint (carryFreePrimes n) (terminalFailurePrimeBank n) := by
    rw [terminalFailurePrimeBank]
    exact disjoint_sdiff
  rw [preterminalClosedPrimeBank_eq_carryFree_union_terminalFailure,
    primeHarmonicMass, sum_union hdisjoint]
  rw [← erdos377Mass_eq_carryFreeRailSum, primeHarmonicMass]

/-- Signed terminal-root packets, before separating survivors from failures. -/
noncomputable def terminalSignedRootLedger (n : ℕ) : ℝ :=
  ∑ r ∈ occupiedDepths n,
    dynamicBankSignedLedger (railBand n r) n (r - 1)

/-- Exact terminal compensator: preterminal mass and the signed root ledger average to the
original mass. -/
theorem erdos377Mass_eq_half_preterminalMass_add_half_terminalSignedRootLedger (n : ℕ) :
    erdos377Mass n =
      (1 : ℝ) / 2 * primeHarmonicMass (preterminalClosedPrimeBank n) +
        (1 : ℝ) / 2 * terminalSignedRootLedger n := by
  rw [erdos377Mass_eq_sum_depthBandMass, terminalSignedRootLedger]
  calc
    ∑ r ∈ occupiedDepths n, primeHarmonicMass (depthBand n r) =
        ∑ r ∈ occupiedDepths n,
          dynamicBankEnergy (railBand n r) n r := by
            apply sum_congr rfl
            intro r _
            exact (dynamicBankEnergy_railBand_terminal_eq_depthBandMass n r).symm
    _ = ∑ r ∈ occupiedDepths n,
        ((1 : ℝ) / 2 * dynamicBankEnergy (railBand n r) n (r - 1) +
          (1 : ℝ) / 2 * dynamicBankSignedLedger (railBand n r) n (r - 1)) := by
            apply sum_congr rfl
            intro r hr
            have hstep := dynamicBankEnergy_succ_eq_half_add_signed
              (railBand n r) n (r - 1)
            simpa [Nat.sub_add_cancel (occupiedDepth_pos hr)] using hstep
    _ = (1 : ℝ) / 2 *
          (∑ r ∈ occupiedDepths n,
            dynamicBankEnergy (railBand n r) n (r - 1)) +
        (1 : ℝ) / 2 *
          ∑ r ∈ occupiedDepths n,
            dynamicBankSignedLedger (railBand n r) n (r - 1) := by
              rw [sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
    _ = (1 : ℝ) / 2 * primeHarmonicMass (preterminalClosedPrimeBank n) +
        (1 : ℝ) / 2 *
          ∑ r ∈ occupiedDepths n,
            dynamicBankSignedLedger (railBand n r) n (r - 1) := by
              rw [sum_occupiedDepths_preterminalEnergy_eq_primeHarmonicMass]

/-- The terminal signed root ledger is survivor mass minus terminal-failure mass. -/
theorem terminalSignedRootLedger_eq_erdos377Mass_sub_terminalFailureMass (n : ℕ) :
    terminalSignedRootLedger n =
      erdos377Mass n - primeHarmonicMass (terminalFailurePrimeBank n) := by
  have haverage :=
    erdos377Mass_eq_half_preterminalMass_add_half_terminalSignedRootLedger n
  have hsplit :=
    preterminalClosedPrimeBankMass_eq_erdos377Mass_add_terminalFailureMass n
  linarith

/-- Terminal root signs transported losslessly onto the same Mellin carrier as all earlier
cells. -/
noncomputable def terminalSignedFullyMellinRootLedger (n : ℕ) : ℝ :=
  ∑ r ∈ occupiedDepths n,
    fullyMellinReconstructedLedger (railBand n r) n (r - 1)

/-- The terminal Mellin transport preserves the signed root ledger exactly. -/
theorem terminalSignedFullyMellinRootLedger_eq_terminalSignedRootLedger (n : ℕ) :
    terminalSignedFullyMellinRootLedger n = terminalSignedRootLedger n := by
  rw [terminalSignedFullyMellinRootLedger, terminalSignedRootLedger]
  apply sum_congr rfl
  intro r _
  rw [fullyMellinReconstructedLedger_eq_recursiveWarpedLedger,
    ← dynamicBankSignedLedger_eq_recursiveWarpedLedger (railBand_subset_primesLE n r)]

/-- All nonterminal and terminal signed packets on one common harmonic carrier. -/
noncomputable def compensatedFullyMellinLedger (n : ℕ) : ℝ :=
  preterminalSignedFullyMellinLedger n + terminalSignedFullyMellinRootLedger n

/-!
For the next step, no prior expectation about contraction is used.  Two independent executable
decompositions are tested:

1. complete the geometric transfer at one fixed depth, beginning with
   `rw [depthCompensatedFullyMellinLedger]`;
2. telescope the decreasing zero-one survival sequence prime by prime, beginning with
   `rw [firstFailureKernel]`.

The first decomposition is exact below.  The second is developed after it and records the unique
loss of a prime without taking an absolute value.
-/

/-- The compensated Mellin packet at one depth: all earlier dwell-weighted cells followed by the
terminal root cell. -/
noncomputable def depthCompensatedFullyMellinLedger (n r : ℕ) : ℝ :=
  (∑ j ∈ range (r - 1), ((1 : ℝ) / 2) ^ (r - 1 - j) *
      fullyMellinReconstructedLedger (railBand n r) n j) +
    fullyMellinReconstructedLedger (railBand n r) n (r - 1)

/-- The terminal root completes the half-transfer recurrence exactly.  After the completion, the
entire depth packet is twice the terminal energy minus its geometrically damped entrance. -/
theorem depthCompensatedFullyMellinLedger_eq_terminalEnergy
    {n r : ℕ} (hr : 0 < r) :
    depthCompensatedFullyMellinLedger n r =
      2 * dynamicBankEnergy (railBand n r) n r -
        ((1 : ℝ) / 2) ^ (r - 1) * dynamicBankEnergy (railBand n r) n 0 := by
  have htransport (j : ℕ) :
      fullyMellinReconstructedLedger (railBand n r) n j =
        dynamicBankSignedLedger (railBand n r) n j := by
    rw [fullyMellinReconstructedLedger_eq_recursiveWarpedLedger,
      ← dynamicBankSignedLedger_eq_recursiveWarpedLedger (railBand_subset_primesLE n r)]
  have hpre := dynamicBankEnergy_eq_vanishingDwell
    (railBand n r) n (r - 1)
  have hstep := dynamicBankEnergy_succ_eq_half_add_signed
    (railBand n r) n (r - 1)
  have hstep' :
      dynamicBankEnergy (railBand n r) n r =
        (1 : ℝ) / 2 * dynamicBankEnergy (railBand n r) n (r - 1) +
          (1 : ℝ) / 2 * dynamicBankSignedLedger (railBand n r) n (r - 1) := by
    simpa [Nat.sub_add_cancel hr] using hstep
  rw [depthCompensatedFullyMellinLedger]
  simp_rw [htransport]
  linarith

/-- Total loss of one prime after it has entered the first closed cell.  Since the closure weights
form a decreasing zero-one sequence, only the unique first failed cell contributes. -/
noncomputable def postEntranceFirstFailureKernel (p n r : ℕ) : ℝ :=
  ∑ j ∈ range r,
    (dynamicClosureWeight p n j - dynamicClosureWeight p n (j + 1))

/-- First-failure telescoping is exact, with no independence assumption on the digits. -/
theorem postEntranceFirstFailureKernel_eq_entry_sub_terminal (p n r : ℕ) :
    postEntranceFirstFailureKernel p n r =
      dynamicClosureWeight p n 0 - dynamicClosureWeight p n r := by
  rw [postEntranceFirstFailureKernel]
  induction r with
  | zero => simp
  | succ r ih =>
      rw [sum_range_succ, ih]
      ring

/-- Closing more cells can only decrease the exact zero-one closure weight. -/
theorem dynamicClosureWeight_antitone_cells (p n : ℕ) {a b : ℕ} (hab : a ≤ b) :
    dynamicClosureWeight p n b ≤ dynamicClosureWeight p n a := by
  rw [dynamicClosureWeight_eq_ite, dynamicClosureWeight_eq_ite]
  by_cases hb : DynamicClosedOrbit p n (b + 1)
  · have ha : DynamicClosedOrbit p n (a + 1) := by
      intro i hi
      exact hb i (hi.trans_le (Nat.succ_le_succ hab))
    simp [hb, ha]
  · by_cases ha : DynamicClosedOrbit p n (a + 1) <;> simp [hb, ha]

/-- The first-failure charge is a genuine nonnegative stopping kernel. -/
theorem postEntranceFirstFailureKernel_nonneg (p n r : ℕ) :
    0 ≤ postEntranceFirstFailureKernel p n r := by
  rw [postEntranceFirstFailureKernel_eq_entry_sub_terminal]
  exact sub_nonneg.mpr (dynamicClosureWeight_antitone_cells p n (Nat.zero_le r))

/-- The stopping kernel is literally the indicator that the prime entered the carrier but failed
before terminal closure. -/
theorem postEntranceFirstFailureKernel_eq_ite (p n r : ℕ) :
    postEntranceFirstFailureKernel p n r =
      if DynamicClosedOrbit p n 1 ∧ ¬ DynamicClosedOrbit p n (r + 1) then 1 else 0 := by
  rw [postEntranceFirstFailureKernel_eq_entry_sub_terminal,
    dynamicClosureWeight_eq_ite, dynamicClosureWeight_eq_ite]
  by_cases hterminal : DynamicClosedOrbit p n (r + 1)
  · have hentry : DynamicClosedOrbit p n 1 := by
      intro i hi
      exact hterminal i (hi.trans_le (by omega))
    simp [hterminal, hentry]
  · by_cases hentry : DynamicClosedOrbit p n 1 <;> simp [hterminal, hentry]

/-- Consequently every prime pays at most one first-failure charge. -/
theorem postEntranceFirstFailureKernel_le_one (p n r : ℕ) :
    postEntranceFirstFailureKernel p n r ≤ 1 := by
  rw [postEntranceFirstFailureKernel_eq_ite]
  split <;> norm_num

/-- Prime packet that closes the entrance cell but has a later first failure. -/
noncomputable def postEntranceFailurePrimeBank (n r : ℕ) : Finset ℕ := by
  classical
  exact (railBand n r).filter fun p ↦
    DynamicClosedOrbit p n 1 ∧ ¬ DynamicClosedOrbit p n (r + 1)

/-- The first-failure kernel sums to the ordinary harmonic mass of the disjoint failure bank. -/
theorem sum_postEntranceFirstFailureKernel_eq_failureMass (n r : ℕ) :
    (∑ p ∈ railBand n r,
      (1 : ℝ) / (p : ℝ) * postEntranceFirstFailureKernel p n r) =
        primeHarmonicMass (postEntranceFailurePrimeBank n r) := by
  rw [primeHarmonicMass, postEntranceFailurePrimeBank, sum_filter]
  apply sum_congr rfl
  intro p _
  rw [postEntranceFirstFailureKernel_eq_ite]
  by_cases hfailure :
      DynamicClosedOrbit p n 1 ∧ ¬ DynamicClosedOrbit p n (r + 1) <;>
    simp [hfailure]

/-- Flat logarithmic (Haar) weight of one prime sample. -/
noncomputable def mellinPrimeHaarWeight (p : ℕ) : ℝ :=
  Real.log (p : ℝ) / (p : ℝ)

/-- Mellin amplitude converting flat logarithmic prime mass back to harmonic mass. -/
noncomputable def mellinHarmonicAmplitude (p : ℕ) : ℝ :=
  (Real.log (p : ℝ))⁻¹

/-- Exact atom-level harmonic conversion. -/
theorem mellinPrimeHaarWeight_mul_harmonicAmplitude {p : ℕ} (hp : p.Prime) :
    mellinPrimeHaarWeight p * mellinHarmonicAmplitude p = (1 : ℝ) / (p : ℝ) := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hpOne : (p : ℝ) ≠ 1 := by exact_mod_cast hp.ne_one
  have hlog : Real.log (p : ℝ) ≠ 0 :=
    Real.log_ne_zero_of_pos_of_ne_one hpR hpOne
  rw [mellinPrimeHaarWeight, mellinHarmonicAmplitude]
  field_simp

/-- The continuous Mellin amplitude whose prime samples are `mellinHarmonicAmplitude`. -/
noncomputable def continuousMellinHarmonicAmplitude (x : ℝ) : ℝ :=
  (Real.log x)⁻¹

/-- Its derivative is the summable Stieltjes kernel `-1/(x log² x)`. -/
theorem hasDerivAt_continuousMellinHarmonicAmplitude {x : ℝ} (hx : 1 < x) :
    HasDerivAt continuousMellinHarmonicAmplitude (-x⁻¹ / Real.log x ^ 2) x := by
  change HasDerivAt (fun y : ℝ ↦ (Real.log y)⁻¹) (-x⁻¹ / Real.log x ^ 2) x
  exact Real.hasDerivAt_inv_log (by linarith : x ≠ 0) (by linarith : x ≠ 1)
    (by linarith : x ≠ -1)

/-- The entire variation of the harmonic amplitude above `2` has a fixed budget. -/
theorem continuousMellinHarmonicAmplitude_variation_budget {b : ℝ} (hb : 2 ≤ b) :
    (∫ t in (2 : ℝ)..b, t⁻¹ / Real.log t ^ 2) ≤ (Real.log 2)⁻¹ := by
  rw [integral_inv_div_log_sq (by norm_num) (by linarith)]
  have hinvlogb : 0 ≤ (Real.log b)⁻¹ := by
    exact inv_nonneg.mpr (Real.log_nonneg (by linarith))
  linarith

/-- The sampled harmonic amplitude is antitone along increasing prime rails. -/
theorem mellinHarmonicAmplitude_antitone_primes
    {p q : ℕ} (hp : p.Prime) (_hq : q.Prime) (hpq : p ≤ q) :
    mellinHarmonicAmplitude q ≤ mellinHarmonicAmplitude p := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hlogp : 0 < Real.log (p : ℝ) :=
    Real.log_pos (by exact_mod_cast hp.one_lt)
  have hlogpq : Real.log (p : ℝ) ≤ Real.log (q : ℝ) :=
    Real.log_le_log hpR (by exact_mod_cast hpq)
  simpa [mellinHarmonicAmplitude, one_div] using
    one_div_le_one_div_of_le hlogp hlogpq

/-- An antitone carrier has purely endpoint variation on every finite warped mesh. -/
theorem warpedMeshVariation_eq_sub_of_antitone
    (w : ℕ → ℝ) (hanti : Antitone w) (M : ℕ) :
    warpedMeshVariation w M = w 0 - w M := by
  induction M with
  | zero => simp [warpedMeshVariation]
  | succ M ih =>
      rw [warpedMeshVariation, sum_range_succ]
      change warpedMeshVariation w M + |w (M + 1) - w M| = _
      rw [ih, abs_of_nonpos (sub_nonpos.mpr (hanti (Nat.le_succ M)))]
      ring

/-- Endpoint variation of a nonnegative antitone carrier is bounded by its entrance value. -/
theorem warpedMeshVariation_le_entrance_of_antitone_nonneg
    (w : ℕ → ℝ) (hanti : Antitone w) (hnonneg : ∀ i, 0 ≤ w i) (M : ℕ) :
    warpedMeshVariation w M ≤ w 0 := by
  rw [warpedMeshVariation_eq_sub_of_antitone w hanti M]
  linarith [hnonneg M]

/-- Uniform discrete Stieltjes variation for the fully harmonic prime amplitude on any increasing
prime mesh.  The bound is independent of the packet length and of its prime locations. -/
theorem warpedMeshVariation_mellinHarmonicAmplitude_le
    (p : ℕ → ℕ) (hmono : Monotone p) (hprime : ∀ i, (p i).Prime) (M : ℕ) :
    warpedMeshVariation (fun i ↦ mellinHarmonicAmplitude (p i)) M ≤
      (Real.log 2)⁻¹ := by
  have hanti : Antitone (fun i ↦ mellinHarmonicAmplitude (p i)) := by
    intro i j hij
    exact mellinHarmonicAmplitude_antitone_primes (hprime i) (hprime j) (hmono hij)
  have hnonneg (i : ℕ) : 0 ≤ mellinHarmonicAmplitude (p i) := by
    rw [mellinHarmonicAmplitude]
    exact inv_nonneg.mpr (Real.log_nonneg (by exact_mod_cast (hprime i).one_le))
  calc
    warpedMeshVariation (fun i ↦ mellinHarmonicAmplitude (p i)) M ≤
        mellinHarmonicAmplitude (p 0) :=
      warpedMeshVariation_le_entrance_of_antitone_nonneg _ hanti hnonneg M
    _ ≤ (Real.log 2)⁻¹ := by
      have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
      have hlog : Real.log 2 ≤ Real.log (p 0 : ℝ) :=
        Real.log_le_log (by norm_num) (by exact_mod_cast (hprime 0).two_le)
      simpa [mellinHarmonicAmplitude, one_div] using
        one_div_le_one_div_of_le hlog2 hlog

/-- Turnkey Stieltjes transfer on a prime Haar mesh.  Once the flat-log discrepancy increments
have `B`-bounded partial sums, restoring the original harmonic amplitude costs at most the fixed
factor `2 / log 2`, independently of the packet length. -/
theorem mellinHaarPrimeMesh_discreteStieltjesBound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (a : ℕ → E) (p : ℕ → ℕ) (hmono : Monotone p) (hprime : ∀ i, (p i).Prime)
    {B : ℝ} (hB0 : 0 ≤ B) (hB : ∀ k, ‖∑ i ∈ range k, a i‖ ≤ B) :
    ∀ M,
      ‖∑ i ∈ range M, mellinHarmonicAmplitude (p i) • a i‖ ≤
        2 * B * (Real.log 2)⁻¹ := by
  have hampNonneg (i : ℕ) : 0 ≤ mellinHarmonicAmplitude (p i) := by
    rw [mellinHarmonicAmplitude]
    exact inv_nonneg.mpr (Real.log_nonneg (by exact_mod_cast (hprime i).one_le))
  have hampBound (i : ℕ) : ‖mellinHarmonicAmplitude (p i)‖ ≤ (Real.log 2)⁻¹ := by
    rw [Real.norm_eq_abs, abs_of_nonneg (hampNonneg i)]
    have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hlog : Real.log 2 ≤ Real.log (p i : ℝ) :=
      Real.log_le_log (by norm_num) (by exact_mod_cast (hprime i).two_le)
    simpa [mellinHarmonicAmplitude, one_div] using
      one_div_le_one_div_of_le hlog2 hlog
  have hvariation (M : ℕ) :
      warpedMeshVariation (fun i ↦ mellinHarmonicAmplitude (p i)) M ≤
        (Real.log 2)⁻¹ :=
    warpedMeshVariation_mellinHarmonicAmplitude_le p hmono hprime M
  intro M
  have hstieltjes := discreteStieltjesVariationBound a
    (fun i ↦ mellinHarmonicAmplitude (p i)) hB0 hB hampBound hvariation M
  calc
    ‖∑ i ∈ range M, mellinHarmonicAmplitude (p i) • a i‖ ≤
        B * (Real.log 2)⁻¹ + B * (Real.log 2)⁻¹ := hstieltjes
    _ = 2 * B * (Real.log 2)⁻¹ := by ring

/-- Prime-wise form of the compensated depth packet.  The positive entrance budget is depleted
exactly twice at the first failed cell; terminal survivors retain the remainder. -/
theorem depthCompensatedFullyMellinLedger_eq_firstFailureSum
    {n r : ℕ} (hr : 0 < r) :
    depthCompensatedFullyMellinLedger n r =
      ∑ p ∈ railBand n r, (1 : ℝ) / (p : ℝ) *
        (((2 : ℝ) - ((1 : ℝ) / 2) ^ (r - 1)) * dynamicClosureWeight p n 0 -
          2 * postEntranceFirstFailureKernel p n r) := by
  rw [depthCompensatedFullyMellinLedger_eq_terminalEnergy hr,
    dynamicBankEnergy, dynamicBankEnergy, Finset.mul_sum, Finset.mul_sum]
  simp only [← Finset.sum_sub_distrib]
  apply sum_congr rfl
  intro p _
  rw [postEntranceFirstFailureKernel_eq_entry_sub_terminal]
  ring

/-- The global compensated carrier is the sum of its completed depth packets. -/
theorem compensatedFullyMellinLedger_eq_sum_depthCompensated (n : ℕ) :
    compensatedFullyMellinLedger n =
      ∑ r ∈ occupiedDepths n, depthCompensatedFullyMellinLedger n r := by
  simp only [compensatedFullyMellinLedger, preterminalSignedFullyMellinLedger,
    terminalSignedFullyMellinRootLedger, depthCompensatedFullyMellinLedger,
    sum_add_distrib]

/-- Global first-failure normal form.  It is one prime sum on one Mellin scale: an entry charge
minus the disjoint stopping charge, with the terminal survivors left automatically. -/
theorem compensatedFullyMellinLedger_eq_firstFailureLedger (n : ℕ) :
    compensatedFullyMellinLedger n =
      ∑ r ∈ occupiedDepths n,
        ∑ p ∈ railBand n r, (1 : ℝ) / (p : ℝ) *
          (((2 : ℝ) - ((1 : ℝ) / 2) ^ (r - 1)) * dynamicClosureWeight p n 0 -
            2 * postEntranceFirstFailureKernel p n r) := by
  rw [compensatedFullyMellinLedger_eq_sum_depthCompensated]
  apply sum_congr rfl
  intro r hr
  exact depthCompensatedFullyMellinLedger_eq_firstFailureSum (occupiedDepth_pos hr)

/-- Fully scaled global first-failure ledger.  Prime sampling is now measured by flat logarithmic
Haar mass `log p / p`; all non-flatness is isolated in the bounded-variation amplitude
`1 / log p`. -/
theorem compensatedFullyMellinLedger_eq_mellinHaarFirstFailureLedger (n : ℕ) :
    compensatedFullyMellinLedger n =
      ∑ r ∈ occupiedDepths n,
        ∑ p ∈ railBand n r,
          mellinPrimeHaarWeight p * mellinHarmonicAmplitude p *
            (((2 : ℝ) - ((1 : ℝ) / 2) ^ (r - 1)) * dynamicClosureWeight p n 0 -
              2 * postEntranceFirstFailureKernel p n r) := by
  rw [compensatedFullyMellinLedger_eq_firstFailureLedger]
  apply sum_congr rfl
  intro r _
  apply sum_congr rfl
  intro p hp
  rw [mellinPrimeHaarWeight_mul_harmonicAmplitude
    (Nat.prime_of_mem_primesLE (mem_filter.mp hp).1)]

/-- Flat-log compensated charge of one raw prime, with its depth read directly from the prime. -/
noncomputable def mellinHaarCompensatedCharge (n p : ℕ) : ℝ :=
  mellinPrimeHaarWeight p *
    (((2 : ℝ) - ((1 : ℝ) / 2) ^ (railDepth p n - 1)) *
        dynamicClosureWeight p n 0 -
      2 * postEntranceFirstFailureKernel p n (railDepth p n))

/-- The one-prime Haar density has only three values.  A terminal survivor has charge
`2 - 2^{-(r-1)}`, an entered prime with a later failure has charge `-2^{-(r-1)}`, and a prime
that fails at entrance has charge zero. -/
theorem mellinHaarCompensatedCharge_eq_threeWaySign (n p : ℕ) :
    mellinHaarCompensatedCharge n p =
      mellinPrimeHaarWeight p *
        (if DynamicClosedOrbit p n (railDepth p n + 1) then
          (2 : ℝ) - ((1 : ℝ) / 2) ^ (railDepth p n - 1)
        else if DynamicClosedOrbit p n 1 then
          -((1 : ℝ) / 2) ^ (railDepth p n - 1)
        else 0) := by
  rw [mellinHaarCompensatedCharge, dynamicClosureWeight_eq_ite,
    postEntranceFirstFailureKernel_eq_ite]
  by_cases hterminal : DynamicClosedOrbit p n (railDepth p n + 1)
  · have hentry : DynamicClosedOrbit p n 1 := by
      intro i hi
      exact hterminal i (hi.trans_le (by omega))
    simp [hterminal, hentry]
  · by_cases hentry : DynamicClosedOrbit p n 1 <;> simp [hterminal, hentry]

/-- Cumulative flat-log compensated charge up to a prime cutoff. -/
noncomputable def mellinHaarCompensatedCumulative (n x : ℕ) : ℝ :=
  ∑ p ∈ (occupiedRawPrimeBank n).filter (· ≤ x), mellinHaarCompensatedCharge n p

/-- Fiber collapse to one increasing prime carrier.  Depth is now state carried by the prime, so
the Stieltjes mesh no longer has a separate outer depth sum. -/
theorem compensatedFullyMellinLedger_eq_onePrimeMellinHaarLedger (n : ℕ) :
    compensatedFullyMellinLedger n =
      ∑ p ∈ occupiedRawPrimeBank n,
        mellinHarmonicAmplitude p * mellinHaarCompensatedCharge n p := by
  classical
  let u := occupiedRawPrimeBank n
  have hmaps : ∀ p ∈ u, railDepth p n ∈ occupiedDepths n := by
    intro p hp
    exact (mem_filter.mp hp).2
  have hfiber (r : ℕ) (hr : r ∈ occupiedDepths n) :
      u.filter (fun p ↦ railDepth p n = r) = railBand n r := by
    ext p
    simp only [u, occupiedRawPrimeBank, railBand, mem_filter]
    constructor
    · rintro ⟨⟨hpn, _⟩, hdepth⟩
      exact ⟨hpn, hdepth⟩
    · rintro ⟨hpn, hdepth⟩
      refine ⟨⟨hpn, ?_⟩, hdepth⟩
      rw [hdepth]
      exact hr
  rw [compensatedFullyMellinLedger_eq_mellinHaarFirstFailureLedger]
  calc
    (∑ r ∈ occupiedDepths n,
        ∑ p ∈ railBand n r,
          mellinPrimeHaarWeight p * mellinHarmonicAmplitude p *
            (((2 : ℝ) - ((1 : ℝ) / 2) ^ (r - 1)) * dynamicClosureWeight p n 0 -
              2 * postEntranceFirstFailureKernel p n r)) =
        ∑ r ∈ occupiedDepths n,
          ∑ p ∈ u with railDepth p n = r,
            mellinHarmonicAmplitude p * mellinHaarCompensatedCharge n p := by
              apply sum_congr rfl
              intro r hr
              rw [hfiber r hr]
              apply sum_congr rfl
              intro p hp
              simp only [mellinHaarCompensatedCharge]
              rw [(mem_filter.mp hp).2]
              ring
    _ = ∑ p ∈ u,
          mellinHarmonicAmplitude p * mellinHaarCompensatedCharge n p := by
            exact Finset.sum_fiberwise_of_maps_to hmaps _

/-- Exact compensated readout.  Terminal failures cancel their preterminal charge before any
absolute value is introduced. -/
theorem erdos377Mass_eq_half_entrance_add_half_compensatedFullyMellinLedger (n : ℕ) :
    erdos377Mass n =
      (1 : ℝ) / 2 *
        (∑ r ∈ occupiedDepths n,
          ((1 : ℝ) / 2) ^ (r - 1) * dynamicBankEnergy (railBand n r) n 0) +
        (1 : ℝ) / 2 * compensatedFullyMellinLedger n := by
  have haverage :=
    erdos377Mass_eq_half_preterminalMass_add_half_terminalSignedRootLedger n
  have hpreterminal :=
    preterminalSignedWarpedLedger_eq_preterminalMass_sub_entrance n
  have hnonterminal := preterminalSignedFullyMellinLedger_eq_signedWarpedLedger n
  have hterminal := terminalSignedFullyMellinRootLedger_eq_terminalSignedRootLedger n
  rw [compensatedFullyMellinLedger]
  linarith

/-- The same preterminal norm before logarithmic normalization. -/
noncomputable def preterminalWarpedVariation (n : ℕ) : ℝ :=
  ∑ r ∈ occupiedDepths n,
    ∑ j ∈ range (r - 1), ((1 : ℝ) / 2) ^ (r - 1 - j) *
      recursiveWarpedInteriorVariation (railBand n r) n j

/-- Stopping-time envelope obtained by charging every complete warped cell to the survivor that
occupies it.  This keeps the exact dwell exponent and is the unsigned harmonic target left after
the cell geometry has been discharged. -/
noncomputable def preterminalSurvivorEnergy (n : ℕ) : ℝ :=
  ∑ r ∈ occupiedDepths n,
    ∑ j ∈ range (r - 1), ((1 : ℝ) / 2) ^ (r - 1 - j) *
      dynamicBankEnergy (railBand n r) n j

/-- Global warped-variation contraction into the exact dwell-weighted survivor energy. -/
theorem preterminalWarpedVariation_le_survivorEnergy (n : ℕ) :
    preterminalWarpedVariation n ≤ preterminalSurvivorEnergy n := by
  rw [preterminalWarpedVariation, preterminalSurvivorEnergy]
  apply sum_le_sum
  intro r _
  apply sum_le_sum
  intro j _
  exact mul_le_mul_of_nonneg_left
    (recursiveWarpedInteriorVariation_le_dynamicBankEnergy
      (railBand_subset_primesLE n r)) (by positivity)

/-- A coherent power rail carries exactly one third-unit of survivor energy at every active
preterminal depth. -/
theorem dynamicBankEnergy_railBand_three_pow_eq_one_third
    {r j : ℕ} (hr : 2 ≤ r) (hj : j + 1 ≤ r) :
    dynamicBankEnergy (railBand (3 ^ r) r) (3 ^ r) j = (1 : ℝ) / 3 := by
  rw [railBand_three_pow hr, dynamicBankEnergy]
  simp only [sum_singleton, dynamicClosureWeight]
  rw [three_pow_dynamicSurvivalWeight_eq_one hj]
  norm_num

/-- The same coherent rail has positive square-wave orientation at every nonterminal cell. -/
theorem three_pow_nonterminal_dynamicBankSignedLedger_eq_one_third
    {r j : ℕ} (hr : 2 ≤ r) (hj : j + 2 ≤ r) :
    dynamicBankSignedLedger (railBand (3 ^ r) r) (3 ^ r) j = (1 : ℝ) / 3 := by
  rw [railBand_three_pow hr, dynamicBankSignedLedger]
  simp only [sum_singleton]
  have hclosure : dynamicClosureWeight 3 (3 ^ r) j = 1 := by
    rw [dynamicClosureWeight]
    exact three_pow_dynamicSurvivalWeight_eq_one (by omega)
  have hsign : dynamicSquareSign 3 (3 ^ r) j = 1 := by
    rw [dynamicSquareSign, if_pos]
    apply (harmonizedCellPhase_lt_half_iff
      (p := 3) (n := 3 ^ r) (j := j + 1) (by norm_num)).mpr
    rw [Nat.mod_eq_zero_of_dvd (Nat.pow_dvd_pow 3 hj)]
    positivity
  rw [hclosure, hsign]
  norm_num

/-- Exact contour reconstruction forces at least one third-unit of complete-cell variation on a
coherent nonterminal power rail. -/
theorem one_third_le_recursiveWarpedInteriorVariation_three_pow
    {r j : ℕ} (hr : 2 ≤ r) (hj : j + 2 ≤ r) :
    (1 : ℝ) / 3 ≤
      recursiveWarpedInteriorVariation (railBand (3 ^ r) r) (3 ^ r) j := by
  have hjnonterminal : j + 1 < r := by omega
  have hvariation :=
    abs_railBand_recursiveWarpedLedger_nonterminal_le_variation
      (n := 3 ^ r) hjnonterminal
  rw [← dynamicBankSignedLedger_eq_recursiveWarpedLedger
      (railBand_subset_primesLE (3 ^ r) r),
    three_pow_nonterminal_dynamicBankSignedLedger_eq_one_third hr hj,
    abs_of_pos (by norm_num)] at hvariation
  exact hvariation

/-- The last preterminal cell of `3^r` alone contributes at least one sixth-unit. -/
theorem one_six_le_depthPreterminalWarpedVariation_three_pow
    {r : ℕ} (hr : 2 ≤ r) :
    (1 : ℝ) / 6 ≤ depthPreterminalWarpedVariation (3 ^ r) r := by
  rw [depthPreterminalWarpedVariation]
  have hmem : r - 2 ∈ range (r - 1) := mem_range.mpr (by omega)
  calc
    (1 : ℝ) / 6 ≤ ((1 : ℝ) / 2) ^ (r - 1 - (r - 2)) *
        recursiveWarpedInteriorVariation (railBand (3 ^ r) r) (3 ^ r) (r - 2) := by
          have hexp : r - 1 - (r - 2) = 1 := by omega
          rw [hexp, pow_one]
          nlinarith [one_third_le_recursiveWarpedInteriorVariation_three_pow
            hr (by omega : r - 2 + 2 ≤ r)]
    _ ≤ ∑ j ∈ range (r - 1), ((1 : ℝ) / 2) ^ (r - 1 - j) *
        recursiveWarpedInteriorVariation (railBand (3 ^ r) r) (3 ^ r) j := by
          exact Finset.single_le_sum (s := range (r - 1))
            (f := fun j ↦ ((1 : ℝ) / 2) ^ (r - 1 - j) *
              recursiveWarpedInteriorVariation (railBand (3 ^ r) r) (3 ^ r) j) (by
                intro j _
                exact mul_nonneg (by positivity) (by
                  rw [recursiveWarpedInteriorVariation]
                  positivity)) hmem

/-- Consequently the raw depth ledger cannot be assigned geometric decay uniformly: coherent
atoms must be charged to a separate uniform atomic budget before a summable diffuse estimate. -/
theorem not_exists_uniformPreterminalWarpedDepthDecay :
    ¬ ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℕ, 2 ≤ r →
      depthPreterminalWarpedVariation (3 ^ r) r ≤
        C * ((1 : ℝ) / 2) ^ r := by
  rintro ⟨C, hC, hdecay⟩
  by_cases hCzero : C = 0
  · have hlower := one_six_le_depthPreterminalWarpedVariation_three_pow
      (r := 2) (by omega)
    have hupper := hdecay 2 (by omega)
    rw [hCzero] at hupper
    norm_num at hupper
    linarith
  · have hCpos : 0 < C := lt_of_le_of_ne hC (Ne.symm hCzero)
    have hthreshold : 0 < (1 : ℝ) / (6 * (C + 1)) := by positivity
    obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one hthreshold
      (by norm_num : (1 : ℝ) / 2 < 1)
    let K := k + 2
    have hK : 2 ≤ K := by simp [K]
    have hpow : ((1 : ℝ) / 2) ^ K ≤ ((1 : ℝ) / 2) ^ k := by
      rw [show K = k + 2 by rfl, pow_add]
      norm_num
    have hCdecay : C * ((1 : ℝ) / 2) ^ K < (1 : ℝ) / 6 := calc
      C * ((1 : ℝ) / 2) ^ K ≤ C * ((1 : ℝ) / 2) ^ k :=
        mul_le_mul_of_nonneg_left hpow hC
      _ < C * ((1 : ℝ) / (6 * (C + 1))) := mul_lt_mul_of_pos_left hk hCpos
      _ < (1 : ℝ) / 6 := by
        rw [div_eq_mul_inv]
        field_simp
        linarith
    have hlower := one_six_le_depthPreterminalWarpedVariation_three_pow hK
    have hupper := hdecay K hK
    linarith

/-- The empty prime bank has no warped cell variation. -/
theorem recursiveWarpedInteriorVariation_empty (n j : ℕ) :
    recursiveWarpedInteriorVariation ∅ n j = 0 := by
  simp [recursiveWarpedInteriorVariation, dynamicPrefixPrimeBank,
    dynamicSurvivingPrimeBank, bankPrimeReciprocalCumulative,
    reciprocalCellSecondDifference]

/-- Complete-cell variation on harmonically concentrated depth bands. -/
noncomputable def preterminalHarmonicAtomicWarpedVariation (n : ℕ) : ℝ :=
  ∑ r ∈ occupiedDepths n,
    ∑ j ∈ range (r - 1), ((1 : ℝ) / 2) ^ (r - 1 - j) *
      recursiveWarpedInteriorVariation (harmonicAtomicRailBand n r) n j

/-- Complete-cell variation on the harmonic-diffuse depth bands. -/
noncomputable def preterminalHarmonicDiffuseWarpedVariation (n : ℕ) : ℝ :=
  ∑ r ∈ occupiedDepths n,
    ∑ j ∈ range (r - 1), ((1 : ℝ) / 2) ^ (r - 1 - j) *
      recursiveWarpedInteriorVariation (harmonicDiffuseRailBand n r) n j

/-- Corrected structural target: the global warped variation is exactly an atomic budget plus a
diffuse variation ledger.  The coherent power obstruction lies wholly in the first summand. -/
theorem preterminalWarpedVariation_eq_harmonicAtomic_add_diffuse (n : ℕ) :
    preterminalWarpedVariation n =
      preterminalHarmonicAtomicWarpedVariation n +
        preterminalHarmonicDiffuseWarpedVariation n := by
  rw [preterminalWarpedVariation, preterminalHarmonicAtomicWarpedVariation,
    preterminalHarmonicDiffuseWarpedVariation, ← sum_add_distrib]
  apply sum_congr rfl
  intro r _
  rw [← sum_add_distrib]
  apply sum_congr rfl
  intro j _
  by_cases h : IsHarmonicAtomicRailBand n r
  · simp [harmonicAtomicRailBand, harmonicDiffuseRailBand, h,
      recursiveWarpedInteriorVariation_empty]
  · simp [harmonicAtomicRailBand, harmonicDiffuseRailBand, h,
      recursiveWarpedInteriorVariation_empty]

/-- Dwell-weighted cost of the exact discrete Mellin clock adapters. -/
noncomputable def preterminalMellinAdapterCost (n : ℕ) : ℝ :=
  ∑ r ∈ occupiedDepths n,
    ∑ j ∈ range (r - 1), ((1 : ℝ) / 2) ^ (r - 1 - j) *
      recursiveMellinAdapterVariation (railBand n r) n j

/-- Preterminal cost caused only by changes in the sampled survivor potentials. -/
noncomputable def preterminalMellinSamplingAdapterCost (n : ℕ) : ℝ :=
  ∑ r ∈ occupiedDepths n,
    ∑ j ∈ range (r - 1), ((1 : ℝ) / 2) ^ (r - 1 - j) *
      recursiveMellinSamplingAdapterVariation (railBand n r) n j

/-- Preterminal cost caused only by discrete logarithmic clock curvature. -/
noncomputable def preterminalMellinClockCurvatureCost (n : ℕ) : ℝ :=
  ∑ r ∈ occupiedDepths n,
    ∑ j ∈ range (r - 1), ((1 : ℝ) / 2) ^ (r - 1 - j) *
      recursiveMellinClockCurvatureVariation (railBand n r) n j

/-- Dwell-weighted continuous reflected-residual clock cost. -/
noncomputable def preterminalMellinContinuousClockCurvatureCost (n : ℕ) : ℝ :=
  ∑ r ∈ occupiedDepths n,
    ∑ j ∈ range (r - 1), ((1 : ℝ) / 2) ^ (r - 1 - j) *
      recursiveMellinContinuousClockCurvatureVariation (railBand n r) n j

/-- Dwell-weighted integer-floor clock quantization cost. -/
noncomputable def preterminalMellinClockQuantizationCost (n : ℕ) : ℝ :=
  ∑ r ∈ occupiedDepths n,
    ∑ j ∈ range (r - 1), ((1 : ℝ) / 2) ^ (r - 1 - j) *
      recursiveMellinClockQuantizationVariation (railBand n r) n j

/-- Empty survivor banks contribute no arithmetic sampling variation. -/
theorem recursiveMellinSamplingAdapterVariation_empty (n j : ℕ) :
    recursiveMellinSamplingAdapterVariation ∅ n j = 0 := by
  have hempty (m : ℕ) : dynamicPrefixPrimeBank ∅ n j m = ∅ := by
    simp [dynamicPrefixPrimeBank, dynamicSurvivingPrimeBank]
  simp [recursiveMellinSamplingAdapterVariation, mellinCellSamplingAdapter,
    normalizedBankPrimeCarrier, bankPrimeReciprocalCumulative, hempty]

/-- Empty survivor banks contribute no integer-clock quantization variation. -/
theorem recursiveMellinClockQuantizationVariation_empty (n j : ℕ) :
    recursiveMellinClockQuantizationVariation ∅ n j = 0 := by
  have hempty (m : ℕ) : dynamicPrefixPrimeBank ∅ n j m = ∅ := by
    simp [dynamicPrefixPrimeBank, dynamicSurvivingPrimeBank]
  simp [recursiveMellinClockQuantizationVariation,
    mellinCellClockQuantizationCurvature, normalizedBankPrimeCarrier,
    bankPrimeReciprocalCumulative, hempty]

/-- The exact local ledger still present after the continuous Mellin clock has been discharged. -/
noncomputable def recursiveWarpedSamplingQuantizationVariation
    (s : Finset ℕ) (n j : ℕ) : ℝ :=
  recursiveWarpedInteriorVariation s n j +
    (recursiveMellinSamplingAdapterVariation s n j +
      recursiveMellinClockQuantizationVariation s n j) +
    (recursiveMellinSamplingAdapterVariation s n j +
      recursiveMellinClockQuantizationVariation s n j)

theorem recursiveWarpedSamplingQuantizationVariation_empty (n j : ℕ) :
    recursiveWarpedSamplingQuantizationVariation ∅ n j = 0 := by
  rw [recursiveWarpedSamplingQuantizationVariation,
    recursiveWarpedInteriorVariation_empty,
    recursiveMellinSamplingAdapterVariation_empty,
    recursiveMellinClockQuantizationVariation_empty]
  ring

/-- Named form of the entire remaining dwell-weighted target. -/
noncomputable def preterminalWarpedSamplingQuantizationVariation (n : ℕ) : ℝ :=
  ∑ r ∈ occupiedDepths n,
    ∑ j ∈ range (r - 1), ((1 : ℝ) / 2) ^ (r - 1 - j) *
      recursiveWarpedSamplingQuantizationVariation (railBand n r) n j

/-- The named target is definitionally the raw warped ledger plus the two adapter copies in the
global reduction. -/
theorem preterminalWarpedSamplingQuantizationVariation_eq (n : ℕ) :
    preterminalWarpedSamplingQuantizationVariation n =
      preterminalWarpedVariation n +
        (preterminalMellinSamplingAdapterCost n +
          preterminalMellinClockQuantizationCost n) +
        (preterminalMellinSamplingAdapterCost n +
          preterminalMellinClockQuantizationCost n) := by
  rw [preterminalWarpedSamplingQuantizationVariation,
    preterminalWarpedVariation, preterminalMellinSamplingAdapterCost,
    preterminalMellinClockQuantizationCost]
  simp_rw [recursiveWarpedSamplingQuantizationVariation]
  simp only [mul_add, sum_add_distrib]

/-- Remaining ledger on harmonically concentrated depth bands. -/
noncomputable def preterminalHarmonicAtomicWarpedSamplingQuantizationVariation
    (n : ℕ) : ℝ :=
  ∑ r ∈ occupiedDepths n,
    ∑ j ∈ range (r - 1), ((1 : ℝ) / 2) ^ (r - 1 - j) *
      recursiveWarpedSamplingQuantizationVariation
        (harmonicAtomicRailBand n r) n j

/-- Remaining ledger on harmonic-diffuse depth bands. -/
noncomputable def preterminalHarmonicDiffuseWarpedSamplingQuantizationVariation
    (n : ℕ) : ℝ :=
  ∑ r ∈ occupiedDepths n,
    ∑ j ∈ range (r - 1), ((1 : ℝ) / 2) ^ (r - 1 - j) *
      recursiveWarpedSamplingQuantizationVariation
        (harmonicDiffuseRailBand n r) n j

/-- Exact atomic/diffuse split of the whole remaining target, including both discrete adapters. -/
theorem preterminalWarpedSamplingQuantizationVariation_eq_atomic_add_diffuse (n : ℕ) :
    preterminalWarpedSamplingQuantizationVariation n =
      preterminalHarmonicAtomicWarpedSamplingQuantizationVariation n +
        preterminalHarmonicDiffuseWarpedSamplingQuantizationVariation n := by
  rw [preterminalWarpedSamplingQuantizationVariation,
    preterminalHarmonicAtomicWarpedSamplingQuantizationVariation,
    preterminalHarmonicDiffuseWarpedSamplingQuantizationVariation,
    ← sum_add_distrib]
  apply sum_congr rfl
  intro r _
  rw [← sum_add_distrib]
  apply sum_congr rfl
  intro j _
  by_cases h : IsHarmonicAtomicRailBand n r
  · simp [harmonicAtomicRailBand, harmonicDiffuseRailBand, h,
      recursiveWarpedSamplingQuantizationVariation_empty]
  · simp [harmonicAtomicRailBand, harmonicDiffuseRailBand, h,
      recursiveWarpedSamplingQuantizationVariation_empty]

/-- Occupied raw depth rails are disjoint fibers of the ambient prime bank, also in the fully
Mellin-scaled measure. -/
theorem sum_occupiedDepths_primeMellinMass_railBand_le (n : ℕ) :
    ∑ r ∈ occupiedDepths n, primeMellinMass (railBand n r) ≤
      primeMellinMass n.primesLE := by
  classical
  let u := n.primesLE.filter fun p ↦ railDepth p n ∈ occupiedDepths n
  have hmaps : ∀ p ∈ u, railDepth p n ∈ occupiedDepths n := by
    intro p hp
    exact (mem_filter.mp hp).2
  have hfiber (r : ℕ) (hr : r ∈ occupiedDepths n) :
      u.filter (fun p ↦ railDepth p n = r) = railBand n r := by
    ext p
    simp only [u, railBand, mem_filter]
    constructor
    · rintro ⟨⟨hpn, _⟩, hdepth⟩
      exact ⟨hpn, hdepth⟩
    · rintro ⟨hpn, hdepth⟩
      refine ⟨⟨hpn, ?_⟩, hdepth⟩
      rw [hdepth]
      exact hr
  simp only [primeMellinMass]
  calc
    (∑ r ∈ occupiedDepths n,
        ∑ p ∈ railBand n r, ((1 : ℝ) / (p : ℝ)) / mellinClock p) =
      ∑ r ∈ occupiedDepths n,
        ∑ p ∈ u with railDepth p n = r,
          ((1 : ℝ) / (p : ℝ)) / mellinClock p := by
            apply sum_congr rfl
            intro r hr
            rw [hfiber r hr]
    _ = ∑ p ∈ u, ((1 : ℝ) / (p : ℝ)) / mellinClock p := by
      exact Finset.sum_fiberwise_of_maps_to hmaps _
    _ ≤ ∑ p ∈ n.primesLE, ((1 : ℝ) / (p : ℝ)) / mellinClock p := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro p hp
        exact (mem_filter.mp hp).1
      · intro p _ _
        exact div_nonneg (by positivity) (mellinClock_pos p).le

/-- After scaling reciprocal weights and every contour cutoff on the same Mellin carrier, the
whole continuous clock-curvature ledger is bounded by one quarter of ambient prime Mellin mass. -/
theorem preterminalMellinContinuousClockCurvatureCost_le_primeMellinMass (n : ℕ) :
    preterminalMellinContinuousClockCurvatureCost n ≤
      primeMellinMass n.primesLE * ((1 : ℝ) / 4) := by
  rw [preterminalMellinContinuousClockCurvatureCost]
  calc
    (∑ r ∈ occupiedDepths n,
        ∑ j ∈ range (r - 1), ((1 : ℝ) / 2) ^ (r - 1 - j) *
          recursiveMellinContinuousClockCurvatureVariation (railBand n r) n j) ≤
      ∑ r ∈ occupiedDepths n, primeMellinMass (railBand n r) * ((1 : ℝ) / 4) := by
        apply sum_le_sum
        intro r _
        calc
          (∑ j ∈ range (r - 1), ((1 : ℝ) / 2) ^ (r - 1 - j) *
              recursiveMellinContinuousClockCurvatureVariation (railBand n r) n j) ≤
            ∑ j ∈ range (r - 1), ((1 : ℝ) / 2) ^ (r - 1 - j) *
              (primeMellinMass (railBand n r) * ((1 : ℝ) / 4)) := by
                apply sum_le_sum
                intro j _
                exact mul_le_mul_of_nonneg_left
                  (recursiveMellinContinuousClockCurvatureVariation_le_primeMellinMass
                    (railBand n r) n j) (by positivity)
          _ = (∑ j ∈ range (r - 1), ((1 : ℝ) / 2) ^ (r - 1 - j)) *
              (primeMellinMass (railBand n r) * ((1 : ℝ) / 4)) := by
                rw [Finset.sum_mul]
          _ ≤ primeMellinMass (railBand n r) * ((1 : ℝ) / 4) := by
            simpa only [one_mul] using mul_le_mul_of_nonneg_right
              (sum_range_preterminal_half_pow_le_one r)
              (mul_nonneg (primeMellinMass_nonneg _) (by norm_num))
    _ = (∑ r ∈ occupiedDepths n, primeMellinMass (railBand n r)) *
        ((1 : ℝ) / 4) := by
          rw [Finset.sum_mul]
    _ ≤ primeMellinMass n.primesLE * ((1 : ℝ) / 4) :=
      mul_le_mul_of_nonneg_right (sum_occupiedDepths_primeMellinMass_railBand_le n) (by norm_num)

/-- Uniform discharge of the continuous warped-clock ledger on the fully harmonic scale. -/
theorem preterminalMellinContinuousClockCurvatureCost_uniform (n : ℕ) :
    preterminalMellinContinuousClockCurvatureCost n ≤
      ((2 + 3 * (2 * Real.log 4 + 2)) / Real.log 2) * ((1 : ℝ) / 4) := by
  exact (preterminalMellinContinuousClockCurvatureCost_le_primeMellinMass n).trans
    (mul_le_mul_of_nonneg_right (primeMellinMass_primesLE_uniform n) (by norm_num))

/-- The global discrete clock cost splits into continuous residual and integer-floor error. -/
theorem preterminalMellinClockCurvatureCost_le_continuous_add_quantization (n : ℕ) :
    preterminalMellinClockCurvatureCost n ≤
      preterminalMellinContinuousClockCurvatureCost n +
        preterminalMellinClockQuantizationCost n := by
  rw [preterminalMellinClockCurvatureCost,
    preterminalMellinContinuousClockCurvatureCost,
    preterminalMellinClockQuantizationCost, ← sum_add_distrib]
  apply sum_le_sum
  intro r _
  rw [← sum_add_distrib]
  apply sum_le_sum
  intro j _
  have hdwell : 0 ≤ ((1 : ℝ) / 2) ^ (r - 1 - j) :=
    pow_nonneg (by norm_num) _
  calc
    ((1 : ℝ) / 2) ^ (r - 1 - j) *
        recursiveMellinClockCurvatureVariation (railBand n r) n j ≤
      ((1 : ℝ) / 2) ^ (r - 1 - j) *
        (recursiveMellinContinuousClockCurvatureVariation (railBand n r) n j +
          recursiveMellinClockQuantizationVariation (railBand n r) n j) :=
        mul_le_mul_of_nonneg_left
          (recursiveMellinClockCurvatureVariation_le_continuous_add_quantization
            (railBand n r) n j) hdwell
    _ = ((1 : ℝ) / 2) ^ (r - 1 - j) *
          recursiveMellinContinuousClockCurvatureVariation (railBand n r) n j +
        ((1 : ℝ) / 2) ^ (r - 1 - j) *
          recursiveMellinClockQuantizationVariation (railBand n r) n j := by ring

/-- The global adapter split inherits the exact local sampling/clock separation. -/
theorem preterminalMellinAdapterCost_le_sampling_add_clockCurvature (n : ℕ) :
    preterminalMellinAdapterCost n ≤
      preterminalMellinSamplingAdapterCost n +
        preterminalMellinClockCurvatureCost n := by
  rw [preterminalMellinAdapterCost, preterminalMellinSamplingAdapterCost,
    preterminalMellinClockCurvatureCost, ← sum_add_distrib]
  apply sum_le_sum
  intro r _
  rw [← sum_add_distrib]
  apply sum_le_sum
  intro j _
  have hdwell : 0 ≤ ((1 : ℝ) / 2) ^ (r - 1 - j) :=
    pow_nonneg (by norm_num) _
  calc
    ((1 : ℝ) / 2) ^ (r - 1 - j) *
        recursiveMellinAdapterVariation (railBand n r) n j ≤
      ((1 : ℝ) / 2) ^ (r - 1 - j) *
        (recursiveMellinSamplingAdapterVariation (railBand n r) n j +
          recursiveMellinClockCurvatureVariation (railBand n r) n j) :=
        mul_le_mul_of_nonneg_left
          (recursiveMellinAdapterVariation_le_sampling_add_clockCurvature
            (railBand n r) n j) hdwell
    _ = ((1 : ℝ) / 2) ^ (r - 1 - j) *
          recursiveMellinSamplingAdapterVariation (railBand n r) n j +
        ((1 : ℝ) / 2) ^ (r - 1 - j) *
          recursiveMellinClockCurvatureVariation (railBand n r) n j := by ring

/-- Reverse harmonic conversion at every recursive depth: the requested preterminal Mellin norm
is reduced to raw reflected-packet variation and two copies of the discrete clock adapter. -/
theorem preterminalMellinVariation_le_warped_add_two_adapters (n : ℕ) :
    preterminalMellinVariation n ≤
      preterminalWarpedVariation n + preterminalMellinAdapterCost n +
        preterminalMellinAdapterCost n := by
  rw [preterminalMellinVariation, preterminalWarpedVariation,
    preterminalMellinAdapterCost]
  calc
    _ ≤ ∑ r ∈ occupiedDepths n,
        ∑ j ∈ range (r - 1), ((1 : ℝ) / 2) ^ (r - 1 - j) *
          (recursiveWarpedInteriorVariation (railBand n r) n j +
            recursiveMellinAdapterVariation (railBand n r) n j +
              recursiveMellinAdapterVariation (railBand n r) n j) := by
      apply sum_le_sum
      intro r _
      apply sum_le_sum
      intro j _
      exact mul_le_mul_of_nonneg_left
        (mellinComponents_le_recursiveWarpedInteriorVariation_add_two_adapters
          (railBand n r) n j) (by positivity)
    _ = (∑ r ∈ occupiedDepths n,
          ∑ j ∈ range (r - 1), ((1 : ℝ) / 2) ^ (r - 1 - j) *
            recursiveWarpedInteriorVariation (railBand n r) n j) +
        (∑ r ∈ occupiedDepths n,
          ∑ j ∈ range (r - 1), ((1 : ℝ) / 2) ^ (r - 1 - j) *
            recursiveMellinAdapterVariation (railBand n r) n j) +
        ∑ r ∈ occupiedDepths n,
          ∑ j ∈ range (r - 1), ((1 : ℝ) / 2) ^ (r - 1 - j) *
            recursiveMellinAdapterVariation (railBand n r) n j := by
      simp only [mul_add, sum_add_distrib]

/-- Final exact routing of the requested norm: raw reflected-packet variation, arithmetic
sampling variation, and pure logarithmic clock curvature are now separate finite ledgers. -/
theorem preterminalMellinVariation_le_warped_add_sampling_add_clock (n : ℕ) :
    preterminalMellinVariation n ≤
      preterminalWarpedVariation n +
        (preterminalMellinSamplingAdapterCost n +
          preterminalMellinClockCurvatureCost n) +
        (preterminalMellinSamplingAdapterCost n +
          preterminalMellinClockCurvatureCost n) := by
  have hreverse := preterminalMellinVariation_le_warped_add_two_adapters n
  have hadapter := preterminalMellinAdapterCost_le_sampling_add_clockCurvature n
  linarith

/-- Fully resolved adapter routing: continuous carrier curvature and integer-floor quantization
are separate from the prime-survivor sampling ledger. -/
theorem preterminalMellinVariation_le_warped_add_sampling_continuous_quantization
    (n : ℕ) :
    preterminalMellinVariation n ≤
      preterminalWarpedVariation n +
        (preterminalMellinSamplingAdapterCost n +
          preterminalMellinContinuousClockCurvatureCost n +
            preterminalMellinClockQuantizationCost n) +
        (preterminalMellinSamplingAdapterCost n +
          preterminalMellinContinuousClockCurvatureCost n +
            preterminalMellinClockQuantizationCost n) := by
  have hsplit := preterminalMellinVariation_le_warped_add_sampling_add_clock n
  have hclock := preterminalMellinClockCurvatureCost_le_continuous_add_quantization n
  linarith

/-- The continuous carrier has now been discharged uniformly; only raw packet variation,
survivor sampling, and the explicit integer-floor quantization adapter remain. -/
theorem preterminalMellinVariation_le_uniformClock_add_warped_sampling_quantization
    (n : ℕ) :
    preterminalMellinVariation n ≤
      2 * (((2 + 3 * (2 * Real.log 4 + 2)) / Real.log 2) * ((1 : ℝ) / 4)) +
        preterminalWarpedVariation n +
          (preterminalMellinSamplingAdapterCost n +
            preterminalMellinClockQuantizationCost n) +
          (preterminalMellinSamplingAdapterCost n +
            preterminalMellinClockQuantizationCost n) := by
  have hsplit :=
    preterminalMellinVariation_le_warped_add_sampling_continuous_quantization n
  have hclock := preterminalMellinContinuousClockCurvatureCost_uniform n
  linarith

/-- After the uniform entrance estimate, only preterminal Mellin variation remains globally. -/
theorem erdos377Mass_le_uniformEntrance_add_preterminalVariation :
    ∃ C : ℝ, ∀ n : ℕ,
      erdos377Mass n ≤ C +
        ∑ r ∈ occupiedDepths n,
          ∑ j ∈ range (r - 1), ((1 : ℝ) / 2) ^ (r - 1 - j) *
            (recursiveMellinCurvatureVariation (railBand n r) n j +
              recursiveMellinAdapterVariation (railBand n r) n j) := by
  rcases preterminalEntrance_uniform with ⟨C, hC⟩
  refine ⟨C, ?_⟩
  intro n
  calc
    erdos377Mass n ≤
        ∑ r ∈ occupiedDepths n,
          (((1 : ℝ) / 2) ^ (r - 1) * dynamicBankEnergy (railBand n r) n 0 +
            ∑ j ∈ range (r - 1), ((1 : ℝ) / 2) ^ (r - 1 - j) *
              (recursiveMellinCurvatureVariation (railBand n r) n j +
                recursiveMellinAdapterVariation (railBand n r) n j)) :=
      erdos377Mass_le_sum_preterminalFullMellin n
    _ = (∑ r ∈ occupiedDepths n,
          ((1 : ℝ) / 2) ^ (r - 1) * dynamicBankEnergy (railBand n r) n 0) +
        ∑ r ∈ occupiedDepths n,
          ∑ j ∈ range (r - 1), ((1 : ℝ) / 2) ^ (r - 1 - j) *
            (recursiveMellinCurvatureVariation (railBand n r) n j +
              recursiveMellinAdapterVariation (railBand n r) n j) := by
      rw [sum_add_distrib]
    _ ≤ C +
        ∑ r ∈ occupiedDepths n,
          ∑ j ∈ range (r - 1), ((1 : ℝ) / 2) ^ (r - 1 - j) *
            (recursiveMellinCurvatureVariation (railBand n r) n j +
              recursiveMellinAdapterVariation (railBand n r) n j) :=
      add_le_add_left (hC n) _

/-- Named form of the remaining target norm. -/
theorem erdos377Mass_le_uniformEntrance_add_preterminalMellinVariation :
    ∃ C : ℝ, ∀ n : ℕ,
      erdos377Mass n ≤ C + preterminalMellinVariation n := by
  simpa [preterminalMellinVariation] using
    erdos377Mass_le_uniformEntrance_add_preterminalVariation

/-- Unconditional global reduction after the complete harmonic split.  The carrier geometry,
survivor sampling, and integer-clock curvature now appear as three separate ledgers. -/
theorem erdos377Mass_le_uniformEntrance_add_warped_sampling_clock :
    ∃ C : ℝ, ∀ n : ℕ,
      erdos377Mass n ≤ C + preterminalWarpedVariation n +
        (preterminalMellinSamplingAdapterCost n +
          preterminalMellinClockCurvatureCost n) +
        (preterminalMellinSamplingAdapterCost n +
          preterminalMellinClockCurvatureCost n) := by
  rcases erdos377Mass_le_uniformEntrance_add_preterminalMellinVariation with ⟨C, hC⟩
  refine ⟨C, ?_⟩
  intro n
  have hsplit := preterminalMellinVariation_le_warped_add_sampling_add_clock n
  linarith [hC n]

/-- Global reduction with the harmonic carrier, survivor sampling, and integer-floor error all
explicit. -/
theorem erdos377Mass_le_uniformEntrance_add_warped_sampling_continuous_quantization :
    ∃ C : ℝ, ∀ n : ℕ,
      erdos377Mass n ≤ C + preterminalWarpedVariation n +
        (preterminalMellinSamplingAdapterCost n +
          preterminalMellinContinuousClockCurvatureCost n +
            preterminalMellinClockQuantizationCost n) +
        (preterminalMellinSamplingAdapterCost n +
          preterminalMellinContinuousClockCurvatureCost n +
            preterminalMellinClockQuantizationCost n) := by
  rcases erdos377Mass_le_uniformEntrance_add_preterminalMellinVariation with ⟨C, hC⟩
  refine ⟨C, ?_⟩
  intro n
  have hsplit :=
    preterminalMellinVariation_le_warped_add_sampling_continuous_quantization n
  linarith [hC n]

/-- Global reduction after the continuous Mellin clock has been bounded absolutely.  The three
remaining finite ledgers are the raw warped second differences, survivor-sampling variation, and
integer-floor quantization. -/
theorem erdos377Mass_le_uniform_add_warped_sampling_quantization :
    ∃ C : ℝ, ∀ n : ℕ,
      erdos377Mass n ≤ C + preterminalWarpedVariation n +
        (preterminalMellinSamplingAdapterCost n +
          preterminalMellinClockQuantizationCost n) +
        (preterminalMellinSamplingAdapterCost n +
          preterminalMellinClockQuantizationCost n) := by
  rcases erdos377Mass_le_uniformEntrance_add_preterminalMellinVariation with ⟨C, hC⟩
  let K := ((2 + 3 * (2 * Real.log 4 + 2)) / Real.log 2) * ((1 : ℝ) / 4)
  refine ⟨C + 2 * K, ?_⟩
  intro n
  have hsplit :=
    preterminalMellinVariation_le_uniformClock_add_warped_sampling_quantization n
  dsimp only [K] at hsplit ⊢
  linarith [hC n]

/-- Compact final reduction to the atom-corrected remaining ledger. -/
theorem erdos377Mass_le_uniform_add_preterminalWarpedSamplingQuantization :
    ∃ C : ℝ, ∀ n : ℕ,
      erdos377Mass n ≤ C + preterminalWarpedSamplingQuantizationVariation n := by
  rcases erdos377Mass_le_uniform_add_warped_sampling_quantization with ⟨C, hC⟩
  refine ⟨C, ?_⟩
  intro n
  rw [preterminalWarpedSamplingQuantizationVariation_eq]
  simpa only [add_assoc] using hC n

/-! ## Endgame adapters: necessity, the harmonic capstone, and split unification

Three closures of the reduction architecture.  The atomic budget is *necessary*: any uniform
bound already contains it, so the budget is an invariant of the problem, not of the route.
The harmonic-scale split *suffices*: a harmonic atomic budget plus contraction of the
harmonic-diffuse ledger exports the uniform bound.  And the dispersion certificate makes the
harmonic gate at least as strong as the cardinal one: a harmonic-diffuse band always carries
more rail samples than its depth. -/

/-!
The three compiler-level endgame decompositions tested here begin with:

1. `refine erdos377Bound_of_harmonicAtomic_diffuse_uniform_band (A := 1)
     (ρ := (1 : ℝ) / 2) (B := 1) (H := 2 + (2 * Real.log 4 + 2) * Real.log 2) ...`;
2. `rcases erdos377Mass_le_uniform_add_preterminalWarpedSamplingQuantization with ⟨C, hC⟩`;
3. `rw [compensatedFullyMellinLedger_eq_onePrimeMellinHaarLedger]` inside the exact compensated
   readout.

The first route discharges the raw harmonic envelope below.  Its remaining goals are the atomic
closed-rail budget and diffuse terminal contraction.  The second leaves the sum of the atomic and
diffuse sampling/quantization variations.  The third leaves the one-prime Mellin-Haar compensated
ledger.
-/

/-- Uniform budget requested only from harmonically concentrated closed rails. -/
def HarmonicAtomicRailBudget (B : ℝ) : Prop :=
  ∀ n : ℕ,
    ∑ r ∈ occupiedDepths n, primeHarmonicMass (harmonicAtomicDepthBand n r) ≤ B

/-- Relative contraction requested only on harmonically dispersed raw bands. -/
def HarmonicDiffuseRailContractionAt (A ρ : ℝ) : Prop :=
  ∀ n r : ℕ,
    primeHarmonicMass (harmonicDiffuseDepthBand n r) ≤
      A * ρ ^ r * primeHarmonicMass (harmonicDiffuseRailBand n r)

/-- Uniform prime-harmonic mass bound for each harmonically dispersed raw band. -/
def UniformHarmonicDiffuseRailBandEnvelope (H : ℝ) : Prop :=
  ∀ n r : ℕ, primeHarmonicMass (harmonicDiffuseRailBand n r) ≤ H

/-- A nonempty raw depth rail has positive logarithmic depth, without requiring a closed rail. -/
theorem railBand_depth_pos_of_nonempty {n r : ℕ} (hne : (railBand n r).Nonempty) :
    0 < r := by
  rcases hne with ⟨p, hp⟩
  have hpLE : p ∈ n.primesLE := (mem_filter.mp hp).1
  have hpPrime : p.Prime := Nat.prime_of_mem_primesLE hpLE
  have hpos : 0 < railDepth p n := by
    simpa [railDepth] using
      Nat.log_pos hpPrime.one_lt (Nat.le_of_mem_primesLE hpLE)
  simpa [(mem_filter.mp hp).2] using hpos

/-- Prime harmonic mass is monotone when the prime bank is restricted. -/
theorem primeHarmonicMass_mono {s t : Finset ℕ} (hst : s ⊆ t) :
    primeHarmonicMass s ≤ primeHarmonicMass t := by
  rw [primeHarmonicMass, primeHarmonicMass]
  exact Finset.sum_le_sum_of_subset_of_nonneg hst (fun p _ _ ↦ by positivity)

/-- The diffuse raw carrier already has the uniform logarithmic-band envelope required by the
endgame adapter. -/
theorem uniformHarmonicDiffuseRailBandEnvelope :
    UniformHarmonicDiffuseRailBandEnvelope
      (2 + (2 * Real.log 4 + 2) * Real.log 2) := by
  intro n r
  by_cases hs : (harmonicDiffuseRailBand n r).Nonempty
  · have hrail : (railBand n r).Nonempty :=
      hs.mono (harmonicDiffuseRailBand_subset_railBand n r)
    exact (primeHarmonicMass_mono
      (harmonicDiffuseRailBand_subset_railBand n r)).trans
        (primeHarmonicMass_railBand_le_uniform
          (railBand_depth_pos_of_nonempty hrail))
  · rw [not_nonempty_iff_eq_empty.mp hs, primeHarmonicMass]
    positivity

/-- A harmonic-diffuse band has more rail samples than its depth: summing the dispersion
certificate over the band forces `r < card`.  The harmonic gate is therefore at least as
strong a classifier as the cardinal one. -/
theorem harmonicDiffuse_depth_lt_card {n r : ℕ}
    (hne : (harmonicDiffuseRailBand n r).Nonempty) :
    r < (harmonicDiffuseRailBand n r).card := by
  classical
  have hmasspos : 0 < primeHarmonicMass (harmonicDiffuseRailBand n r) := by
    rw [primeHarmonicMass]
    refine Finset.sum_pos (fun p hp ↦ ?_) hne
    have hprime : p.Prime := Nat.prime_of_mem_primesLE
      (railBand_subset_primesLE n r (harmonicDiffuseRailBand_subset_railBand n r hp))
    have hpos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hprime.pos
    positivity
  have hmul : (r : ℝ) * primeHarmonicMass (harmonicDiffuseRailBand n r) <
      ((harmonicDiffuseRailBand n r).card : ℝ) *
        primeHarmonicMass (harmonicDiffuseRailBand n r) := by
    calc
      (r : ℝ) * primeHarmonicMass (harmonicDiffuseRailBand n r) =
          ∑ p ∈ harmonicDiffuseRailBand n r, (r : ℝ) * ((1 : ℝ) / (p : ℝ)) := by
        rw [primeHarmonicMass, Finset.mul_sum]
      _ < ∑ p ∈ harmonicDiffuseRailBand n r,
            primeHarmonicMass (harmonicDiffuseRailBand n r) :=
        Finset.sum_lt_sum_of_nonempty hne
          (fun p hp ↦ harmonicDiffuse_atom_lt_bandMass hp)
      _ = ((harmonicDiffuseRailBand n r).card : ℝ) *
            primeHarmonicMass (harmonicDiffuseRailBand n r) := by
        rw [Finset.sum_const, nsmul_eq_mul]
  exact_mod_cast lt_of_mul_lt_mul_right hmul hmasspos.le

/-- Export adapter on the harmonic-scale split: a harmonic atomic budget plus contraction of
the harmonic-diffuse ledger yields the uniform Erdős-377 bound, with the geometric series
discharging the envelope. -/
theorem erdos377Bound_of_harmonicAtomic_diffuse_uniform_band {A ρ B H : ℝ}
    (hA : 0 ≤ A) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (hH : 0 ≤ H)
    (hatomic : HarmonicAtomicRailBudget B)
    (hcontract : HarmonicDiffuseRailContractionAt A ρ)
    (hband : UniformHarmonicDiffuseRailBandEnvelope H) :
    Erdos377Bound := by
  refine ⟨B + A * H * (1 - ρ)⁻¹, fun n ↦ ?_⟩
  have hsummable : Summable (fun r : ℕ ↦ ρ ^ r) :=
    summable_geometric_of_lt_one hρ0 hρ1
  have hfinite : ∑ r ∈ occupiedDepths n, ρ ^ r ≤ ∑' r : ℕ, ρ ^ r :=
    hsummable.sum_le_tsum (occupiedDepths n) (fun r _ ↦ pow_nonneg hρ0 r)
  rw [erdos377Mass_eq_sum_depthBandMass]
  calc
    ∑ r ∈ occupiedDepths n, primeHarmonicMass (depthBand n r) =
        ∑ r ∈ occupiedDepths n,
          (primeHarmonicMass (harmonicAtomicDepthBand n r) +
            primeHarmonicMass (harmonicDiffuseDepthBand n r)) :=
      sum_congr rfl fun r _ ↦
        primeHarmonicMass_depthBand_eq_harmonicAtomic_add_diffuse n r
    _ = (∑ r ∈ occupiedDepths n, primeHarmonicMass (harmonicAtomicDepthBand n r)) +
        ∑ r ∈ occupiedDepths n, primeHarmonicMass (harmonicDiffuseDepthBand n r) := by
      rw [sum_add_distrib]
    _ ≤ B + ∑ r ∈ occupiedDepths n, A * ρ ^ r * H := by
      refine add_le_add (hatomic n) (sum_le_sum fun r _ ↦ ?_)
      calc
        primeHarmonicMass (harmonicDiffuseDepthBand n r) ≤
            A * ρ ^ r * primeHarmonicMass (harmonicDiffuseRailBand n r) :=
          hcontract n r
        _ ≤ A * ρ ^ r * H :=
          mul_le_mul_of_nonneg_left (hband n r)
            (mul_nonneg hA (pow_nonneg hρ0 r))
    _ = B + A * H * ∑ r ∈ occupiedDepths n, ρ ^ r := by
      rw [Finset.mul_sum]
      congr 1
      exact sum_congr rfl fun r _ ↦ by ring
    _ ≤ B + A * H * (1 - ρ)⁻¹ := by
      have hmul := mul_le_mul_of_nonneg_left hfinite (mul_nonneg hA hH)
      rw [tsum_geometric_of_lt_one hρ0 hρ1] at hmul
      linarith

/-- Necessity of the atomic budget: any uniform bound already bounds the atomic ledger.  The
budget hypothesis is an invariant of the problem, not an artifact of the split route. -/
theorem atomicRailBudget_of_erdos377Bound (h : Erdos377Bound) :
    ∃ B : ℝ, AtomicRailBudget B := by
  classical
  obtain ⟨C, hC⟩ := h
  refine ⟨C, fun n ↦ ?_⟩
  have hterm : ∀ r ∈ occupiedDepths n,
      primeHarmonicMass (atomicDepthBand n r) ≤
        primeHarmonicMass (depthBand n r) := by
    intro r _
    by_cases hA : IsAtomicRailBand n r
    · simp [atomicDepthBand, hA]
    · have hzero : atomicDepthBand n r = (∅ : Finset ℕ) := by
        simp [atomicDepthBand, hA]
      rw [hzero, primeHarmonicMass, primeHarmonicMass]
      simp only [Finset.sum_empty]
      exact Finset.sum_nonneg fun p _ ↦ by positivity
  calc
    ∑ r ∈ occupiedDepths n, primeHarmonicMass (atomicDepthBand n r) ≤
        ∑ r ∈ occupiedDepths n, primeHarmonicMass (depthBand n r) :=
      Finset.sum_le_sum hterm
    _ = erdos377Mass n := (erdos377Mass_eq_sum_depthBandMass n).symm
    _ ≤ C := hC n

/-- Necessity on the harmonic scale: the harmonic atomic budget is likewise forced by any
uniform bound. -/
theorem harmonicAtomicRailBudget_of_erdos377Bound (h : Erdos377Bound) :
    ∃ B : ℝ, HarmonicAtomicRailBudget B := by
  classical
  obtain ⟨C, hC⟩ := h
  refine ⟨C, fun n ↦ ?_⟩
  have hterm : ∀ r ∈ occupiedDepths n,
      primeHarmonicMass (harmonicAtomicDepthBand n r) ≤
        primeHarmonicMass (depthBand n r) := by
    intro r _
    by_cases hA : IsHarmonicAtomicRailBand n r
    · simp [harmonicAtomicDepthBand, hA]
    · have hzero : harmonicAtomicDepthBand n r = (∅ : Finset ℕ) := by
        simp [harmonicAtomicDepthBand, hA]
      rw [hzero, primeHarmonicMass, primeHarmonicMass]
      simp only [Finset.sum_empty]
      exact Finset.sum_nonneg fun p _ ↦ by positivity
  calc
    ∑ r ∈ occupiedDepths n, primeHarmonicMass (harmonicAtomicDepthBand n r) ≤
        ∑ r ∈ occupiedDepths n, primeHarmonicMass (depthBand n r) :=
      Finset.sum_le_sum hterm
    _ = erdos377Mass n := (erdos377Mass_eq_sum_depthBandMass n).symm
    _ ≤ C := hC n

/-! ## Carry-mass conservation and the archimedean obstruction

Two structural facts about the whole rail bank at once.

First, a conservation law: the `log p`-weighted total of all carry events across every rail
equals `log ((2n).choose n)` exactly, and the elementary central-binomial bounds pin that
total inside a window of width `log (2n)` around `2n log 2`.  Every balanced rail withdraws
its entire carry tower from a ledger whose total is fixed: dodged carry mass at some scales
must be repaid at others, deterministically, at every `n`.  This is the integrated
registration bound of the digit fiber, closed unconditionally.

Second, the obstruction: any finite-depth balance pattern on any finite rail set is realized
by integers beyond any bound, so congruence data alone can never bound the balanced mass.
The only coupling among rails is the archimedean size of `n`, and the conservation law above
is the identity that sees it. -/

/-- The `log p`-weighted carry ledger summed over all rails is exactly `log ((2n).choose n)`. -/
theorem carryLedger_weighted_sum_eq_log_centralBinom {n : ℕ} (hn : 0 < n) :
    ∑ p ∈ (2 * n).primesLE,
        ((carryLedger p n (carryCutoff p n)).card : ℝ) * Real.log p =
      Real.log ((2 * n).choose n : ℝ) := by
  classical
  have hC0 : (2 * n).choose n ≠ 0 := (Nat.choose_pos (by omega)).ne'
  have hCdvd : (2 * n).choose n ∣ Nat.factorial (2 * n) := by
    have h := Nat.choose_mul_factorial_mul_factorial (show n ≤ 2 * n by omega)
    exact ⟨Nat.factorial n * Nat.factorial (2 * n - n), by rw [← h]; ring⟩
  have hsub : ((2 * n).choose n).primeFactors ⊆ (2 * n).primesLE := by
    intro p hp
    obtain ⟨hprime, hpdvd, -⟩ := Nat.mem_primeFactors.mp hp
    have hple : p ≤ 2 * n := (Nat.Prime.dvd_factorial hprime).mp (hpdvd.trans hCdvd)
    exact Nat.mem_primesLE.mpr ⟨hple, hprime⟩
  have hprodN : (∏ p ∈ ((2 * n).choose n).primeFactors,
      p ^ ((2 * n).choose n).factorization p) = (2 * n).choose n := by
    rw [← Nat.prod_factorization_eq_prod_primeFactors]
    exact Nat.prod_factorization_pow_eq_self hC0
  have hne : ∀ p ∈ ((2 * n).choose n).primeFactors,
      ((p : ℝ) ^ ((2 * n).choose n).factorization p) ≠ 0 := by
    intro p hp
    have hprime := Nat.prime_of_mem_primeFactors hp
    have hppos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hprime.pos
    positivity
  have hlog : Real.log ((2 * n).choose n : ℝ) =
      ∑ p ∈ ((2 * n).choose n).primeFactors,
        (((2 * n).choose n).factorization p : ℝ) * Real.log p := by
    have hcast : ((2 * n).choose n : ℝ) =
        ∏ p ∈ ((2 * n).choose n).primeFactors,
          (p : ℝ) ^ ((2 * n).choose n).factorization p := by
      exact_mod_cast hprodN.symm
    rw [hcast, Real.log_prod hne]
    exact Finset.sum_congr rfl fun p _ ↦ Real.log_pow _ _
  calc
    ∑ p ∈ (2 * n).primesLE,
        ((carryLedger p n (carryCutoff p n)).card : ℝ) * Real.log p =
        ∑ p ∈ (2 * n).primesLE,
          ((((2 * n).choose n).factorization p : ℝ)) * Real.log p := by
      refine Finset.sum_congr rfl fun p hp ↦ ?_
      rw [carryCutoff, centralBinom_factorization_eq_carryLedger_card
        (Nat.prime_of_mem_primesLE hp) (Nat.lt_add_one _)]
    _ = ∑ p ∈ ((2 * n).choose n).primeFactors,
          ((((2 * n).choose n).factorization p : ℝ)) * Real.log p := by
      symm
      refine Finset.sum_subset hsub fun p _ hnot ↦ ?_
      have hzero : ((2 * n).choose n).factorization p = 0 := by
        by_contra hne0
        have hmem : p ∈ ((2 * n).choose n).factorization.support :=
          Finsupp.mem_support_iff.mpr hne0
        rw [Nat.support_factorization] at hmem
        exact hnot hmem
      simp [hzero]
    _ = Real.log ((2 * n).choose n : ℝ) := hlog.symm

/-- Upper half of the Stirling window, from the elementary bound `C(2n,n) ≤ 4^n`. -/
theorem log_centralBinom_le (n : ℕ) :
    Real.log ((2 * n).choose n : ℝ) ≤ 2 * (n : ℝ) * Real.log 2 := by
  have hb : (2 * n).choose n ≤ 4 ^ n := by
    rw [← Nat.centralBinom_eq_two_mul_choose]
    exact Nat.centralBinom_le_four_pow n
  have hpos : (0 : ℝ) < ((2 * n).choose n : ℝ) := by
    exact_mod_cast Nat.choose_pos (show n ≤ 2 * n by omega)
  have hb' : ((2 * n).choose n : ℝ) ≤ (4 : ℝ) ^ n := by exact_mod_cast hb
  calc
    Real.log ((2 * n).choose n : ℝ) ≤ Real.log ((4 : ℝ) ^ n) :=
      Real.log_le_log hpos hb'
    _ = n * Real.log 4 := Real.log_pow _ _
    _ = 2 * (n : ℝ) * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
      push_cast
      ring

/-- Lower half of the Stirling window, from Erdős's bound `4^n ≤ 2n · C(2n,n)`. -/
theorem two_mul_log_two_sub_le_log_centralBinom {n : ℕ} (hn : 0 < n) :
    2 * (n : ℝ) * Real.log 2 - Real.log (2 * (n : ℝ)) ≤
      Real.log ((2 * n).choose n : ℝ) := by
  have hb : 4 ^ n ≤ 2 * n * ((2 * n).choose n) := by
    rw [← Nat.centralBinom_eq_two_mul_choose]
    exact Nat.four_pow_le_two_mul_self_mul_centralBinom n hn
  have hCpos : (0 : ℝ) < ((2 * n).choose n : ℝ) := by
    exact_mod_cast Nat.choose_pos (show n ≤ 2 * n by omega)
  have h2npos : (0 : ℝ) < 2 * (n : ℝ) := by
    have : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    linarith
  have hb' : (4 : ℝ) ^ n ≤ (2 * (n : ℝ)) * ((2 * n).choose n : ℝ) := by
    exact_mod_cast hb
  have h1 : Real.log ((4 : ℝ) ^ n) ≤
      Real.log ((2 * (n : ℝ)) * ((2 * n).choose n : ℝ)) :=
    Real.log_le_log (by positivity) hb'
  rw [Real.log_pow, Real.log_mul h2npos.ne' hCpos.ne'] at h1
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  rw [hlog4] at h1
  linarith

/-- **Carry-mass conservation law.**  The `log p`-weighted total of all carry events across
every rail is pinned inside a window of width `log (2n)` around `2n log 2`, at every `n`.
A balanced rail contributes zero to a fixed total, so its dodged carry tower is repaid at
other scales exactly.  This is the integrated registration bound of the digit fiber, closed
unconditionally by elementary central-binomial estimates. -/
theorem carry_conservation_law {n : ℕ} (hn : 0 < n) :
    2 * (n : ℝ) * Real.log 2 - Real.log (2 * (n : ℝ)) ≤
        ∑ p ∈ (2 * n).primesLE,
          ((carryLedger p n (carryCutoff p n)).card : ℝ) * Real.log p ∧
      ∑ p ∈ (2 * n).primesLE,
          ((carryLedger p n (carryCutoff p n)).card : ℝ) * Real.log p ≤
        2 * (n : ℝ) * Real.log 2 := by
  rw [carryLedger_weighted_sum_eq_log_centralBinom hn]
  exact ⟨two_mul_log_two_sub_le_log_centralBinom hn, log_centralBinom_le n⟩

/-- **Archimedean obstruction.**  Any finite-depth balance pattern on any finite rail set is
realized by integers beyond any bound (witnessed by the all-zero digit pattern), so no
congruence information alone can bound the balanced mass.  The coupling among rails that a
budget proof must use is the archimedean size of `n`, whose exact ledger is the conservation
law above. -/
theorem carryFreeThrough_realizable {S : Finset ℕ} (hS : ∀ p ∈ S, 0 < p)
    (k : ℕ → ℕ) (N : ℕ) :
    ∃ m : ℕ, N < m ∧ ∀ p ∈ S, CarryFreeThrough p m (k p) := by
  classical
  refine ⟨(N + 1) * ∏ p ∈ S, p ^ k p, ?_, ?_⟩
  · have hprod : 0 < ∏ p ∈ S, p ^ k p :=
      Finset.prod_pos fun p hp ↦ pow_pos (hS p hp) _
    have hle := Nat.le_mul_of_pos_right (N + 1) hprod
    omega
  · intro p hp i hi
    obtain ⟨hi1, hi2⟩ := Finset.mem_Ico.mp hi
    have hdvd : p ^ i ∣ (N + 1) * ∏ q ∈ S, q ^ k q := by
      refine Dvd.dvd.mul_left ?_ (N + 1)
      exact (pow_dvd_pow p (by omega : i ≤ k p)).trans
        (Finset.dvd_prod_of_mem _ hp)
    rw [Nat.mod_eq_zero_of_dvd hdvd, Nat.mul_zero]
    exact pow_pos (hS p hp) i

/-! ## The harmonized conservation law: level split and band spectrometry

The global carry ledger mixes every rung of the refinement ladder into one total, and the
`n`-scale part of that total is pure chart geometry: a level-one carry at rail `p` happens
exactly when `p` lies in a hyperbola band `(n/(k+1), 2n/(2k+1)]`.  Splitting the ledger by
level and evaluating level one as exact Chebyshev-mass differences over the bands leaves the
deep ledger — the only part with digit-tower content — pinned at `√(2n)` scale.  Each rung
is read in its own chart; no rung can hide another rung's slack. -/

/-- Rails whose level-one cell carries: the chart-geometric part of the ledger. -/
noncomputable def levelOneCarryPrimes (n : ℕ) : Finset ℕ := by
  classical
  exact (2 * n).primesLE.filter fun p ↦ p ≤ 2 * (n % p)

/-- Chebyshev-type prime log mass, `θ` restricted to the integers. -/
noncomputable def primeLogMass (m : ℕ) : ℝ :=
  ∑ p ∈ m.primesLE, Real.log p

/-- Level-one carry mass. -/
noncomputable def levelOneCarryMass (n : ℕ) : ℝ :=
  ∑ p ∈ levelOneCarryPrimes n, Real.log p

/-- Deep carry ledger of one rail: levels `2` through the cutoff. -/
noncomputable def deepCarryLedger (p n : ℕ) : Finset ℕ := by
  classical
  exact (Ico 2 (carryCutoff p n)).filter (carryAt p n)

/-- Deep (level `≥ 2`) carry mass: the digit-tower part of the ledger. -/
noncomputable def deepCarryMass (n : ℕ) : ℝ :=
  ∑ p ∈ (2 * n).primesLE, ((deepCarryLedger p n).card : ℝ) * Real.log p

/-- The carry ledger splits into its level-one bit and its deep tail. -/
theorem carryLedger_card_split {p n : ℕ} (hp : p.Prime) (hple : p ≤ 2 * n) :
    (carryLedger p n (carryCutoff p n)).card =
      (if p ≤ 2 * (n % p) then 1 else 0) + (deepCarryLedger p n).card := by
  classical
  have hb : 2 ≤ carryCutoff p n := by
    have hpos : 0 < Nat.log p (2 * n) := Nat.log_pos hp.one_lt hple
    rw [carryCutoff]
    omega
  have hsplit : Ico 1 (carryCutoff p n) = Ico 1 2 ∪ Ico 2 (carryCutoff p n) :=
    (Finset.Ico_union_Ico_eq_Ico (by omega) hb).symm
  simp only [carryLedger, deepCarryLedger]
  rw [hsplit, Finset.filter_union, Finset.card_union_of_disjoint
    (Finset.disjoint_filter_filter (Finset.Ico_disjoint_Ico_consecutive 1 2 _))]
  congr 1
  rw [Nat.Ico_succ_singleton, Finset.filter_singleton]
  by_cases hc : carryAt p n 1
  · rw [if_pos hc, Finset.card_singleton,
      if_pos (by simpa [carryAt, pow_one] using hc)]
  · rw [if_neg hc, Finset.card_empty,
      if_neg (by simpa [carryAt, pow_one] using hc)]

/-- Level split of the conservation law. -/
theorem levelOne_add_deep_eq_log_centralBinom {n : ℕ} (hn : 0 < n) :
    levelOneCarryMass n + deepCarryMass n = Real.log ((2 * n).choose n : ℝ) := by
  classical
  rw [← carryLedger_weighted_sum_eq_log_centralBinom hn, levelOneCarryMass,
    levelOneCarryPrimes, Finset.sum_filter, deepCarryMass, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun p hp ↦ ?_
  have hprime := Nat.prime_of_mem_primesLE hp
  have hple : p ≤ 2 * n := (Nat.mem_primesLE.mp hp).1
  rw [carryLedger_card_split hprime hple]
  push_cast
  by_cases hc : p ≤ 2 * (n % p)
  · simp only [if_pos hc]
    ring
  · simp only [if_neg hc]
    ring

/-- `primesLE` is monotone. -/
theorem primesLE_mono {a b : ℕ} (hab : a ≤ b) : a.primesLE ⊆ b.primesLE := by
  intro p hp
  rw [Nat.mem_primesLE] at hp ⊢
  exact ⟨hp.1.trans hab, hp.2⟩

/-- Fiberwise band law: within quotient fiber `k`, the level-one carrying rails are exactly
the primes of the hyperbola band `(n/(k+1), 2n/(2k+1)]`. -/
theorem levelOneCarryPrimes_filter_eq_sdiff (n k : ℕ) :
    (levelOneCarryPrimes n).filter (fun p ↦ n / p = k) =
      (2 * n / (2 * k + 1)).primesLE \ (n / (k + 1)).primesLE := by
  classical
  ext p
  simp only [levelOneCarryPrimes, Finset.mem_filter, Finset.mem_sdiff,
    Nat.mem_primesLE, not_and]
  constructor
  · rintro ⟨⟨⟨hple, hprime⟩, hcarry⟩, hquot⟩
    have hppos : 0 < p := hprime.pos
    have hdm := Nat.div_add_mod n p
    rw [hquot] at hdm
    have hring1 : p * (2 * k + 1) = 2 * (p * k) + p := by ring
    have hmodlt : n % p < p := Nat.mod_lt _ hppos
    refine ⟨⟨?_, hprime⟩, fun hle ↦ ?_⟩
    · rw [Nat.le_div_iff_mul_le (by omega : 0 < 2 * k + 1)]
      omega
    · exfalso
      have hlt : n / (k + 1) < p := by
        rw [Nat.div_lt_iff_lt_mul (by omega : 0 < k + 1)]
        have hring2 : p * (k + 1) = p * k + p := by ring
        omega
      omega
  · rintro ⟨⟨hple1, hprime⟩, hnot⟩
    have hppos : 0 < p := hprime.pos
    have hgt : n / (k + 1) < p := by
      by_contra hle
      exact hnot (not_lt.mp hle) hprime
    have hmul1 : p * (2 * k + 1) ≤ 2 * n := by
      rwa [Nat.le_div_iff_mul_le (by omega : 0 < 2 * k + 1)] at hple1
    have hmul2 : n < p * (k + 1) := by
      rwa [Nat.div_lt_iff_lt_mul (by omega : 0 < k + 1)] at hgt
    have hring1 : p * (2 * k + 1) = 2 * (p * k) + p := by ring
    have hring2 : p * (k + 1) = p * k + p := by ring
    have hdiv : n / p = k := by
      apply Nat.div_eq_of_lt_le
      · have hcomm : k * p = p * k := by ring
        omega
      · have hcomm : (k + 1) * p = p * k + p := by ring
        omega
    have hdm := Nat.div_add_mod n p
    rw [hdiv] at hdm
    exact ⟨⟨⟨by omega, hprime⟩, by omega⟩, hdiv⟩

/-- Level one evaluated exactly: the band spectrometer formula.  Chebyshev mass differences
over the hyperbola bands, one term per quotient fiber, no estimate anywhere. -/
theorem levelOneCarryMass_eq_band_sum (n : ℕ) :
    levelOneCarryMass n =
      ∑ k ∈ range (n + 1),
        (primeLogMass (2 * n / (2 * k + 1)) - primeLogMass (n / (k + 1))) := by
  classical
  rw [levelOneCarryMass, ← Finset.sum_fiberwise_of_maps_to
    (g := fun p ↦ n / p) (t := range (n + 1))
    (fun p _ ↦ Finset.mem_range.mpr
      (lt_of_le_of_lt (Nat.div_le_self n p) (Nat.lt_succ_self n)))
    (fun p ↦ Real.log p)]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  have hsub : (n / (k + 1)).primesLE ⊆ (2 * n / (2 * k + 1)).primesLE := by
    apply primesLE_mono
    rw [Nat.le_div_iff_mul_le (by omega : 0 < 2 * k + 1)]
    have h1 := Nat.div_mul_le_self n (k + 1)
    have h2 : n / (k + 1) * (2 * k + 1) ≤ n / (k + 1) * (2 * k + 2) :=
      Nat.mul_le_mul_left _ (by omega)
    have h3 : n / (k + 1) * (2 * k + 2) = 2 * (n / (k + 1) * (k + 1)) := by ring
    omega
  rw [levelOneCarryPrimes_filter_eq_sdiff n k, Finset.sum_sdiff_eq_sub hsub]
  simp only [primeLogMass]

/-- The deep ledger is nonnegative. -/
theorem deepCarryMass_nonneg (n : ℕ) : 0 ≤ deepCarryMass n := by
  classical
  rw [deepCarryMass]
  refine Finset.sum_nonneg fun p hp ↦ ?_
  have hprime := Nat.prime_of_mem_primesLE hp
  have h1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hprime.one_lt.le
  exact mul_nonneg (by positivity) (Real.log_nonneg h1)

/-- **Deep pinning.**  The digit-tower ledger lives entirely below `√(2n)` and is bounded by
`√(2n) · log₂(2n) · log(2n)`: after the level-one chart geometry is subtracted, the entire
battlefield of the balanced-rail problem sits inside a `√n`-scale window. -/
theorem deepCarryMass_le_sqrt_bound {n : ℕ} (hn : 0 < n) :
    deepCarryMass n ≤
      (Nat.sqrt (2 * n) : ℝ) * (Nat.log 2 (2 * n) : ℝ) * Real.log (2 * (n : ℝ)) := by
  classical
  have hlog2n : (0 : ℝ) ≤ Real.log (2 * (n : ℝ)) := by
    apply Real.log_nonneg
    have : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  rw [deepCarryMass]
  have hstep : ∀ p ∈ (2 * n).primesLE,
      ((deepCarryLedger p n).card : ℝ) * Real.log p ≠ 0 →
        p ≤ Nat.sqrt (2 * n) := by
    intro p hp hne
    have hcard : (deepCarryLedger p n).Nonempty := by
      by_contra hemp
      rw [Finset.not_nonempty_iff_eq_empty] at hemp
      simp [hemp] at hne
    obtain ⟨i, hi⟩ := hcard
    simp only [deepCarryLedger, Finset.mem_filter, Finset.mem_Ico] at hi
    obtain ⟨⟨hi2, -⟩, hcarry⟩ := hi
    have hprime := Nat.prime_of_mem_primesLE hp
    have hple : p ^ i ≤ 2 * n := by
      have h2 : n % p ^ i ≤ n := Nat.mod_le _ _
      have h1 : p ^ i ≤ 2 * (n % p ^ i) := hcarry
      omega
    refine Nat.le_sqrt.mpr ?_
    calc
      p * p = p ^ 2 := by ring
      _ ≤ p ^ i := Nat.pow_le_pow_right hprime.one_lt.le hi2
      _ ≤ 2 * n := hple
  rw [← Finset.sum_filter_of_ne hstep]
  have hbound : ∀ p ∈ (2 * n).primesLE.filter (fun p ↦ p ≤ Nat.sqrt (2 * n)),
      ((deepCarryLedger p n).card : ℝ) * Real.log p ≤
        (Nat.log 2 (2 * n) : ℝ) * Real.log (2 * (n : ℝ)) := by
    intro p hp
    rw [Finset.mem_filter] at hp
    have hprime := Nat.prime_of_mem_primesLE hp.1
    have hple : p ≤ 2 * n := (Nat.mem_primesLE.mp hp.1).1
    have hcard : (deepCarryLedger p n).card ≤ Nat.log 2 (2 * n) := by
      calc
        (deepCarryLedger p n).card ≤ (Ico 2 (carryCutoff p n)).card := by
          simp only [deepCarryLedger]
          exact Finset.card_filter_le _ _
        _ = carryCutoff p n - 2 := by rw [Nat.card_Ico]
        _ ≤ Nat.log p (2 * n) := by rw [carryCutoff]; omega
        _ ≤ Nat.log 2 (2 * n) := Nat.log_anti_left (by omega) hprime.two_le
    have hppos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hprime.pos
    have hlogp : Real.log p ≤ Real.log (2 * (n : ℝ)) := by
      apply Real.log_le_log hppos
      exact_mod_cast hple
    have hlogp0 : 0 ≤ Real.log (p : ℝ) :=
      Real.log_nonneg (by exact_mod_cast hprime.one_lt.le)
    calc
      ((deepCarryLedger p n).card : ℝ) * Real.log p ≤
          (Nat.log 2 (2 * n) : ℝ) * Real.log p := by
        apply mul_le_mul_of_nonneg_right _ hlogp0
        exact_mod_cast hcard
      _ ≤ (Nat.log 2 (2 * n) : ℝ) * Real.log (2 * (n : ℝ)) :=
        mul_le_mul_of_nonneg_left hlogp (by positivity)
  calc
    ∑ p ∈ (2 * n).primesLE.filter (fun p ↦ p ≤ Nat.sqrt (2 * n)),
        ((deepCarryLedger p n).card : ℝ) * Real.log p ≤
        ((2 * n).primesLE.filter (fun p ↦ p ≤ Nat.sqrt (2 * n))).card •
          ((Nat.log 2 (2 * n) : ℝ) * Real.log (2 * (n : ℝ))) :=
      Finset.sum_le_card_nsmul _ _ _ hbound
    _ ≤ (Nat.sqrt (2 * n) : ℝ) * ((Nat.log 2 (2 * n) : ℝ) * Real.log (2 * (n : ℝ))) := by
      rw [nsmul_eq_mul]
      refine mul_le_mul_of_nonneg_right ?_ (by positivity)
      have hsubset : (2 * n).primesLE.filter (fun p ↦ p ≤ Nat.sqrt (2 * n)) ⊆
          (Nat.sqrt (2 * n)).primesLE := by
        intro p hp
        rw [Finset.mem_filter, Nat.mem_primesLE] at hp
        exact Nat.mem_primesLE.mpr ⟨hp.2, hp.1.2⟩
      have h1 := Finset.card_le_card hsubset
      have h2 : (Nat.sqrt (2 * n)).primesLE.card ≤ Nat.sqrt (2 * n) := by
        rw [Nat.primesLE_card_eq_primeCounting]
        exact primeCounting_le_self _
      exact_mod_cast le_trans h1 h2
    _ = (Nat.sqrt (2 * n) : ℝ) * (Nat.log 2 (2 * n) : ℝ) * Real.log (2 * (n : ℝ)) := by
      ring

/-- **Harmonized conservation law.**  The band-spectrometer reading of level one equals
`log C(2n,n)` minus a deep ledger pinned at `√(2n)` scale.  Each rung of the refinement
ladder is read in its own chart: the `n`-scale slack of the raw conservation law was
level-one chart geometry, and subtracting it exactly leaves the digit-tower content of the
problem inside a `√n`-scale window, at every `n`. -/
theorem harmonized_carry_conservation {n : ℕ} (hn : 0 < n) :
    (∑ k ∈ range (n + 1),
        (primeLogMass (2 * n / (2 * k + 1)) - primeLogMass (n / (k + 1)))) =
      Real.log ((2 * n).choose n : ℝ) - deepCarryMass n ∧
    0 ≤ deepCarryMass n ∧
    deepCarryMass n ≤
      (Nat.sqrt (2 * n) : ℝ) * (Nat.log 2 (2 * n) : ℝ) * Real.log (2 * (n : ℝ)) := by
  refine ⟨?_, deepCarryMass_nonneg n, deepCarryMass_le_sqrt_bound hn⟩
  rw [← levelOneCarryMass_eq_band_sum, ← levelOne_add_deep_eq_log_centralBinom hn]
  ring

/-! ## Iterated band telescoping: the two-level joint fiber

Joint carry conditions at several levels telescope exactly: within a joint quotient fiber,
the rails satisfying prescribed carry patterns at levels one and two form a single difference
of prime tables, with square-root endpoints at the second level.  No estimate occurs: joint
occupancy counts are alternating sums of the prime clock `θ` at explicitly computable
points.  The level-one band law is the one-level case; this is the two-level case, the
induction template for every deeper pattern. -/

/-- Prime tables intersect at the minimum threshold. -/
theorem primesLE_inter_eq_min (a b : ℕ) :
    a.primesLE ∩ b.primesLE = (min a b).primesLE := by
  ext p
  simp only [Finset.mem_inter, Nat.mem_primesLE, le_min_iff]
  tauto

/-- Unconditional telescoped mass of a prime-table difference: empty and nonempty cases in
one formula. -/
theorem primesLE_sdiff_logMass (a b : ℕ) :
    ∑ p ∈ a.primesLE \ b.primesLE, Real.log p =
      primeLogMass a - primeLogMass (min a b) := by
  classical
  rw [← Finset.sdiff_inter_self_left, Finset.sum_sdiff_eq_sub Finset.inter_subset_left,
    primesLE_inter_eq_min]
  rfl

/-- **Two-level joint fiber law.**  Rails carrying at levels one and two with quotients
`(k, m)` are exactly the primes of one interval whose endpoints mix a hyperbola band with
the square root of a hyperbola band. -/
theorem levelTwoJointCarry_fiber_eq_sdiff (n k m : ℕ) :
    ((2 * n).primesLE.filter (fun p ↦
        p ≤ 2 * (n % p) ∧ p ^ 2 ≤ 2 * (n % p ^ 2) ∧ n / p = k ∧ n / p ^ 2 = m)) =
      (min (2 * n / (2 * k + 1)) (Nat.sqrt (2 * n / (2 * m + 1)))).primesLE \
        (max (n / (k + 1)) (Nat.sqrt (n / (m + 1)))).primesLE := by
  ext p
  simp only [Finset.mem_filter, Finset.mem_sdiff, Nat.mem_primesLE, le_min_iff,
    not_and, not_le]
  constructor
  · rintro ⟨⟨hple, hprime⟩, hc1, hc2, hq1, hq2⟩
    have hppos : 0 < p := hprime.pos
    have hsq : p ^ 2 = p * p := by ring
    have hdm1 := Nat.div_add_mod n p
    rw [hq1] at hdm1
    have hdm2 := Nat.div_add_mod n (p ^ 2)
    rw [hq2] at hdm2
    have hmodlt1 : n % p < p := Nat.mod_lt _ hppos
    have hmodlt2 : n % p ^ 2 < p ^ 2 := Nat.mod_lt _ (by positivity)
    have hring1 : p * (2 * k + 1) = 2 * (p * k) + p := by ring
    have hring2 : p ^ 2 * (2 * m + 1) = 2 * (p ^ 2 * m) + p ^ 2 := by ring
    refine ⟨⟨⟨?_, ?_⟩, hprime⟩, fun hle1 ↦ ?_⟩
    · rw [Nat.le_div_iff_mul_le (by omega : 0 < 2 * k + 1)]
      omega
    · rw [Nat.le_sqrt]
      rw [Nat.le_div_iff_mul_le (by omega : 0 < 2 * m + 1)]
      have : p * p * (2 * m + 1) = p ^ 2 * (2 * m + 1) := by ring
      omega
    · exfalso
      have hlt1 : n / (k + 1) < p := by
        rw [Nat.div_lt_iff_lt_mul (by omega : 0 < k + 1)]
        have : p * (k + 1) = p * k + p := by ring
        omega
      have hlt2 : Nat.sqrt (n / (m + 1)) < p := by
        rw [← not_le, Nat.le_sqrt]
        intro hcon
        rw [Nat.le_div_iff_mul_le (by omega : 0 < m + 1)] at hcon
        have : p * p * (m + 1) = p ^ 2 * m + p ^ 2 := by ring
        omega
      have := max_lt hlt1 hlt2
      omega
  · rintro ⟨⟨⟨hhi1, hhi2⟩, hprime⟩, hlo⟩
    have hppos : 0 < p := hprime.pos
    have hgt : max (n / (k + 1)) (Nat.sqrt (n / (m + 1))) < p := by
      by_contra hle
      exact absurd hprime (hlo (le_of_not_gt hle))
    have hgt1 : n / (k + 1) < p := lt_of_le_of_lt (le_max_left _ _) hgt
    have hgt2 : Nat.sqrt (n / (m + 1)) < p := lt_of_le_of_lt (le_max_right _ _) hgt
    have hmul1 : p * (2 * k + 1) ≤ 2 * n := by
      rwa [Nat.le_div_iff_mul_le (by omega : 0 < 2 * k + 1)] at hhi1
    have hmul2 : p * p * (2 * m + 1) ≤ 2 * n := by
      rw [Nat.le_sqrt] at hhi2
      rwa [Nat.le_div_iff_mul_le (by omega : 0 < 2 * m + 1)] at hhi2
    have hup1 : n < p * (k + 1) := by
      rwa [Nat.div_lt_iff_lt_mul (by omega : 0 < k + 1)] at hgt1
    have hup2 : n < p * p * (m + 1) := by
      have h := hgt2
      rw [← not_le, Nat.le_sqrt, not_le] at h
      have hQ := Nat.div_add_mod n (m + 1)
      have hmod : n % (m + 1) < m + 1 := Nat.mod_lt _ (by omega)
      have hmono : (n / (m + 1) + 1) * (m + 1) ≤ p * p * (m + 1) :=
        Nat.mul_le_mul_right _ (by omega : n / (m + 1) + 1 ≤ p * p)
      have hexp : (n / (m + 1) + 1) * (m + 1) = (m + 1) * (n / (m + 1)) + (m + 1) := by
        ring
      omega
    have hring1 : p * (2 * k + 1) = 2 * (p * k) + p := by ring
    have hring1b : p * (k + 1) = p * k + p := by ring
    have hring2 : p * p * (2 * m + 1) = 2 * (p * p * m) + p * p := by ring
    have hring2b : p * p * (m + 1) = p * p * m + p * p := by ring
    have hdiv1 : n / p = k := by
      apply Nat.div_eq_of_lt_le
      · have : k * p = p * k := by ring
        omega
      · have : (k + 1) * p = p * k + p := by ring
        omega
    have hdiv2 : n / p ^ 2 = m := by
      have hsq : p ^ 2 = p * p := by ring
      rw [hsq]
      apply Nat.div_eq_of_lt_le
      · have : m * (p * p) = p * p * m := by ring
        omega
      · have : (m + 1) * (p * p) = p * p * m + p * p := by ring
        omega
    have hdm1 := Nat.div_add_mod n p
    rw [hdiv1] at hdm1
    have hdm2 := Nat.div_add_mod n (p ^ 2)
    rw [hdiv2] at hdm2
    have hsq : p ^ 2 = p * p := by ring
    have hsqm : p ^ 2 * m = p * p * m := by ring
    refine ⟨⟨by omega, hprime⟩, by omega, by omega, hdiv1, hdiv2⟩

/-- Two-level joint occupancy as an exact `θ`-difference: the `J = 2` rung of iterated band
telescoping.  Joint carry counts need no equidistribution estimate — they are alternating
sums of the prime clock at computable points. -/
theorem levelTwoJointCarry_fiber_logMass (n k m : ℕ) :
    ∑ p ∈ (2 * n).primesLE.filter (fun p ↦
        p ≤ 2 * (n % p) ∧ p ^ 2 ≤ 2 * (n % p ^ 2) ∧ n / p = k ∧ n / p ^ 2 = m),
      Real.log p =
      primeLogMass (min (2 * n / (2 * k + 1)) (Nat.sqrt (2 * n / (2 * m + 1)))) -
        primeLogMass (min (min (2 * n / (2 * k + 1)) (Nat.sqrt (2 * n / (2 * m + 1))))
          (max (n / (k + 1)) (Nat.sqrt (n / (m + 1))))) := by
  rw [levelTwoJointCarry_fiber_eq_sdiff, primesLE_sdiff_logMass]

end CriticalLinePhasor.Erdos377

#print axioms CriticalLinePhasor.Erdos377.centralBinom_factorization_eq_carryLedger_card
#print axioms CriticalLinePhasor.Erdos377.prime_not_dvd_centralBinom_iff_carryFreeThrough
#print axioms CriticalLinePhasor.Erdos377.prime_dvd_centralBinom_iff_exists_carry
#print axioms CriticalLinePhasor.Erdos377.prime_not_dvd_centralBinom_iff_carryFree
#print axioms CriticalLinePhasor.Erdos377.nondivisorPrimes_eq_carryFreePrimes
#print axioms CriticalLinePhasor.Erdos377.erdos377Mass_eq_carryFreeRailSum
#print axioms CriticalLinePhasor.Erdos377.carryAt_iff_one_le_railPhase
#print axioms CriticalLinePhasor.Erdos377.carryFree_iff_geometric
#print axioms CriticalLinePhasor.Erdos377.erdos377Mass_eq_geometricRailMass
#print axioms CriticalLinePhasor.Erdos377.erdos377Mass_eq_sum_depthBands
#print axioms CriticalLinePhasor.Erdos377.geometric_depth_one_iff
#print axioms CriticalLinePhasor.Erdos377.first_cell_iff_reciprocal_interval
#print axioms CriticalLinePhasor.Erdos377.rpow_normalizedRailFrequency
#print axioms CriticalLinePhasor.Erdos377.halfCell_fourier_expansion
#print axioms CriticalLinePhasor.Erdos377.halfCell_eq_zeroMode_add_nonzeroModes
#print axioms CriticalLinePhasor.Erdos377.carryAcceptance_eq_ite
#print axioms CriticalLinePhasor.Erdos377.harmonicRailTransfer_eq_carryAcceptance
#print axioms CriticalLinePhasor.Erdos377.mod_pow_succ_eq_mod_add_digit_mul_pow
#print axioms CriticalLinePhasor.Erdos377.normalizedCellCoordinate_succ
#print axioms CriticalLinePhasor.Erdos377.normalizedChannelGate_sum
#print axioms CriticalLinePhasor.Erdos377.normalizedChannelAverage_le_two_thirds
#print axioms CriticalLinePhasor.Erdos377.normalizedChannelDiscrepancy_sum_eq_zero
#print axioms CriticalLinePhasor.Erdos377.normalizedChannelDiscrepancy_three_zero
#print axioms CriticalLinePhasor.Erdos377.harmonizedCellPhase_lt_half_iff
#print axioms CriticalLinePhasor.Erdos377.next_harmonizedCell_closed_iff_digit_le_half
#print axioms CriticalLinePhasor.Erdos377.prime_not_dvd_centralBinom_iff_dynamicClosedOrbit
#print axioms CriticalLinePhasor.Erdos377.dynamicSurvivalWeight_eq_ite
#print axioms CriticalLinePhasor.Erdos377.dynamicCellOperator_exact_orbit
#print axioms CriticalLinePhasor.Erdos377.dynamicCellOperator_coherence_le
#print axioms CriticalLinePhasor.Erdos377.dynamicClosureWeight_succ_eq_average_add_discrepancy
#print axioms CriticalLinePhasor.Erdos377.dynamicClosure_mul_channelAverage_le_two_thirds
#print axioms CriticalLinePhasor.Erdos377.dynamicHarmonicEnergy_succ_le_two_thirds_add_discrepancy
#print axioms CriticalLinePhasor.Erdos377.dynamicHarmonicEnergy_succ_le
#print axioms CriticalLinePhasor.Erdos377.dynamicRailMass_eq_erdos377Mass
#print axioms CriticalLinePhasor.Erdos377.carryState_eq_zero_of_increments
#print axioms CriticalLinePhasor.Erdos377.incrementClosedThrough_iff_carryFreeThrough
#print axioms CriticalLinePhasor.Erdos377.carryFree_depth_band_bounds
#print axioms CriticalLinePhasor.Erdos377.activeCarryCells_eq_depth
#print axioms CriticalLinePhasor.Erdos377.erdos377Mass_eq_sum_depthBandMass
#print axioms CriticalLinePhasor.Erdos377.depthBand_harmonicMass_le_railBand
#print axioms CriticalLinePhasor.Erdos377.three_pow_carryFree
#print axioms CriticalLinePhasor.Erdos377.three_pow_dynamicSurvivalWeight_eq_one
#print axioms CriticalLinePhasor.Erdos377.railBand_three_pow
#print axioms CriticalLinePhasor.Erdos377.depthBand_three_pow
#print axioms CriticalLinePhasor.Erdos377.not_uniformRailContraction
#print axioms CriticalLinePhasor.Erdos377.depthBand_eq_atomic_union_diffuse
#print axioms CriticalLinePhasor.Erdos377.primeHarmonicMass_depthBand_eq_atomic_add_diffuse
#print axioms CriticalLinePhasor.Erdos377.atomicDepthBand_three_pow
#print axioms CriticalLinePhasor.Erdos377.diffuseDepthBand_three_pow
#print axioms CriticalLinePhasor.Erdos377.diffuseCarrierEnvelope_of_uniform_band
#print axioms CriticalLinePhasor.Erdos377.erdos377Bound_of_atomic_diffuse
#print axioms CriticalLinePhasor.Erdos377.erdos377Bound_of_atomic_diffuse_uniform_band
#print axioms CriticalLinePhasor.Erdos377.lowerHalfCellGate_eq_half_add_squareSign
#print axioms CriticalLinePhasor.Erdos377.dynamicClosureWeight_succ_eq_half_add_signed
#print axioms CriticalLinePhasor.Erdos377.dynamicBankEnergy_succ_eq_half_add_signed
#print axioms CriticalLinePhasor.Erdos377.halfTransferRecurrence_unroll
#print axioms CriticalLinePhasor.Erdos377.dynamicBankEnergy_eq_vanishingDwell
#print axioms CriticalLinePhasor.Erdos377.railBand_log_two_mul_lt_depth_add_two
#print axioms CriticalLinePhasor.Erdos377.railBand_dynamicClosureWeight_eq_ite
#print axioms CriticalLinePhasor.Erdos377.dynamicBankEnergy_railBand_terminal_eq_depthBandMass
#print axioms CriticalLinePhasor.Erdos377.erdos377Mass_eq_sum_vanishingDwell
#print axioms CriticalLinePhasor.Erdos377.dynamicSquareSign_eq_quotientDigitSign
#print axioms CriticalLinePhasor.Erdos377.quotientContourPacket_eq_lower_union_upper
#print axioms CriticalLinePhasor.Erdos377.quotientContourPacket_signedLedger_eq_sub
#print axioms CriticalLinePhasor.Erdos377.hasDerivAt_quotientContourPhase
#print axioms CriticalLinePhasor.Erdos377.quotientWarpAmplitude_mul_density
#print axioms CriticalLinePhasor.Erdos377.quotientContourPhase_warpedReflection
#print axioms CriticalLinePhasor.Erdos377.quotientContourPhase_eq_quotientDigitPhase
#print axioms CriticalLinePhasor.Erdos377.warpedReflection_involutive
#print axioms CriticalLinePhasor.Erdos377.quotientWarpAmplitude_endpoint_distortion
#print axioms CriticalLinePhasor.Erdos377.quotientCell_endpointRatio_eq
#print axioms CriticalLinePhasor.Erdos377.harmonicContourResidual_nonneg_le
#print axioms CriticalLinePhasor.Erdos377.sum_range_reciprocal_cell_distortion
#print axioms CriticalLinePhasor.Erdos377.sum_range_harmonicContourResidual_le_quarter
#print axioms CriticalLinePhasor.Erdos377.warpedReflection_not_integer_example
#print axioms CriticalLinePhasor.Erdos377.warpedMeshVariation_const_mul
#print axioms CriticalLinePhasor.Erdos377.discreteStieltjesVariationBound
#print axioms CriticalLinePhasor.Erdos377.discreteStieltjes_depth_decay
#print axioms CriticalLinePhasor.Erdos377.sum_depth_stieltjesDiscrepancy_le
#print axioms CriticalLinePhasor.Erdos377.alternatingReciprocalKernel_variation_unbounded
#print axioms CriticalLinePhasor.Erdos377.reflectedResidualKernel_warpedVariation_le_half
#print axioms CriticalLinePhasor.Erdos377.scaled_reflectedResidualKernel_warpedVariation_decay
#print axioms CriticalLinePhasor.Erdos377.norm_reflectedResidualKernel_le_half
#print axioms CriticalLinePhasor.Erdos377.reflectedResidualKernel_stieltjes_depth_decay
#print axioms CriticalLinePhasor.Erdos377.sum_depth_reflectedResidualDiscrepancy_le
#print axioms CriticalLinePhasor.Erdos377.double_div_eq_two_mul_div_add_carryBit
#print axioms CriticalLinePhasor.Erdos377.prime_not_dvd_centralBinom_iff_evenQuotientOrbit
#print axioms CriticalLinePhasor.Erdos377.quotientDigit_lower_iff_midpoint
#print axioms CriticalLinePhasor.Erdos377.lowerReciprocalPrimeCell_eq_sdiff
#print axioms CriticalLinePhasor.Erdos377.upperReciprocalPrimeCell_eq_sdiff
#print axioms CriticalLinePhasor.Erdos377.reciprocalPrimeCell_signedMass_eq_secondDifference
#print axioms CriticalLinePhasor.Erdos377.reciprocalPrimeCell_secondDifference_eq_main_add_error
#print axioms CriticalLinePhasor.Erdos377.firstDigitSignedPrimeLedger_eq_sum_secondDifferences
#print axioms CriticalLinePhasor.Erdos377.firstDigitSignedPrimeLedger_eq_main_add_error
#print axioms CriticalLinePhasor.Erdos377.bankPrimeReciprocalCumulative_sdiff
#print axioms CriticalLinePhasor.Erdos377.bankReciprocalPrimeCell_signedMass_eq_secondDifference
#print axioms CriticalLinePhasor.Erdos377.bankReciprocalPrimeCell_signedLedger_eq_sub
#print axioms CriticalLinePhasor.Erdos377.dynamicBankSignedLedger_eq_survivingQuotientSum
#print axioms CriticalLinePhasor.Erdos377.dynamicPrefixPrimeBank_eq_boundary_add_secondDifferences
#print axioms CriticalLinePhasor.Erdos377.dynamicBankSignedLedger_eq_recursiveWarpedLedger
#print axioms CriticalLinePhasor.Erdos377.railBand_le_quotientPrefix
#print axioms CriticalLinePhasor.Erdos377.railBand_dynamicPrefixBoundaryPrimeBank_eq_empty
#print axioms CriticalLinePhasor.Erdos377.railBand_quotientPrefix_lt_terminal
#print axioms CriticalLinePhasor.Erdos377.railBand_dynamicSquareSign_terminal
#print axioms CriticalLinePhasor.Erdos377.railBand_recursiveWarpedLedger_nonterminal
#print axioms CriticalLinePhasor.Erdos377.railBand_recursiveWarpedLedger_terminal_eq_threshold
#print axioms CriticalLinePhasor.Erdos377.erdos377Mass_eq_sum_recursiveWarpedDwell
#print axioms CriticalLinePhasor.Erdos377.abs_recursiveWarpedLedger_le_boundary_add_variation
#print axioms CriticalLinePhasor.Erdos377.railBand_recursiveWarpedBoundaryMass_nonterminal_eq_zero
#print axioms CriticalLinePhasor.Erdos377.abs_railBand_recursiveWarpedLedger_nonterminal_le_variation
#print axioms CriticalLinePhasor.Erdos377.railBand_nonterminal_dwell_ledger_le_warpedVariation
#print axioms CriticalLinePhasor.Erdos377.depthBand_eq_harmonicAtomic_union_diffuse
#print axioms CriticalLinePhasor.Erdos377.primeHarmonicMass_depthBand_eq_harmonicAtomic_add_diffuse
#print axioms CriticalLinePhasor.Erdos377.harmonicAtomicDepthBand_three_pow
#print axioms CriticalLinePhasor.Erdos377.harmonicDiffuseDepthBand_three_pow
#print axioms CriticalLinePhasor.Erdos377.mellinClock_pos
#print axioms CriticalLinePhasor.Erdos377.terminalMellinDrift_pos_iff
#print axioms CriticalLinePhasor.Erdos377.mellinRailCoordinate_three_pow
#print axioms CriticalLinePhasor.Erdos377.mellinCellReconstruction_eq_secondDifference
#print axioms CriticalLinePhasor.Erdos377.recursiveWarpedInteriorVariation_le_mellinComponents
#print axioms CriticalLinePhasor.Erdos377.fullyMellinReconstructedLedger_eq_recursiveWarpedLedger
#print axioms CriticalLinePhasor.Erdos377.abs_fullyMellinReconstructedLedger_le
#print axioms CriticalLinePhasor.Erdos377.railBand_dynamicSquareSign_terminal_mellin
#print axioms CriticalLinePhasor.Erdos377.terminalMellinDrift_three_pow
#print axioms CriticalLinePhasor.Erdos377.terminalMellinDrift_three_pow_pos
#print axioms CriticalLinePhasor.Erdos377.railBand_nonterminal_dwell_ledger_le_fullMellinVariation
#print axioms CriticalLinePhasor.Erdos377.erdos377Mass_eq_sum_fullyMellinDwell
#print axioms CriticalLinePhasor.Erdos377.three_pow_terminal_dynamicBankSignedLedger_eq_one_third
#print axioms CriticalLinePhasor.Erdos377.not_exists_uniformTerminalMellinDecay
#print axioms CriticalLinePhasor.Erdos377.dynamicClosureWeight_le_one
#print axioms CriticalLinePhasor.Erdos377.harmonicAtomicRailBand_subset_railBand
#print axioms CriticalLinePhasor.Erdos377.harmonicDiffuseRailBand_subset_railBand
#print axioms CriticalLinePhasor.Erdos377.harmonicDiffuse_atom_lt_bandMass
#print axioms CriticalLinePhasor.Erdos377.primeHarmonicMass_harmonicAtomicRailBand_le_depth_over_two
#print axioms CriticalLinePhasor.Erdos377.dynamicBankEnergy_le_primeHarmonicMass
#print axioms CriticalLinePhasor.Erdos377.dynamicBankEnergy_harmonicAtomic_terminal_eq_mass
#print axioms CriticalLinePhasor.Erdos377.dynamicBankEnergy_harmonicDiffuse_terminal_eq_mass
#print axioms CriticalLinePhasor.Erdos377.erdos377Mass_eq_sum_harmonicAtomicDiffuseEnergy
#print axioms CriticalLinePhasor.Erdos377.erdos377Mass_eq_sum_harmonicAtomicDiffuseDwell
#print axioms CriticalLinePhasor.Erdos377.tsum_depth_mul_dwell_div_two_eq_one
#print axioms CriticalLinePhasor.Erdos377.harmonicAtomicEntranceMass_le_one
#print axioms CriticalLinePhasor.Erdos377.dynamicPrefixBoundaryPrimeBank_eq_empty_of_subset_railBand
#print axioms CriticalLinePhasor.Erdos377.dynamicPrefixBoundaryLedger_eq_zero_of_subset_railBand
#print axioms CriticalLinePhasor.Erdos377.recursiveWarpedBoundaryMass_nonterminal_eq_zero_of_subset_railBand
#print axioms CriticalLinePhasor.Erdos377.nonterminal_dwell_ledger_le_fullMellinVariation_of_subset_railBand
#print axioms CriticalLinePhasor.Erdos377.harmonicDiffuse_nonterminal_dwell_ledger_le_fullMellinVariation
#print axioms CriticalLinePhasor.Erdos377.erdos377Mass_eq_sum_harmonicAtomicDiffuseFullyMellinDwell
#print axioms CriticalLinePhasor.Erdos377.occupiedDepth_pos
#print axioms CriticalLinePhasor.Erdos377.dynamicBankEnergy_succ_le_of_positive_primes
#print axioms CriticalLinePhasor.Erdos377.dynamicBankEnergy_harmonicDiffuse_terminal_le_preterminal
#print axioms CriticalLinePhasor.Erdos377.primeHarmonicMass_harmonicDiffuseDepthBand_le_preterminal
#print axioms CriticalLinePhasor.Erdos377.abs_dynamicBankSignedLedger_le_fullMellinVariation_of_subset_railBand
#print axioms CriticalLinePhasor.Erdos377.harmonicDiffuseDepthBand_mass_le_preterminalFullMellin
#print axioms CriticalLinePhasor.Erdos377.sum_harmonicDiffuseDepthBand_mass_le_preterminalFullMellin
#print axioms CriticalLinePhasor.Erdos377.dynamicBankEnergy_railBand_terminal_le_preterminal
#print axioms CriticalLinePhasor.Erdos377.primeHarmonicMass_depthBand_le_preterminal
#print axioms CriticalLinePhasor.Erdos377.depthBand_mass_le_preterminalFullMellin
#print axioms CriticalLinePhasor.Erdos377.erdos377Mass_le_sum_preterminalFullMellin
#print axioms CriticalLinePhasor.Erdos377.primeReciprocalIoc_eq_abel
#print axioms CriticalLinePhasor.Erdos377.primeReciprocalIoc_le_abel
#print axioms CriticalLinePhasor.Erdos377.primeCounting_floor_le_chebyshev
#print axioms CriticalLinePhasor.Erdos377.primeCounting_floor_div_sq_le_chebyshev
#print axioms CriticalLinePhasor.Erdos377.primeCounting_le_self
#print axioms CriticalLinePhasor.Erdos377.primeCounting_floor_div_sq_le_inv
#print axioms CriticalLinePhasor.Erdos377.primeReciprocalIoc_le_one_add_log_ratio
#print axioms CriticalLinePhasor.Erdos377.railBand_pow_le_and_lt_pow
#print axioms CriticalLinePhasor.Erdos377.sameRailBand_crossed_power_window
#print axioms CriticalLinePhasor.Erdos377.sameRailBand_mellin_window
#print axioms CriticalLinePhasor.Erdos377.primeCounting_floor_le_mellinKernel
#print axioms CriticalLinePhasor.Erdos377.primeCounting_floor_div_sq_le_mellinKernel
#print axioms CriticalLinePhasor.Erdos377.primeReciprocalIoc_le_one_add_mellinWidth
#print axioms CriticalLinePhasor.Erdos377.sameRailBand_log_lt_two_mul
#print axioms CriticalLinePhasor.Erdos377.sameRailBand_mellinWidth_lt_log_two
#print axioms CriticalLinePhasor.Erdos377.primeHarmonicMass_railBand_le_min_add_Ioc
#print axioms CriticalLinePhasor.Erdos377.primeHarmonicMass_railBand_le_uniform
#print axioms CriticalLinePhasor.Erdos377.preterminalEntrance_uniform
#print axioms CriticalLinePhasor.Erdos377.erdos377Mass_le_uniformEntrance_add_preterminalVariation
#print axioms CriticalLinePhasor.Erdos377.quotientCell_logClockDefect_eq_harmonicContourResidual
#print axioms CriticalLinePhasor.Erdos377.sum_range_scaled_quotientCell_logClockDefect_le_quarter
#print axioms CriticalLinePhasor.Erdos377.sum_depth_scaled_quotientCell_logClockDefect_le_half
#print axioms CriticalLinePhasor.Erdos377.mellinCellGradientAdapter_eq_sampling_add_clockCurvature
#print axioms CriticalLinePhasor.Erdos377.recursiveMellinAdapterVariation_le_sampling_add_clockCurvature
#print axioms CriticalLinePhasor.Erdos377.mellinComponents_le_recursiveWarpedInteriorVariation_add_two_adapters
#print axioms CriticalLinePhasor.Erdos377.preterminalMellinAdapterCost_le_sampling_add_clockCurvature
#print axioms CriticalLinePhasor.Erdos377.preterminalMellinVariation_le_warped_add_sampling_add_clock
#print axioms CriticalLinePhasor.Erdos377.erdos377Mass_le_uniformEntrance_add_warped_sampling_clock
#print axioms CriticalLinePhasor.Erdos377.deriv_mellinReciprocal
#print axioms CriticalLinePhasor.Erdos377.primeMellinIoc_eq_abel
#print axioms CriticalLinePhasor.Erdos377.primeMellinMass_primesLE_uniform
#print axioms CriticalLinePhasor.Erdos377.normalizedBankPrimeCarrier_le_primeMellinMass
#print axioms CriticalLinePhasor.Erdos377.sum_Ico_abs_mellinCellContinuousClockCurvature_le_primeMellinMass
#print axioms CriticalLinePhasor.Erdos377.recursiveMellinContinuousClockCurvatureVariation_le_primeMellinMass
#print axioms CriticalLinePhasor.Erdos377.preterminalMellinContinuousClockCurvatureCost_uniform
#print axioms CriticalLinePhasor.Erdos377.preterminalMellinVariation_le_uniformClock_add_warped_sampling_quantization
#print axioms CriticalLinePhasor.Erdos377.erdos377Mass_le_uniform_add_warped_sampling_quantization
#print axioms CriticalLinePhasor.Erdos377.abs_bankReciprocalPrimeCell_secondDifference_le_mass
#print axioms CriticalLinePhasor.Erdos377.dynamicPrefixInteriorPrimeBank_mass_eq_sum_cells
#print axioms CriticalLinePhasor.Erdos377.recursiveWarpedInteriorVariation_le_dynamicBankEnergy
#print axioms CriticalLinePhasor.Erdos377.preterminalWarpedVariation_le_survivorEnergy
#print axioms CriticalLinePhasor.Erdos377.primePreterminalStoppingKernel_nonneg
#print axioms CriticalLinePhasor.Erdos377.primePreterminalStoppingKernel_le_one
#print axioms CriticalLinePhasor.Erdos377.depthPreterminalSurvivorEnergy_eq_primeStoppingKernel
#print axioms CriticalLinePhasor.Erdos377.depthPreterminalSurvivorEnergy_le_primeHarmonicMass
#print axioms CriticalLinePhasor.Erdos377.depthBand_mass_le_entrance_add_signedWarped
#print axioms CriticalLinePhasor.Erdos377.erdos377Mass_le_preterminalEntrance_add_signedWarpedLedger
#print axioms CriticalLinePhasor.Erdos377.erdos377Mass_le_uniformEntrance_add_signedWarpedLedger
#print axioms CriticalLinePhasor.Erdos377.preterminalSignedFullyMellinLedger_eq_signedWarpedLedger
#print axioms CriticalLinePhasor.Erdos377.erdos377Mass_le_uniformEntrance_add_signedFullyMellinLedger
#print axioms CriticalLinePhasor.Erdos377.sum_occupiedDepths_preterminalEnergy_eq_primeHarmonicMass
#print axioms CriticalLinePhasor.Erdos377.erdos377Mass_le_preterminalClosedPrimeBankMass
#print axioms CriticalLinePhasor.Erdos377.preterminalSignedWarpedLedger_eq_preterminalMass_sub_entrance
#print axioms CriticalLinePhasor.Erdos377.railBand_dynamicClosedOrbit_succ_iff_carryFree
#print axioms CriticalLinePhasor.Erdos377.preterminalClosedPrime_carryFree_iff_terminalThreshold
#print axioms CriticalLinePhasor.Erdos377.mem_terminalFailurePrimeBank_iff
#print axioms CriticalLinePhasor.Erdos377.terminalFailurePrime_power_window
#print axioms CriticalLinePhasor.Erdos377.carryFreePrimes_subset_preterminalClosedPrimeBank
#print axioms CriticalLinePhasor.Erdos377.preterminalClosedPrimeBank_eq_carryFree_union_terminalFailure
#print axioms CriticalLinePhasor.Erdos377.preterminalClosedPrimeBankMass_eq_erdos377Mass_add_terminalFailureMass
#print axioms CriticalLinePhasor.Erdos377.erdos377Mass_eq_half_preterminalMass_add_half_terminalSignedRootLedger
#print axioms CriticalLinePhasor.Erdos377.terminalSignedRootLedger_eq_erdos377Mass_sub_terminalFailureMass
#print axioms CriticalLinePhasor.Erdos377.terminalSignedFullyMellinRootLedger_eq_terminalSignedRootLedger
#print axioms CriticalLinePhasor.Erdos377.erdos377Mass_eq_half_entrance_add_half_compensatedFullyMellinLedger
#print axioms CriticalLinePhasor.Erdos377.depthCompensatedFullyMellinLedger_eq_terminalEnergy
#print axioms CriticalLinePhasor.Erdos377.postEntranceFirstFailureKernel_eq_entry_sub_terminal
#print axioms CriticalLinePhasor.Erdos377.dynamicClosureWeight_antitone_cells
#print axioms CriticalLinePhasor.Erdos377.postEntranceFirstFailureKernel_nonneg
#print axioms CriticalLinePhasor.Erdos377.postEntranceFirstFailureKernel_eq_ite
#print axioms CriticalLinePhasor.Erdos377.postEntranceFirstFailureKernel_le_one
#print axioms CriticalLinePhasor.Erdos377.sum_postEntranceFirstFailureKernel_eq_failureMass
#print axioms CriticalLinePhasor.Erdos377.mellinPrimeHaarWeight_mul_harmonicAmplitude
#print axioms CriticalLinePhasor.Erdos377.hasDerivAt_continuousMellinHarmonicAmplitude
#print axioms CriticalLinePhasor.Erdos377.continuousMellinHarmonicAmplitude_variation_budget
#print axioms CriticalLinePhasor.Erdos377.mellinHarmonicAmplitude_antitone_primes
#print axioms CriticalLinePhasor.Erdos377.warpedMeshVariation_eq_sub_of_antitone
#print axioms CriticalLinePhasor.Erdos377.warpedMeshVariation_le_entrance_of_antitone_nonneg
#print axioms CriticalLinePhasor.Erdos377.warpedMeshVariation_mellinHarmonicAmplitude_le
#print axioms CriticalLinePhasor.Erdos377.mellinHaarPrimeMesh_discreteStieltjesBound
#print axioms CriticalLinePhasor.Erdos377.depthCompensatedFullyMellinLedger_eq_firstFailureSum
#print axioms CriticalLinePhasor.Erdos377.compensatedFullyMellinLedger_eq_sum_depthCompensated
#print axioms CriticalLinePhasor.Erdos377.compensatedFullyMellinLedger_eq_firstFailureLedger
#print axioms CriticalLinePhasor.Erdos377.compensatedFullyMellinLedger_eq_mellinHaarFirstFailureLedger
#print axioms CriticalLinePhasor.Erdos377.mellinHaarCompensatedCharge_eq_threeWaySign
#print axioms CriticalLinePhasor.Erdos377.compensatedFullyMellinLedger_eq_onePrimeMellinHaarLedger
#print axioms CriticalLinePhasor.Erdos377.dynamicBankEnergy_railBand_three_pow_eq_one_third
#print axioms CriticalLinePhasor.Erdos377.three_pow_nonterminal_dynamicBankSignedLedger_eq_one_third
#print axioms CriticalLinePhasor.Erdos377.one_third_le_recursiveWarpedInteriorVariation_three_pow
#print axioms CriticalLinePhasor.Erdos377.one_six_le_depthPreterminalWarpedVariation_three_pow
#print axioms CriticalLinePhasor.Erdos377.not_exists_uniformPreterminalWarpedDepthDecay
#print axioms CriticalLinePhasor.Erdos377.recursiveWarpedInteriorVariation_empty
#print axioms CriticalLinePhasor.Erdos377.preterminalWarpedVariation_eq_harmonicAtomic_add_diffuse
#print axioms CriticalLinePhasor.Erdos377.recursiveMellinSamplingAdapterVariation_empty
#print axioms CriticalLinePhasor.Erdos377.recursiveMellinClockQuantizationVariation_empty
#print axioms CriticalLinePhasor.Erdos377.preterminalWarpedSamplingQuantizationVariation_eq
#print axioms CriticalLinePhasor.Erdos377.preterminalWarpedSamplingQuantizationVariation_eq_atomic_add_diffuse
#print axioms CriticalLinePhasor.Erdos377.erdos377Mass_le_uniform_add_preterminalWarpedSamplingQuantization
#print axioms CriticalLinePhasor.Erdos377.harmonicDiffuse_depth_lt_card
#print axioms CriticalLinePhasor.Erdos377.erdos377Bound_of_harmonicAtomic_diffuse_uniform_band
#print axioms CriticalLinePhasor.Erdos377.atomicRailBudget_of_erdos377Bound
#print axioms CriticalLinePhasor.Erdos377.harmonicAtomicRailBudget_of_erdos377Bound
#print axioms CriticalLinePhasor.Erdos377.railBand_depth_pos_of_nonempty
#print axioms CriticalLinePhasor.Erdos377.primeHarmonicMass_mono
#print axioms CriticalLinePhasor.Erdos377.uniformHarmonicDiffuseRailBandEnvelope
#print axioms CriticalLinePhasor.Erdos377.carryLedger_weighted_sum_eq_log_centralBinom
#print axioms CriticalLinePhasor.Erdos377.carry_conservation_law
#print axioms CriticalLinePhasor.Erdos377.carryFreeThrough_realizable
#print axioms CriticalLinePhasor.Erdos377.levelOne_add_deep_eq_log_centralBinom
#print axioms CriticalLinePhasor.Erdos377.levelOneCarryMass_eq_band_sum
#print axioms CriticalLinePhasor.Erdos377.deepCarryMass_le_sqrt_bound
#print axioms CriticalLinePhasor.Erdos377.harmonized_carry_conservation
#print axioms CriticalLinePhasor.Erdos377.primesLE_sdiff_logMass
#print axioms CriticalLinePhasor.Erdos377.levelTwoJointCarry_fiber_eq_sdiff
#print axioms CriticalLinePhasor.Erdos377.levelTwoJointCarry_fiber_logMass
