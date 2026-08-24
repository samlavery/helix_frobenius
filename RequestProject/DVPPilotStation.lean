import RequestProject.DVPEulerMaclaurin
import RequestProject.DVPDirichletBlock
import Mathlib.NumberTheory.Harmonic.EulerMascheroni

/-!
# E8 pilot station: `‖ζ(3/2) − 5217/2000‖ ≤ 1/100`

One complete worked station through the certificate pipeline: the
Euler–Maclaurin enclosure at `N = 4` plus kernel-arithmetic `√n` brackets.
Validates the composition end-to-end before the generated stations.
-/

open Complex Finset

noncomputable section

namespace CriticalLinePhasor.DVP

/-- `4^{−1/2} = 1/2` in real rpow. -/
private lemma four_rpow_neg_half : (4 : ℝ) ^ (-(1/2) : ℝ) = 1/2 := by
  have h4 : (4 : ℝ) = (2 : ℝ) ^ (2 : ℕ) := by norm_num
  rw [h4, ← Real.rpow_natCast (2 : ℝ) 2, ← Real.rpow_mul (by norm_num)]
  norm_num

/-- `4^{−3/2} = 1/8`. -/
private lemma four_rpow_neg_three_half : (4 : ℝ) ^ (-(3/2) : ℝ) = 1/8 := by
  have h4 : (4 : ℝ) = (2 : ℝ) ^ (2 : ℕ) := by norm_num
  rw [h4, ← Real.rpow_natCast (2 : ℝ) 2, ← Real.rpow_mul (by norm_num)]
  norm_num

/-- `4^{−7/2} = 1/128`. -/
private lemma four_rpow_neg_seven_half : (4 : ℝ) ^ (-(7/2) : ℝ) = 1/128 := by
  have h4 : (4 : ℝ) = (2 : ℝ) ^ (2 : ℕ) := by norm_num
  rw [h4, ← Real.rpow_natCast (2 : ℝ) 2, ← Real.rpow_mul (by norm_num)]
  norm_num

/-- `4^{−5/2} = 1/32`. -/
private lemma four_rpow_neg_five_half : (4 : ℝ) ^ (-(5/2) : ℝ) = 1/32 := by
  have h4 : (4 : ℝ) = (2 : ℝ) ^ (2 : ℕ) := by norm_num
  rw [h4, ← Real.rpow_natCast (2 : ℝ) 2, ← Real.rpow_mul (by norm_num)]
  norm_num

/-- `n^{−3/2} = n^{−1}·n^{−1/2}` for positive natural base. -/
private lemma rpow_neg_three_half_eq {n : ℕ} (hn : 1 ≤ n) :
    ((n : ℝ)) ^ (-(3/2) : ℝ) = ((n : ℝ))⁻¹ * ((n : ℝ)) ^ (-(1/2) : ℝ) := by
  have hpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  rw [show (-(3/2) : ℝ) = (-1) + (-(1/2)) by norm_num,
    Real.rpow_add hpos]
  congr 1
  rw [show ((-1 : ℝ)) = ((-1 : ℤ) : ℝ) by norm_num, Real.rpow_intCast,
    zpow_neg_one]

/-- **THE PILOT STATION**: a kernel-checked rigorous evaluation of ζ at a
real point through the Euler–Maclaurin enclosure, to one percent. -/
theorem pilot_station_A :
    ‖riemannZeta (((3/2 : ℝ)) : ℂ) - (((5217/2000 : ℝ)) : ℂ)‖ ≤ 1/100 := by
  set s : ℂ := ((3/2 : ℝ) : ℂ) with hsdef
  have hσ : 0 < s.re := by
    rw [hsdef]
    simp only [Complex.ofReal_re]
    norm_num
  have hs1 : s ≠ 1 := by
    rw [hsdef]
    intro h
    have := congrArg Complex.re h
    simp at this
    norm_num at this
  have hN : 1 ≤ 4 := by norm_num
  have hEM := zeta_EM_enclosure_numeric (N := 4) hN hσ hs1
  -- the EM error is 39/4096
  have hsre : s.re = 3/2 := by
    rw [hsdef]
    simp
  have hnorm_s : ‖s‖ = 3/2 := by
    rw [hsdef, Complex.norm_real, Real.norm_eq_abs]
    norm_num
  have hnorm_s1 : ‖s + 1‖ = 5/2 := by
    have h1 : s + 1 = ((5/2 : ℝ) : ℂ) := by
      rw [hsdef]
      push_cast
      ring
    rw [h1, Complex.norm_real, Real.norm_eq_abs]
    norm_num
  have hEMerr : ‖s‖ * ‖s + 1‖ * (1/8)
      * (((4 : ℕ) : ℝ) ^ (-s.re - 2) + ((4 : ℕ) : ℝ) ^ (-s.re - 1) / (s.re + 1))
      = 39/4096 := by
    rw [hnorm_s, hnorm_s1, hsre]
    have hc : ((4 : ℕ) : ℝ) = (4 : ℝ) := by norm_num
    rw [hc]
    rw [show (-(3/2 : ℝ) - 2) = (-(7/2) : ℝ) by norm_num,
      show (-(3/2 : ℝ) - 1) = (-(5/2) : ℝ) by norm_num,
      four_rpow_neg_seven_half, four_rpow_neg_five_half]
    norm_num
  rw [hEMerr] at hEM
  -- the boundary terms are EXACT
  have hone_minus : (1 : ℂ) - s = ((-(1/2) : ℝ) : ℂ) := by
    rw [hsdef]
    push_cast
    ring
  have hneg_s : -s = ((-(3/2) : ℝ) : ℂ) := by
    rw [hsdef]
    push_cast
    ring
  have hboundary : (((4 : ℕ) : ℝ) : ℂ) ^ (1 - s) / (s - 1) = 1 := by
    rw [hone_minus]
    have hb : (((4 : ℕ) : ℝ) : ℂ) ^ (((-(1/2) : ℝ)) : ℂ)
        = (((4 : ℝ) ^ (-(1/2) : ℝ) : ℝ) : ℂ) := by
      rw [← Complex.ofReal_cpow (by norm_num)]
      norm_num
    rw [hb, four_rpow_neg_half]
    have hs1' : s - 1 = ((1/2 : ℝ) : ℂ) := by
      rw [hsdef]
      push_cast
      ring
    rw [hs1']
    push_cast
    norm_num
  have hcorr : (((4 : ℕ) : ℝ) : ℂ) ^ (-s) / 2 = ((1/16 : ℝ) : ℂ) := by
    rw [hneg_s]
    have hb : (((4 : ℕ) : ℝ) : ℂ) ^ (((-(3/2) : ℝ)) : ℂ)
        = (((4 : ℝ) ^ (-(3/2) : ℝ) : ℝ) : ℂ) := by
      rw [← Complex.ofReal_cpow (by norm_num)]
      norm_num
    rw [hb, four_rpow_neg_three_half]
    push_cast
    norm_num
  -- the head terms
  set t2 : ℝ := (2 : ℝ) ^ (-(3/2) : ℝ) with ht2def
  set t3 : ℝ := (3 : ℝ) ^ (-(3/2) : ℝ) with ht3def
  have hhead : ∑ n ∈ Finset.range (4 + 1), (((n : ℝ)) : ℂ) ^ (-s)
      = ((1 + t2 + t3 + 1/8 : ℝ) : ℂ) := by
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_succ, Finset.sum_range_one]
    have h0 : (((0 : ℕ) : ℝ) : ℂ) ^ (-s) = 0 := by
      norm_num
      intro h
      rw [hsdef] at h
      rw [show (0 : ℂ) = ((0 : ℝ) : ℂ) by norm_num] at h
      exact absurd (Complex.ofReal_inj.mp h) (by norm_num)
    have h1 : (((1 : ℕ) : ℝ) : ℂ) ^ (-s) = 1 := by
      norm_num
    have h2 : (((2 : ℕ) : ℝ) : ℂ) ^ (-s) = ((t2 : ℝ) : ℂ) := by
      rw [hneg_s, ht2def]
      rw [← Complex.ofReal_cpow (by norm_num)]
      norm_num
    have h3 : (((3 : ℕ) : ℝ) : ℂ) ^ (-s) = ((t3 : ℝ) : ℂ) := by
      rw [hneg_s, ht3def]
      rw [← Complex.ofReal_cpow (by norm_num)]
      norm_num
    have h4 : (((4 : ℕ) : ℝ) : ℂ) ^ (-s) = ((1/8 : ℝ) : ℂ) := by
      rw [hneg_s]
      have hb : (((4 : ℕ) : ℝ) : ℂ) ^ (((-(3/2) : ℝ)) : ℂ)
          = (((4 : ℝ) ^ (-(3/2) : ℝ) : ℝ) : ℂ) := by
        rw [← Complex.ofReal_cpow (by norm_num)]
        norm_num
      rw [hb, four_rpow_neg_three_half]
    rw [h0, h1, h2, h3, h4]
    push_cast
    ring
  -- the √n brackets, kernel arithmetic
  have hy2 := inv_sqrt_enclosure (n := 2) (a := 7071/10000) (b := 70711/100000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hy3 := inv_sqrt_enclosure (n := 3) (a := 57735/100000) (b := 57736/100000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have ht2eq : t2 = (2 : ℝ)⁻¹ * (2 : ℝ) ^ (-(1/2) : ℝ) := by
    rw [ht2def]
    have := rpow_neg_three_half_eq (n := 2) (by norm_num)
    push_cast at this ⊢
    exact this
  have ht3eq : t3 = (3 : ℝ)⁻¹ * (3 : ℝ) ^ (-(1/2) : ℝ) := by
    rw [ht3def]
    have := rpow_neg_three_half_eq (n := 3) (by norm_num)
    push_cast at this ⊢
    exact this
  have ht2bracket : |t2 - (7071/20000 : ℝ)| ≤ 1/200000 := by
    have h1 : ((7071/10000 : ℚ) : ℝ) ≤ (2 : ℝ) ^ (-(1/2) : ℝ) := by
      have := hy2.1
      push_cast at this ⊢
      convert this using 2
    have h2 : (2 : ℝ) ^ (-(1/2) : ℝ) ≤ ((70711/100000 : ℚ) : ℝ) := by
      have := hy2.2
      push_cast at this ⊢
      convert this using 2
    push_cast at h1 h2
    rw [ht2eq, abs_le]
    constructor <;> nlinarith
  have ht3bracket : |t3 - (3849/20000 : ℝ)| ≤ 1/300000 := by
    have h1 : ((57735/100000 : ℚ) : ℝ) ≤ (3 : ℝ) ^ (-(1/2) : ℝ) := by
      have := hy3.1
      push_cast at this ⊢
      convert this using 2
    have h2 : (3 : ℝ) ^ (-(1/2) : ℝ) ≤ ((57736/100000 : ℚ) : ℝ) := by
      have := hy3.2
      push_cast at this ⊢
      convert this using 2
    push_cast at h1 h2
    rw [ht3eq, abs_le]
    constructor <;> nlinarith
  -- assembly
  have hdiff : ((∑ n ∈ Finset.range (4 + 1), (((n : ℝ)) : ℂ) ^ (-s))
        + (((4 : ℕ) : ℝ) : ℂ) ^ (1 - s) / (s - 1)
        - (((4 : ℕ) : ℝ) : ℂ) ^ (-s) / 2)
      - (((5217/2000 : ℝ)) : ℂ)
      = (((t2 - 7071/20000 : ℝ)) : ℂ) + (((t3 - 3849/20000 : ℝ)) : ℂ) := by
    rw [hhead, hboundary, hcorr]
    push_cast
    ring
  calc ‖riemannZeta s - (((5217/2000 : ℝ)) : ℂ)‖
      = ‖(riemannZeta s
          - ((∑ n ∈ Finset.range (4 + 1), (((n : ℝ)) : ℂ) ^ (-s))
            + (((4 : ℕ) : ℝ) : ℂ) ^ (1 - s) / (s - 1)
            - (((4 : ℕ) : ℝ) : ℂ) ^ (-s) / 2))
          + (((∑ n ∈ Finset.range (4 + 1), (((n : ℝ)) : ℂ) ^ (-s))
            + (((4 : ℕ) : ℝ) : ℂ) ^ (1 - s) / (s - 1)
            - (((4 : ℕ) : ℝ) : ℂ) ^ (-s) / 2)
            - (((5217/2000 : ℝ)) : ℂ))‖ := by
        congr 1
        ring
    _ ≤ ‖riemannZeta s
          - ((∑ n ∈ Finset.range (4 + 1), (((n : ℝ)) : ℂ) ^ (-s))
            + (((4 : ℕ) : ℝ) : ℂ) ^ (1 - s) / (s - 1)
            - (((4 : ℕ) : ℝ) : ℂ) ^ (-s) / 2)‖
          + ‖((∑ n ∈ Finset.range (4 + 1), (((n : ℝ)) : ℂ) ^ (-s))
            + (((4 : ℕ) : ℝ) : ℂ) ^ (1 - s) / (s - 1)
            - (((4 : ℕ) : ℝ) : ℂ) ^ (-s) / 2)
            - (((5217/2000 : ℝ)) : ℂ)‖ := norm_add_le _ _
    _ ≤ 39/4096 + (1/200000 + 1/300000) := by
        apply add_le_add hEM
        rw [hdiff]
        calc ‖(((t2 - 7071/20000 : ℝ)) : ℂ) + (((t3 - 3849/20000 : ℝ)) : ℂ)‖
            ≤ ‖(((t2 - 7071/20000 : ℝ)) : ℂ)‖
              + ‖(((t3 - 3849/20000 : ℝ)) : ℂ)‖ := norm_add_le _ _
          _ = |t2 - 7071/20000| + |t3 - 3849/20000| := by
              rw [Complex.norm_real, Complex.norm_real,
                Real.norm_eq_abs, Real.norm_eq_abs]
          _ ≤ 1/200000 + 1/300000 := add_le_add ht2bracket ht3bracket
    _ ≤ 1/100 := by norm_num

/-- **PILOT B — the angle path in anger**: a kernel-checked enclosure of
`cos 1` through the quarter-angle machinery (`k = 0`, `r = ¼`, `δ = 0`;
the sin certificate is the order-3 Taylor value `30401/122880` with tail
`7/17694720`).  True value `0.5403023…`; certified to `1/25000`. -/
theorem pilot_station_B :
    |Real.cos 1
      - ((2 * (1 - 2 * (30401/122880 : ℚ) ^ 2) ^ 2 - 1 : ℚ) : ℝ)|
      ≤ 1/25000 := by
  have hsinT : sinTaylor (1/4) 3 = 30401/122880 := by
    norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial]
  have htail := sin_enclosure (x := (1/4 : ℚ)) (by norm_num) (n := 3)
    (by norm_num)
  rw [hsinT] at htail
  have htail' : |Real.sin ((1/4 : ℚ) : ℝ) - ((30401/122880 : ℚ) : ℝ)|
      ≤ ((7/17694720 : ℚ) : ℝ) := by
    have hb : |((1/4 : ℚ) : ℝ)| ^ (2 * 3)
        * (((2 * 3).succ : ℝ) * (((2 * 3).factorial : ℝ) * ((2 * 3 : ℕ) : ℝ))⁻¹)
        = ((7/17694720 : ℚ) : ℝ) := by
      norm_num [Nat.factorial]
    rw [hb] at htail
    exact htail
  have hθ : |(1 : ℝ) - (0 : ℤ) * (2 * Real.pi) - 4 * ((1/4 : ℚ) : ℝ)|
      ≤ ((0 : ℚ) : ℝ) := by
    push_cast
    norm_num
  have hŝ2 : |((30401/122880 : ℚ) : ℝ)| ≤ 2 := by
    rw [abs_le]
    constructor <;> norm_num
  have hmain := cos_angle_eval (θ := (1 : ℝ)) (r := 1/4)
    (ŝ := 30401/122880) (δ := 0) (τ := 7/17694720)
    (0 : ℤ) hθ htail' hŝ2
  calc |Real.cos 1
      - ((2 * (1 - 2 * (30401/122880 : ℚ) ^ 2) ^ 2 - 1 : ℚ) : ℝ)|
      ≤ ((0 : ℚ) : ℝ) + 96 * ((7/17694720 : ℚ) : ℝ) := hmain
    _ ≤ 1/25000 := by
        push_cast
        norm_num

/-- **PILOT C — the log certificate in anger**: `log 2` to five decimals,
via order-10 Taylor for `exp` at the two endpoints (no shift needed:
both arguments are below 1).  The kernel evaluates the order-10 partial
sums exactly. -/
theorem pilot_station_C :
    ((69314/100000 : ℚ) : ℝ) ≤ Real.log 2
      ∧ Real.log 2 ≤ ((69315/100000 : ℚ) : ℝ) := by
  have henc1 := exp_enclosure (x := (69314/100000 : ℚ))
    (by norm_num) (n := 10) (by norm_num)
  have henc2 := exp_enclosure (x := (69315/100000 : ℚ))
    (by norm_num) (n := 10) (by norm_num)
  have h1 : Real.exp ((69314/100000 : ℚ) : ℝ) ≤ (2 : ℕ) := by
    have hub := (abs_le.mp henc1).2
    have hval : ((expTaylor (69314/100000) 10 : ℚ) : ℝ)
        + |((69314/100000 : ℚ) : ℝ)| ^ 10
          * (((10 : ℕ).succ : ℝ) / (((10 : ℕ).factorial : ℝ) * 10)) ≤ 2 := by
      rw [show |((69314/100000 : ℚ) : ℝ)| = ((69314/100000 : ℚ) : ℝ) from
        abs_of_pos (by norm_num)]
      push_cast
      norm_num [expTaylor, Finset.sum_range_succ, Nat.factorial]
    push_cast
    linarith
  have h2 : ((2 : ℕ) : ℝ) ≤ Real.exp ((69315/100000 : ℚ) : ℝ) := by
    have hlb := (abs_le.mp henc2).1
    have hval : (2 : ℝ) ≤ ((expTaylor (69315/100000) 10 : ℚ) : ℝ)
        - |((69315/100000 : ℚ) : ℝ)| ^ 10
          * (((10 : ℕ).succ : ℝ) / (((10 : ℕ).factorial : ℝ) * 10)) := by
      rw [show |((69315/100000 : ℚ) : ℝ)| = ((69315/100000 : ℚ) : ℝ) from
        abs_of_pos (by norm_num)]
      push_cast
      norm_num [expTaylor, Finset.sum_range_succ, Nat.factorial]
    push_cast
    linarith
  have hlog := log_enclosure_nat (m := 2) (by norm_num) h1 h2
  have hc : ((2 : ℕ) : ℝ) = (2 : ℝ) := by norm_num
  rw [hc] at hlog
  exact hlog

/-- `log 10 ≥ 2299/1000`, by an order-8 exp certificate with shift 2. -/
theorem log_ten_lower : ((2299/1000 : ℚ) : ℝ) ≤ Real.log 10 := by
  have henc := exp_enclosure (x := (299/1000 : ℚ))
    (by norm_num) (n := 8) (by norm_num)
  have hτ : |Real.exp ((299/1000 : ℚ) : ℝ)
      - ((expTaylor (299/1000) 8 : ℚ) : ℝ)| ≤ ((1/10^7 : ℚ) : ℝ) := by
    have hb : |((299/1000 : ℚ) : ℝ)| ^ 8
        * (((8 : ℕ).succ : ℝ) / (((8 : ℕ).factorial : ℝ) * 8))
        ≤ ((1/10^7 : ℚ) : ℝ) := by
      rw [show |((299/1000 : ℚ) : ℝ)| = ((299/1000 : ℚ) : ℝ) from
        abs_of_pos (by norm_num)]
      push_cast
      norm_num [Nat.factorial]
    exact le_trans henc hb
  have hshift := exp_upper_shift (x := (2299/1000 : ℚ)) 2
    (by
      have hx : ((2299/1000 : ℚ) - (2 : ℕ) : ℚ) = 299/1000 := by norm_num
      rw [hx]
      exact hτ)
  have h10 : Real.exp ((2299/1000 : ℚ) : ℝ) ≤ (10 : ℕ) := by
    refine le_trans hshift ?_
    push_cast
    norm_num [expTaylor, Finset.sum_range_succ, Nat.factorial]
  have := (log_enclosure_nat (m := 10) (by norm_num) h10
    (le_of_lt (by
      calc ((10 : ℕ) : ℝ) = 10 := by norm_num
        _ < Real.exp 10 := by
            nlinarith [Real.add_one_le_exp (10:ℝ)]))).1
  calc ((2299/1000 : ℚ) : ℝ) ≤ Real.log ((10 : ℕ) : ℝ) := this
    _ = Real.log 10 := by norm_num

/-- `log 11 ≤ 23989/10000`, by an order-8 exp certificate with shift 2. -/
theorem log_eleven_upper : Real.log 11 ≤ ((23989/10000 : ℚ) : ℝ) := by
  have henc := exp_enclosure (x := (3989/10000 : ℚ))
    (by norm_num) (n := 8) (by norm_num)
  have hτ : |Real.exp ((3989/10000 : ℚ) : ℝ)
      - ((expTaylor (3989/10000) 8 : ℚ) : ℝ)| ≤ ((1/10^7 : ℚ) : ℝ) := by
    have hb : |((3989/10000 : ℚ) : ℝ)| ^ 8
        * (((8 : ℕ).succ : ℝ) / (((8 : ℕ).factorial : ℝ) * 8))
        ≤ ((1/10^7 : ℚ) : ℝ) := by
      rw [show |((3989/10000 : ℚ) : ℝ)| = ((3989/10000 : ℚ) : ℝ) from
        abs_of_pos (by norm_num)]
      push_cast
      norm_num [Nat.factorial]
    exact le_trans henc hb
  have hshift := exp_lower_shift (x := (23989/10000 : ℚ)) 2
    (by
      have hx : ((23989/10000 : ℚ) - (2 : ℕ) : ℚ) = 3989/10000 := by norm_num
      rw [hx]
      exact hτ)
    (by norm_num [expTaylor, Finset.sum_range_succ, Nat.factorial])
  have h11 : ((11 : ℕ) : ℝ) ≤ Real.exp ((23989/10000 : ℚ) : ℝ) := by
    refine le_trans ?_ hshift
    push_cast
    norm_num [expTaylor, Finset.sum_range_succ, Nat.factorial]
  have := (log_enclosure_nat (m := 11) (by norm_num)
    (by
      calc Real.exp ((0 : ℚ) : ℝ) = 1 := by norm_num [Real.exp_zero]
        _ ≤ ((11 : ℕ) : ℝ) := by norm_num) h11).2
  calc Real.log 11 = Real.log ((11 : ℕ) : ℝ) := by norm_num
    _ ≤ ((23989/10000 : ℚ) : ℝ) := this

/-- **The γ enclosure**: `0.53 < γ < 0.63`, from the `n = 10` mathlib
sandwich `harmonic 10 − log 11 < γ < harmonic 10 − log 10` with the two log
certificates above (`harmonic 10 = 7381/2520`, kernel-evaluated). -/
theorem gamma_enclosure :
    (53/100 : ℝ) < Real.eulerMascheroniConstant
      ∧ Real.eulerMascheroniConstant < 63/100 := by
  have hlow := Real.eulerMascheroniSeq_lt_eulerMascheroniConstant 10
  have hhigh := Real.eulerMascheroniConstant_lt_eulerMascheroniSeq' 10
  have hseq : Real.eulerMascheroniSeq 10 = harmonic 10 - Real.log 11 := by
    rw [Real.eulerMascheroniSeq]
    norm_num
  have hseq' : Real.eulerMascheroniSeq' 10 = harmonic 10 - Real.log 10 := by
    rw [Real.eulerMascheroniSeq']
    norm_num
  have hharm : (harmonic 10 : ℝ) = 7381/2520 := by
    norm_num [harmonic_succ, harmonic_zero]
  rw [hseq, hharm] at hlow
  rw [hseq', hharm] at hhigh
  have h11 := log_eleven_upper
  have h10 := log_ten_lower
  push_cast at h11 h10
  constructor
  · calc (53/100 : ℝ) < 7381/2520 - 23989/10000 := by norm_num
      _ ≤ 7381/2520 - Real.log 11 := by linarith
      _ < Real.eulerMascheroniConstant := hlow
  · calc Real.eulerMascheroniConstant < 7381/2520 - Real.log 10 := hhigh
      _ ≤ 7381/2520 - 2299/1000 := by linarith
      _ < 63/100 := by norm_num

/-- **The log π certificate**: `1.1447 ≤ log π ≤ 1.1448` (π to d6, exp
shift-certificates at order 7). -/
theorem log_pi_enclosure :
    ((11447/10000 : ℚ) : ℝ) ≤ Real.log Real.pi
      ∧ Real.log Real.pi ≤ ((11448/10000 : ℚ) : ℝ) := by
  have hπ := Real.pi_pos
  constructor
  · rw [Real.le_log_iff_exp_le hπ]
    have henc := exp_enclosure (x := (1447/10000 : ℚ))
      (by norm_num) (n := 7) (by norm_num)
    have hτ : |Real.exp ((1447/10000 : ℚ) : ℝ)
        - ((expTaylor (1447/10000) 7 : ℚ) : ℝ)| ≤ ((1/10^8 : ℚ) : ℝ) := by
      have hb : |((1447/10000 : ℚ) : ℝ)| ^ 7
          * (((7 : ℕ).succ : ℝ) / (((7 : ℕ).factorial : ℝ) * 7))
          ≤ ((1/10^8 : ℚ) : ℝ) := by
        rw [show |((1447/10000 : ℚ) : ℝ)| = ((1447/10000 : ℚ) : ℝ) from
          abs_of_pos (by norm_num)]
        push_cast
        norm_num [Nat.factorial]
      exact le_trans henc hb
    have hshift := exp_upper_shift (x := (11447/10000 : ℚ)) 1
      (by
        have hx : ((11447/10000 : ℚ) - (1 : ℕ) : ℚ) = 1447/10000 := by
          norm_num
        rw [hx]
        exact hτ)
    have hnum : (((expTaylor (1447/10000) 7 + 1/10^8)
        * (2.7182818286 : ℚ) ^ 1 : ℚ) : ℝ) ≤ 3.141592 := by
      push_cast
      norm_num [expTaylor, Finset.sum_range_succ, Nat.factorial]
    have hpi6 := Real.pi_gt_d6
    calc Real.exp ((11447/10000 : ℚ) : ℝ)
        ≤ (((expTaylor (1447/10000) 7 + 1/10^8)
            * (2.7182818286 : ℚ) ^ 1 : ℚ) : ℝ) := hshift
      _ ≤ 3.141592 := hnum
      _ ≤ Real.pi := le_of_lt hpi6
  · rw [Real.log_le_iff_le_exp hπ]
    have henc := exp_enclosure (x := (1448/10000 : ℚ))
      (by norm_num) (n := 7) (by norm_num)
    have hτ : |Real.exp ((1448/10000 : ℚ) : ℝ)
        - ((expTaylor (1448/10000) 7 : ℚ) : ℝ)| ≤ ((1/10^8 : ℚ) : ℝ) := by
      have hb : |((1448/10000 : ℚ) : ℝ)| ^ 7
          * (((7 : ℕ).succ : ℝ) / (((7 : ℕ).factorial : ℝ) * 7))
          ≤ ((1/10^8 : ℚ) : ℝ) := by
        rw [show |((1448/10000 : ℚ) : ℝ)| = ((1448/10000 : ℚ) : ℝ) from
          abs_of_pos (by norm_num)]
        push_cast
        norm_num [Nat.factorial]
      exact le_trans henc hb
    have hshift := exp_lower_shift (x := (11448/10000 : ℚ)) 1
      (by
        have hx : ((11448/10000 : ℚ) - (1 : ℕ) : ℚ) = 1448/10000 := by
          norm_num
        rw [hx]
        exact hτ)
      (by norm_num [expTaylor, Finset.sum_range_succ, Nat.factorial])
    have hnum : (3.141593 : ℝ)
        ≤ (((expTaylor (1448/10000) 7 - 1/10^8)
            * (2.7182818283 : ℚ) ^ 1 : ℚ) : ℝ) := by
      push_cast
      norm_num [expTaylor, Finset.sum_range_succ, Nat.factorial]
    have hpi6 := Real.pi_lt_d6
    calc Real.pi ≤ 3.141593 := le_of_lt hpi6
      _ ≤ (((expTaylor (1448/10000) 7 - 1/10^8)
            * (2.7182818283 : ℚ) ^ 1 : ℚ) : ℝ) := hnum
      _ ≤ Real.exp ((11448/10000 : ℚ) : ℝ) := hshift

/-- Tight two-sided `log 10`: `2.3025 ≤ log 10 ≤ 2.3026` (order-9 exp
certs, shift 2). -/
theorem log_ten_enclosure :
    ((23025/10000 : ℚ) : ℝ) ≤ Real.log 10
      ∧ Real.log 10 ≤ ((23026/10000 : ℚ) : ℝ) := by
  constructor
  · rw [show ((10:ℝ)) = (((10:ℕ)):ℝ) by norm_num]
    refine (log_enclosure_nat (m := 10) (by norm_num) ?_
      (le_of_lt (by
        calc (((10:ℕ)):ℝ) = 10 := by norm_num
          _ < Real.exp 10 := by nlinarith [Real.add_one_le_exp (10:ℝ)]))).1
    have henc := exp_enclosure (x := (3025/10000 : ℚ))
      (by norm_num) (n := 9) (by norm_num)
    have hτ : |Real.exp ((3025/10000 : ℚ) : ℝ)
        - ((expTaylor (3025/10000) 9 : ℚ) : ℝ)| ≤ ((1/10^8 : ℚ) : ℝ) := by
      have hb : |((3025/10000 : ℚ) : ℝ)| ^ 9
          * (((9 : ℕ).succ : ℝ) / (((9 : ℕ).factorial : ℝ) * 9))
          ≤ ((1/10^8 : ℚ) : ℝ) := by
        rw [show |((3025/10000 : ℚ) : ℝ)| = ((3025/10000 : ℚ) : ℝ) from
          abs_of_pos (by norm_num)]
        push_cast
        norm_num [Nat.factorial]
      exact le_trans henc hb
    have hshift := exp_upper_shift (x := (23025/10000 : ℚ)) 2
      (by
        have hx : ((23025/10000 : ℚ) - (2 : ℕ) : ℚ) = 3025/10000 := by
          norm_num
        rw [hx]
        exact hτ)
    refine le_trans hshift ?_
    push_cast
    norm_num [expTaylor, Finset.sum_range_succ, Nat.factorial]
  · rw [show ((10:ℝ)) = (((10:ℕ)):ℝ) by norm_num]
    refine (log_enclosure_nat (m := 10) (by norm_num)
      (by
        calc Real.exp ((0:ℚ) : ℝ) = 1 := by norm_num [Real.exp_zero]
          _ ≤ (((10:ℕ)):ℝ) := by norm_num) ?_).2
    have henc := exp_enclosure (x := (3026/10000 : ℚ))
      (by norm_num) (n := 9) (by norm_num)
    have hτ : |Real.exp ((3026/10000 : ℚ) : ℝ)
        - ((expTaylor (3026/10000) 9 : ℚ) : ℝ)| ≤ ((1/10^8 : ℚ) : ℝ) := by
      have hb : |((3026/10000 : ℚ) : ℝ)| ^ 9
          * (((9 : ℕ).succ : ℝ) / (((9 : ℕ).factorial : ℝ) * 9))
          ≤ ((1/10^8 : ℚ) : ℝ) := by
        rw [show |((3026/10000 : ℚ) : ℝ)| = ((3026/10000 : ℚ) : ℝ) from
          abs_of_pos (by norm_num)]
        push_cast
        norm_num [Nat.factorial]
      exact le_trans henc hb
    have hshift := exp_lower_shift (x := (23026/10000 : ℚ)) 2
      (by
        have hx : ((23026/10000 : ℚ) - (2 : ℕ) : ℚ) = 3026/10000 := by
          norm_num
        rw [hx]
        exact hτ)
      (by norm_num [expTaylor, Finset.sum_range_succ, Nat.factorial])
    refine le_trans ?_ hshift
    push_cast
    norm_num [expTaylor, Finset.sum_range_succ, Nat.factorial]

/-- Two-sided `log 101`: `4.6151 ≤ log 101 ≤ 4.6152` (order-10 exp certs,
shift 4). -/
theorem log_101_enclosure :
    ((46151/10000 : ℚ) : ℝ) ≤ Real.log 101
      ∧ Real.log 101 ≤ ((46152/10000 : ℚ) : ℝ) := by
  constructor
  · rw [show ((101:ℝ)) = (((101:ℕ)):ℝ) by norm_num]
    refine (log_enclosure_nat (m := 101) (by norm_num) ?_
      (le_of_lt (by
        calc (((101:ℕ)):ℝ) = 101 := by norm_num
          _ < Real.exp 101 := by nlinarith [Real.add_one_le_exp (101:ℝ)]))).1
    have henc := exp_enclosure (x := (6151/10000 : ℚ))
      (by norm_num) (n := 10) (by norm_num)
    have hτ : |Real.exp ((6151/10000 : ℚ) : ℝ)
        - ((expTaylor (6151/10000) 10 : ℚ) : ℝ)| ≤ ((1/10^7 : ℚ) : ℝ) := by
      have hb : |((6151/10000 : ℚ) : ℝ)| ^ 10
          * (((10 : ℕ).succ : ℝ) / (((10 : ℕ).factorial : ℝ) * 10))
          ≤ ((1/10^7 : ℚ) : ℝ) := by
        rw [show |((6151/10000 : ℚ) : ℝ)| = ((6151/10000 : ℚ) : ℝ) from
          abs_of_pos (by norm_num)]
        push_cast
        norm_num [Nat.factorial]
      exact le_trans henc hb
    have hshift := exp_upper_shift (x := (46151/10000 : ℚ)) 4
      (by
        have hx : ((46151/10000 : ℚ) - (4 : ℕ) : ℚ) = 6151/10000 := by
          norm_num
        rw [hx]
        exact hτ)
    refine le_trans hshift ?_
    push_cast
    norm_num [expTaylor, Finset.sum_range_succ, Nat.factorial]
  · rw [show ((101:ℝ)) = (((101:ℕ)):ℝ) by norm_num]
    refine (log_enclosure_nat (m := 101) (by norm_num)
      (by
        calc Real.exp ((0:ℚ) : ℝ) = 1 := by norm_num [Real.exp_zero]
          _ ≤ (((101:ℕ)):ℝ) := by norm_num) ?_).2
    have henc := exp_enclosure (x := (6152/10000 : ℚ))
      (by norm_num) (n := 10) (by norm_num)
    have hτ : |Real.exp ((6152/10000 : ℚ) : ℝ)
        - ((expTaylor (6152/10000) 10 : ℚ) : ℝ)| ≤ ((1/10^7 : ℚ) : ℝ) := by
      have hb : |((6152/10000 : ℚ) : ℝ)| ^ 10
          * (((10 : ℕ).succ : ℝ) / (((10 : ℕ).factorial : ℝ) * 10))
          ≤ ((1/10^7 : ℚ) : ℝ) := by
        rw [show |((6152/10000 : ℚ) : ℝ)| = ((6152/10000 : ℚ) : ℝ) from
          abs_of_pos (by norm_num)]
        push_cast
        norm_num [Nat.factorial]
      exact le_trans henc hb
    have hshift := exp_lower_shift (x := (46152/10000 : ℚ)) 4
      (by
        have hx : ((46152/10000 : ℚ) - (4 : ℕ) : ℚ) = 6152/10000 := by
          norm_num
        rw [hx]
        exact hτ)
      (by norm_num [expTaylor, Finset.sum_range_succ, Nat.factorial])
    refine le_trans ?_ hshift
    push_cast
    norm_num [expTaylor, Finset.sum_range_succ, Nat.factorial]

set_option maxHeartbeats 12800000 in
/-- **The tight γ enclosure**: `0.5721 < γ < 0.5824` from the `n = 100`
harmonic sandwich (`harmonic 100` kernel-evaluated; `log 100 = 2·log 10`). -/
theorem gamma_enclosure_tight :
    (5720/10000 : ℝ) < Real.eulerMascheroniConstant
      ∧ Real.eulerMascheroniConstant < 5825/10000 := by
  have hlow := Real.eulerMascheroniSeq_lt_eulerMascheroniConstant 100
  have hhigh := Real.eulerMascheroniConstant_lt_eulerMascheroniSeq' 100
  have hseq : Real.eulerMascheroniSeq 100 = harmonic 100 - Real.log 101 := by
    rw [Real.eulerMascheroniSeq]
    norm_num
  have hseq' : Real.eulerMascheroniSeq' 100 = harmonic 100 - Real.log 100 := by
    rw [Real.eulerMascheroniSeq']
    norm_num
  have hlog100 : Real.log 100 = 2 * Real.log 10 := by
    rw [show (100:ℝ) = 10^2 by norm_num, Real.log_pow]
    push_cast
    ring
  have hharm : (harmonic 100 : ℝ)
      ≤ 51874/10000 ∧ (51873/10000 : ℝ) ≤ (harmonic 100 : ℝ) := by
    constructor <;>
    · norm_num [harmonic_succ, harmonic_zero]
  obtain ⟨hharm_u, hharm_l⟩ := hharm
  have h101 := log_101_enclosure
  have h10 := log_ten_enclosure
  push_cast at h101 h10
  rw [hseq] at hlow
  rw [hseq', hlog100] at hhigh
  constructor
  · calc (5720/10000 : ℝ)
        < 51873/10000 - 46152/10000 := by norm_num
      _ ≤ harmonic 100 - Real.log 101 := by
          have := h101.2
          linarith
      _ < Real.eulerMascheroniConstant := hlow
  · calc Real.eulerMascheroniConstant
        < harmonic 100 - 2 * Real.log 10 := hhigh
      _ ≤ 51874/10000 - 2 * (23025/10000) := by
          have := h10.1
          linarith
      _ < 5825/10000 := by norm_num

end CriticalLinePhasor.DVP

section AxiomAudit
#print axioms CriticalLinePhasor.DVP.pilot_station_A
#print axioms CriticalLinePhasor.DVP.pilot_station_B
#print axioms CriticalLinePhasor.DVP.pilot_station_C
#print axioms CriticalLinePhasor.DVP.gamma_enclosure
#print axioms CriticalLinePhasor.DVP.log_pi_enclosure
#print axioms CriticalLinePhasor.DVP.log_ten_enclosure
#print axioms CriticalLinePhasor.DVP.log_101_enclosure
#print axioms CriticalLinePhasor.DVP.gamma_enclosure_tight
end AxiomAudit
