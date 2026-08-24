# N=1000-segment chain generator: Table + Psum + Core + Segment for one anchor.
# Usage: python3 tmp/att296_chain_gen.py <Mn> <rung-label> <witness-file>
# Core consts derived: hns=(Mn+4)/2, hns1=(Mn+6)/2, prod=(Mn+4)(Mn+6)/4, errco=ceil(prod/8) checked vs header.
from fractions import Fraction as F
import re, glob, sys, math
def s(x): return f'{x.numerator}/{x.denominator}' if x.denominator != 1 else f'{x.numerator}'
def fr(x): return F(*[int(y) for y in x.split('/')]) if '/' in x else F(int(x))
Mn = int(sys.argv[1]); RUNG = sys.argv[2]; WFILE = sys.argv[3]
logbr = {}
for fn in ['DVPLog58Table','DVPLog200Table','DVPLog250Table','DVPLog500Table','DVPLog1000Table']:
    txt = open(f'RequestProject/{fn}.lean').read()
    for m in re.finditer(r'theorem log_br_(\d+) :\n    \(\((\S+) : ℚ\) : ℝ\) ≤ Real\.log \(\d+ : ℕ\)\n      ∧ Real\.log \(\d+ : ℕ\) ≤ \(\((\S+) : ℚ\) : ℝ\)', txt):
        logbr[int(m.group(1))] = (fr(m.group(2)), fr(m.group(3)))
wbr = {}
for fn in glob.glob('RequestProject/DVPWeights*.lean'):
    txt = open(fn).read()
    for m in re.finditer(r'theorem wbr_(\d+)_(\d+) :\n    \(\((\S+) : ℚ\) : ℝ\) ≤ [^\n]*\n[^\n]*\n?[^\n]*≤ \(\((\S+) : ℚ\) : ℝ\)', txt):
        wbr[(int(m.group(1)), int(m.group(2)))] = (fr(m.group(3)), fr(m.group(4)))
rows = {}
hdr = None
for i, line in enumerate(open(WFILE)):
    if i == 0:
        hdr = dict(kv.split('=') for kv in line.split()); continue
    p = line.split()
    d = dict(kv.split('=') for kv in p[1:])
    rows[int(p[0])] = (int(d['k']), d['r'], d['delta'], fr(d['v']))
assert int(hdr['Mn']) == Mn and int(hdr['N']) == 1000
EPSL_HDR = hdr['eps']
ERRCO = int(hdr['errco'])
prod = (Mn+4)*(Mn+6)
assert ERRCO*32 >= prod, (ERRCO, prod/32)
EPSL = EPSL_HDR; EPS = F(*[int(x) for x in EPSL.split('/')])
T = f'{Mn}o2'
# ---- Table ----
body = f"""import RequestProject.DVPCosSinEval
import RequestProject.DVPLog200Table
import RequestProject.DVPLog250Table
import RequestProject.DVPLog500Table
import RequestProject.DVPLog1000Table

/-!
# The cosine table at `t = {Mn}/2` ({RUNG}; halved brackets, N = 1000)
-/

open Finset

noncomputable section

namespace CriticalLinePhasor.DVP

"""
for n in range(2, 1001):
    k, r, dq, v = rows[n]
    lo, hi = logbr[n]
    body += f"""theorem cos{T}_br_{n} :
    |Real.cos ((({Mn} : ℕ) : ℝ) * (Real.log ({n} : ℕ) / 2)) - (({s(v)} : ℚ) : ℝ)|
      ≤ (({EPSL} : ℚ) : ℝ) := by
  have hlo : (({s(lo/2)} : ℚ) : ℝ) ≤ Real.log ({n} : ℕ) / 2 := by
    have h := (log_br_{n}).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ({n} : ℕ) / 2 ≤ (({s(hi/2)} : ℚ) : ℝ) := by
    have h := (log_br_{n}).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := {r}) (δ := {dq}) {Mn} {k}
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

"""
body += f"""end CriticalLinePhasor.DVP

section AxiomAudit
#print axioms CriticalLinePhasor.DVP.cos{T}_br_1000
end AxiomAudit
"""
open(f'RequestProject/DVPCos{T}Table.lean','w').write(body)
print(f'Table written')
# ---- Psum ----
psb = f"""import RequestProject.DVPCos{T}Table

/-!
# The cosine partial-sum floor, `t = {Mn}/2` (N = 1000)
-/

open Finset

noncomputable section

namespace CriticalLinePhasor.DVP

/-- The cosine sequence of the `t = {Mn}/2` segment certificate. -/
def cos{T}c (n : ℕ) : ℝ := Real.cos ((({Mn}:ℕ):ℝ) * (Real.log n / 2))

"""
acc = rows[11][3] - EPS
minacc = acc
psb += f"""theorem psum{T}_11 : (({s(acc)} : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 11, cos{T}c k := by
  rw [Finset.Icc_self, Finset.sum_singleton]
  have h : -(({EPSL} : ℚ) : ℝ) ≤ cos{T}c 11 - (({s(rows[11][3])} : ℚ) : ℝ) :=
    (abs_le.mp cos{T}_br_11).1
  push_cast at h ⊢
  linarith

"""
for j in range(12, 1001):
    v = rows[j][3]
    acc = acc + v - EPS
    minacc = min(minacc, acc)
    psb += f"""theorem psum{T}_{j} : (({s(acc)} : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 {j}, cos{T}c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 {j}, cos{T}c k)
      = (∑ k ∈ Finset.Icc 11 {j-1}, cos{T}c k) + cos{T}c {j} := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := {j-1}) (by norm_num) cos{T}c
    simpa using h
  have hprev := psum{T}_{j-1}
  have hstep : -(({EPSL} : ℚ) : ℝ) ≤ cos{T}c {j} - (({s(v)} : ℚ) : ℝ) :=
    (abs_le.mp cos{T}_br_{j}).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

"""
C1000 = acc
print(f'min prefix {float(minacc):+.4f}; C1000 = {s(C1000)} (header {hdr["C1000"]})')
assert minacc > 0 and s(C1000) == hdr['C1000']
psb += f"""set_option maxHeartbeats 6400000 in
set_option maxRecDepth 32768 in
theorem psum{T}_floor : ∀ j : ℕ, 11 ≤ j → j ≤ 1000 →
    ((0 : ℚ) : ℝ) ≤ ∑ k ∈ Finset.Icc 11 j, cos{T}c k := by
  intro j hj1 hj2
  interval_cases j
"""
for j in range(11, 1001):
    psb += f'  · exact le_trans (by norm_num) psum{T}_{j}\n'
psb += f"""
end CriticalLinePhasor.DVP

section AxiomAudit
#print axioms CriticalLinePhasor.DVP.psum{T}_floor
#print axioms CriticalLinePhasor.DVP.psum{T}_1000
end AxiomAudit
"""
open(f'RequestProject/DVPCos{T}Psum.lean','w').write(psb)
print('Psum written')
# ---- Core (transform of the 581o2 core, /2-forms kept) ----
src = open('RequestProject/DVPSegment581o2Core.lean').read()
out = src.replace('581', str(Mn))
out = out.replace('rung-290.5', RUNG)
out = out.replace('585/2', f'{Mn+4}/2')
out = out.replace('587/2', f'{Mn+6}/2')
out = out.replace('343395/4', f'{prod}/4')
out = out.replace('10733', str(ERRCO))
out = out.replace('500', '1000')
out = out.replace('(1000/' + str(Mn), '(2000/' + str(Mn))
out = out.replace('maxRecDepth 16384', 'maxRecDepth 32768')
assert '343395' not in out and '10733' not in out and '585/2' not in out and '6931' not in out
open(f'RequestProject/DVPSegment{T}Core.lean','w').write(out)
print('Core written')
# ---- Segment ----
COST = F(2000,Mn)
intervals = [(5,6),(6,7),(7,9),(9,11),(11,14),(14,17),(17,20)]
lit = {5:'1/2',6:'3/5',7:'7/10',9:'9/10',11:'11/10',14:'7/5',17:'17/10',20:'2'}
div_lit = {5:'3/2',6:'8/5',7:'17/10',9:'19/10',11:'21/10',14:'12/5',17:'27/10'}
sb = f"""import RequestProject.DVPSegment{T}Core
import RequestProject.DVPWeights289o2
import RequestProject.DVPWeights581o2
import RequestProject.DVPWeights1000col
import RequestProject.DVPWeights63
import RequestProject.DVPWeights74
import RequestProject.DVPWeights81

/-!
# Segment positivity at `t = {Mn}/2`: {RUNG} (seven σ-intervals, N = 1000)
-/

open Complex Finset

noncomputable section

namespace CriticalLinePhasor.DVP

"""
for idx, (a, b) in enumerate(intervals, start=1):
    terms = {}
    tblock = ''
    for n in range(2, 11):
        v = rows[n][3]
        clo = v - EPS
        tblock += f"""  have hc{n} : (({s(clo)} : ℚ) : ℝ) ≤ cos{T}c {n} := by
    have h : -(({EPSL} : ℚ) : ℝ) ≤ cos{T}c {n} - (({s(v)} : ℚ) : ℝ) :=
      (abs_le.mp cos{T}_br_{n}).1
    push_cast at h ⊢
    linarith
"""
        if clo >= 0:
            wlo = wbr[(n, b)][0]
            tlo = wlo*clo
            terms[n] = tlo
            tblock += f"""  have hterm{n} : (({s(tlo)} : ℚ) : ℝ)
      ≤ (({n}:ℕ) : ℝ) ^ (-σ) * cos{T}c {n} := by
    have hwlo : (({s(wlo)} : ℚ) : ℝ) ≤ (({n}:ℕ) : ℝ) ^ (-σ) := by
      refine le_trans (wbr_{n}_{b}).1 ?_
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      push_cast
      linarith
    have hwhi : (({n}:ℕ) : ℝ) ^ (-σ) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by linarith)
    have hq0 : (0:ℝ) ≤ (({s(wlo)} : ℚ) : ℝ) := by push_cast; norm_num
    have hkey := (mul_lower_of_bracket hwlo hwhi hq0 hc{n}).1
      (by push_cast; norm_num)
    calc (({s(tlo)} : ℚ) : ℝ)
        = (({s(wlo)} : ℚ) : ℝ) * (({s(clo)} : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
"""
        else:
            whi = wbr[(n, a)][1]
            tlo = whi*clo
            terms[n] = tlo
            tblock += f"""  have hterm{n} : (({s(tlo)} : ℚ) : ℝ)
      ≤ (({n}:ℕ) : ℝ) ^ (-σ) * cos{T}c {n} := by
    have hw : (({n}:ℕ) : ℝ) ^ (-σ) ≤ (({s(whi)} : ℚ) : ℝ) := by
      refine le_trans ?_ (wbr_{n}_{a}).2
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      push_cast
      linarith
    have h0 : (0:ℝ) ≤ (({n}:ℕ) : ℝ) ^ (-σ) := Real.rpow_nonneg (by norm_num) _
    have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc{n}).2
      (by push_cast; norm_num)
    calc (({s(tlo)} : ℚ) : ℝ)
        = (({s(whi)} : ℚ) : ℝ) * (({s(clo)} : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
"""
    w11hi = wbr[(11, a)][1]
    w500lo = wbr[(1000, b)][0]
    w500hi_a = wbr[(1000, a)][1]
    rp2hi = wbr[(1000, a+20)][1]
    rp3hi = wbr[(1000, a+10)][1]
    htail_c = w500lo*C1000
    floor = 1 + sum(terms.values()) + htail_c - w500hi_a*(COST+F(1,2)) - ERRCO*(rp2hi + rp3hi/(1+F(a,10)))
    print(f'interval {idx} [{lit[a]},{lit[b]}]: floor = {float(floor):+.4f}')
    assert floor > F(1,5), (idx, float(floor))
    sb += f"""set_option maxRecDepth 32768 in
set_option maxHeartbeats 3200000 in
theorem seg{T}_interval_{idx} {{σ : ℝ}} (ha : ({lit[a]}:ℝ) ≤ σ) (hb : σ ≤ ({lit[b]}:ℝ)) :
    (1/5 : ℝ) ≤ (riemannZeta (↑σ + ↑(((({Mn}:ℕ)):ℝ)/2) * Complex.I)).re := by
  have h1 : (1/2 : ℝ) ≤ σ := by linarith
  have h2 : σ ≤ 2 := by linarith
  have hcore := re_zeta{T}_lower h1 h2
{tblock}  have hanti : ∀ k : ℕ, 11 ≤ k →
      (((k+1:ℕ)) : ℝ) ^ (-σ) ≤ ((k:ℕ) : ℝ) ^ (-σ) := by
    intro k hk
    apply rpow_neg_anti
    · exact_mod_cast (by omega : 1 ≤ k)
    · push_cast
      linarith
    · linarith
  have hnn : ∀ k : ℕ, 11 ≤ k → (0:ℝ) ≤ ((k:ℕ) : ℝ) ^ (-σ) :=
    fun k _ => Real.rpow_nonneg (Nat.cast_nonneg k) _
  have habel := abel_icc_lower (c := cos{T}c)
    (w := fun n : ℕ => ((n:ℕ) : ℝ) ^ (-σ))
    (M := 11) (Cmin := ((0 : ℚ) : ℝ))
    500 (by norm_num) hanti hnn psum{T}_floor
  have hw11 : ((11:ℕ) : ℝ) ^ (-σ) ≤ (({s(w11hi)} : ℚ) : ℝ) := by
    refine le_trans ?_ (wbr_11_{a}).2
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    push_cast
    linarith
  have hw1000lo : (({s(w500lo)} : ℚ) : ℝ) ≤ ((1000:ℕ) : ℝ) ^ (-σ) := by
    refine le_trans (wbr_1000_{b}).1 ?_
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    push_cast
    linarith
  have htail : (({s(htail_c)} : ℚ) : ℝ)
      ≤ ∑ n ∈ Finset.Icc (11:ℕ) 1000, (((n:ℕ) : ℝ) ^ (-σ) * cos{T}c n) := by
    refine le_trans ?_ habel
    have hC1000 := psum{T}_1000
    have hx1 : (({s(w11hi)} : ℚ) : ℝ) * ((0 : ℚ) : ℝ)
        ≤ ((11:ℕ) : ℝ) ^ (-σ) * ((0 : ℚ) : ℝ) :=
      mul_le_mul_of_nonpos_right hw11 (by push_cast; norm_num)
    have hx2 : (({s(w500lo)} : ℚ) : ℝ)
          * ((({s(C1000)} : ℚ) : ℝ) - ((0 : ℚ) : ℝ))
        ≤ ((1000:ℕ) : ℝ) ^ (-σ)
          * ((∑ k ∈ Finset.Icc (11:ℕ) 1000, cos{T}c k)
            - ((0 : ℚ) : ℝ)) := by
      apply mul_le_mul hw1000lo ?_ ?_ (Real.rpow_nonneg (by norm_num) _)
      · linarith [hC500]
      · push_cast
        norm_num
    push_cast at hx1 hx2 ⊢
    nlinarith [hx1, hx2]
  have hcost1 : (1000 : ℝ) ^ (-σ) * (2000/{Mn} + 1/2)
      ≤ (({s(w500hi_a)} : ℚ) : ℝ) * (2000/{Mn} + 1/2) := by
    apply mul_le_mul_of_nonneg_right ?_ (by norm_num)
    have hbr := (wbr_1000_{a}).2
    have hexp : (-(((({a}:ℕ)) : ℝ) / ((((10:ℕ))) : ℝ))) = (-({a}/10) : ℝ) := by
      norm_num
    have hbase : (((1000:ℕ)) : ℝ) = (1000 : ℝ) := by norm_num
    rw [hexp, hbase] at hbr
    refine le_trans ?_ hbr
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    linarith
  have hrp2 : (1000 : ℝ) ^ (-σ - 2) ≤ (({s(rp2hi)} : ℚ) : ℝ) := by
    have hbr := (wbr_1000_{a+20}).2
    have hexp : (-(((({a+20}:ℕ)) : ℝ) / ((((10:ℕ))) : ℝ))) = (-({a+20}/10) : ℝ) := by
      norm_num
    have hbase : (((1000:ℕ)) : ℝ) = (1000 : ℝ) := by norm_num
    rw [hexp, hbase] at hbr
    refine le_trans ?_ hbr
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    linarith
  have hrp3 : (1000 : ℝ) ^ (-σ - 1) / (σ + 1)
      ≤ (({s(rp3hi)} : ℚ) : ℝ) / ({div_lit[a]}) := by
    have hnum : (1000 : ℝ) ^ (-σ - 1) ≤ (({s(rp3hi)} : ℚ) : ℝ) := by
      have hbr := (wbr_1000_{a+10}).2
      have hexp : (-(((({a+10}:ℕ)) : ℝ) / ((((10:ℕ))) : ℝ))) = (-({a+10}/10) : ℝ) := by
        norm_num
      have hbase : (((1000:ℕ)) : ℝ) = (1000 : ℝ) := by norm_num
      rw [hexp, hbase] at hbr
      refine le_trans ?_ hbr
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      linarith
    apply div_le_div₀ (by push_cast; norm_num) hnum (by norm_num) (by linarith)
  have hsplitsum : ∑ n ∈ Finset.Icc (2:ℕ) 1000, (((n:ℕ) : ℝ) ^ (-σ) * cos{T}c n)
      = (∑ n ∈ Finset.Icc (2:ℕ) 10, (((n:ℕ) : ℝ) ^ (-σ) * cos{T}c n))
        + ∑ n ∈ Finset.Icc (11:ℕ) 1000, (((n:ℕ) : ℝ) ^ (-σ) * cos{T}c n) := by
    rw [show Finset.Icc (2:ℕ) 1000
        = Finset.Icc (2:ℕ) 10 ∪ Finset.Icc (11:ℕ) 1000 by decide]
    exact Finset.sum_union (by decide)
  have hexpand : ∑ n ∈ Finset.Icc (2:ℕ) 10, (((n:ℕ) : ℝ) ^ (-σ) * cos{T}c n)
      = (((2:ℕ) : ℝ) ^ (-σ) * cos{T}c 2) + (((3:ℕ) : ℝ) ^ (-σ) * cos{T}c 3)
        + (((4:ℕ) : ℝ) ^ (-σ) * cos{T}c 4) + (((5:ℕ) : ℝ) ^ (-σ) * cos{T}c 5)
        + (((6:ℕ) : ℝ) ^ (-σ) * cos{T}c 6) + (((7:ℕ) : ℝ) ^ (-σ) * cos{T}c 7)
        + (((8:ℕ) : ℝ) ^ (-σ) * cos{T}c 8) + (((9:ℕ) : ℝ) ^ (-σ) * cos{T}c 9)
        + (((10:ℕ) : ℝ) ^ (-σ) * cos{T}c 10) := by
    rw [show Finset.Icc (2:ℕ) 10 = {{2, 3, 4, 5, 6, 7, 8, 9, 10}} by decide]
    rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_singleton]
    ring
  rw [hsplitsum, hexpand] at hcore
  push_cast at hterm2 hterm3 hterm4 hterm5 hterm6 hterm7 hterm8 hterm9 hterm10 htail hcost1 hrp2 hrp3 hcore ⊢
  linarith [hcore, hterm2, hterm3, hterm4, hterm5, hterm6, hterm7, hterm8,
    hterm9, hterm10, htail, hcost1, hrp2, hrp3]

"""
sb += f"""set_option maxRecDepth 32768 in
/-- **Segment positivity at the anchor {Mn}/2.** -/
theorem segment{T}_re_pos {{σ : ℝ}} (h1 : (1/2:ℝ) ≤ σ) (h2 : σ ≤ 2) :
    (1/5 : ℝ) ≤ (riemannZeta (↑σ + ↑(((({Mn}:ℕ)):ℝ)/2) * Complex.I)).re := by
  rcases le_total σ (3/5 : ℝ) with hc | hc
  · exact seg{T}_interval_1 h1 hc
  rcases le_total σ (7/10 : ℝ) with hc2 | hc2
  · exact seg{T}_interval_2 hc hc2
  rcases le_total σ (9/10 : ℝ) with hc3 | hc3
  · exact seg{T}_interval_3 hc2 hc3
  rcases le_total σ (11/10 : ℝ) with hc4 | hc4
  · exact seg{T}_interval_4 hc3 hc4
  rcases le_total σ (7/5 : ℝ) with hc5 | hc5
  · exact seg{T}_interval_5 hc4 hc5
  rcases le_total σ (17/10 : ℝ) with hc6 | hc6
  · exact seg{T}_interval_6 hc5 hc6
  exact seg{T}_interval_7 hc6 h2

end CriticalLinePhasor.DVP

section AxiomAudit
#print axioms CriticalLinePhasor.DVP.segment{T}_re_pos
end AxiomAudit
"""
open(f'RequestProject/DVPSegment{T}.lean','w').write(sb)
print('Segment written')
