
from fractions import Fraction as F
import math, re, sys
C_LO = F(628318530717958647692, 10**20)
C_HI = F(628318530717958647694, 10**20)
# EPS now read per-witness from header (default 1/10000) inside gen()
def s(x): return f'{x.numerator}/{x.denominator}' if x.denominator != 1 else f'{x.numerator}'
def fr(x): return F(*[int(y) for y in x.split('/')]) if '/' in x else F(int(x))
def fact(n):
    r = 1
    for i in range(2, n+1): r *= i
    return r
logbr = {1: (F(0), F(0))}
for fn in ['DVPLog58Table', 'DVPLog200Table', 'DVPLog250Table', 'DVPLog500Table', 'DVPLog1000Table', 'DVPLog2000Table', 'DVPLog4000Table']:
    txt = open(f'RequestProject/{fn}.lean').read()
    for m in re.finditer(r'theorem log_br_(\d+) :\n    \(\((\S+) : ℚ\) : ℝ\) ≤ Real\.log \(\d+ : ℕ\)\n      ∧ Real\.log \(\d+ : ℕ\) ≤ \(\((\S+) : ℚ\) : ℝ\)', txt):
        logbr[int(m.group(1))] = (fr(m.group(2)), fr(m.group(3)))
def sqb(n):
    # precision must match the compiled sqrt tables: 1e-7 to 1000, 1e-8 beyond
    P = 10**8 if n > 1000 else 10**7
    x = math.exp(-0.5*math.log(n))
    a = F(int(x*P), P)
    while a**2*n > 1: a -= F(1,P)
    b = F(int(x*P)+1, P)
    while b**2*n < 1: b += F(1,P)
    return (a,b)
E_HI = F(27182818286, 10**10)
E_LO = F(27182818283, 10**10)
def expT(x): return sum(x**i/fact(i) for i in range(9))
def check_br(p, mm, lo, hi):
    return ((expT(lo - mm) + abs(lo - mm)**9 * F(10,3265920)) * E_HI**mm <= p
            and F(p) <= (expT(hi - mm) - abs(hi - mm)**9 * F(10,3265920)) * E_LO**mm)
def tight_br(p):
    x = math.log(p); mm = round(x)
    lo = F(int(x*10**8), 10**8); hi = lo + F(1,10**8)
    while not check_br(p, mm, lo, hi):
        lo -= F(1,10**8); hi += F(1,10**8)
    return lo, hi, mm
def load(prefix, name):
    lines = open(f'tmp/{prefix}_station_{name}.txt').read().strip().split('\n')
    hdr = dict(kv.split('=') for kv in lines[0].split())
    rows = []
    for line in lines[1:]:
        p = line.split()
        n = int(p[0]); d = dict(kv.split('=') for kv in p[1:])
        rows.append((n, int(d['k']), fr(d['r']), fr(d['delta']), fr(d['v'])))
    return hdr, rows
def gen(prefix, wname, rung):
    hdr, rows = load(prefix, wname)
    EPSDEN = int(hdr.get('eps', '10000')); EPS = F(1, EPSDEN)
    Mn = int(hdr['Mn']); den = int(hdr['den']); half = (den >= 2)
    sgn = int(hdr['sgn']); N = int(hdr['N']); J = int(hdr['J'])
    psi = fr(hdr['psi']); PSI = s(psi)
    Mh = F(Mn, den)
    name = (f'{Mn}o{den}' if den > 2 else f'{Mn}o2') if half else str(Mn)
    vs, ds = fr(hdr[f'u{N}']), fr(hdr[f'd{N}'])
    rs, ks = fr(hdr[f'r{N}']), int(hdr[f'k{N}'])
    vc = rows[N-1][4]
    sq = {n: sqb(n) for n in range(1, N+1)}
    term_lo = {}
    SLO = F(0)
    for (n, k, r, dq, v) in rows:
        a, b = sq[n]
        clo = v - EPS
        term_lo[n] = a*clo if clo >= 0 else b*clo
        SLO += term_lo[n]
    aN, bN = sq[N]
    Elo = -(vc+EPS)/2 - Mh*(vs+EPS)
    xq = aN if Elo > 0 else bN
    BLO = F(N)*xq*Elo/(F(1,4)+Mh**2)
    ORDER = int(hdr.get('order', '1'))
    if ORDER == 2:
        COSTQ = (bN/2 + (Mh+1)*(bN/F(N))/12
                 + (Mh+1)*(Mh+2)*(Mh+3)/48*(bN/F(N)**3 + (bN/F(N)**2)/F(5,2)))
    else:
        COSTQ = bN/2 + (Mh+1)*(Mh+2)/8*(bN/F(N)**2 + (bN/F(N))/F(3,2))
    assert SLO + BLO - COSTQ > 0, (wname, float(SLO+BLO-COSTQ))
    TEXP = f'(((({Mn}:ℕ)):ℝ)/{den})' if half else f'((({Mn}:ℕ)):ℝ)'
    MhL  = f'((({Mn}:ℕ)):ℝ)/{den}' if half else f'((({Mn}:ℕ)):ℝ)'
    MhP  = f'({Mn}:ℝ)/{den}' if half else f'({Mn}:ℝ)'
    def LARG(n):
        return f'(Real.log (({n} : ℕ)) / {den})' if half else f'Real.log (({n} : ℕ))'
    def LPUSH(n):
        return f'(Real.log ({n}:ℝ) / {den})' if half else f'Real.log ({n}:ℝ)'
    _sfx = '_second' if ORDER == 2 else ''
    core = ((f'phase_station_lower_eighth_eval{_sfx} {Mn} {N}' if den == 8 else (f'phase_station_lower_quarter_eval{_sfx} {Mn} {N}' if den == 4 else f'phase_station_lower_half_eval{_sfx} {Mn} {N}')) if half
            else f'phase_station_lower_eval{_sfx} {Mn} {N}')
    imp_last = (('DVPPhaseStationEighthEval' if den == 8 else ('DVPPhaseStationQuarterEval' if den == 4 else 'DVPPhaseStationHalfEval'))) if half else 'DVPPhaseStationEval'
    extra = 'import RequestProject.DVPSecondOrderAux\n' if ORDER == 2 else ''
    if N > 250 or Mn > 250:
        extra += 'import RequestProject.DVPLog500Table\nimport RequestProject.DVPSqrt500Table\n'
    if N > 500 or Mn > 500:
        extra += 'import RequestProject.DVPLog1000Table\nimport RequestProject.DVPSqrt1000Table\n'
    if N > 1000 or Mn > 1000:
        extra += 'import RequestProject.DVPLog2000Table\nimport RequestProject.DVPSqrt2000Table\n'
    if N > 2000 or Mn > 2000:
        extra += 'import RequestProject.DVPLog4000Table\nimport RequestProject.DVPSqrt4000Table\n'
    body = f"""import RequestProject.DVPSqrt250Table
import RequestProject.DVPLog250Table
import RequestProject.DVPSqrt200Table
import RequestProject.DVPLog200Table
{extra}import RequestProject.{imp_last}

/-!
# Station `t = {Mn}{'/2' if half else ''}` ({rung}; evaluated boundary, N = {N})
-/

open Complex Finset
open CriticalLinePhasor.ContourArgument CriticalLinePhasor.CarrierScale

noncomputable section

namespace CriticalLinePhasor.DVP

/-- The station term (opaque under `simp`/`norm_num`). -/
noncomputable def stT{name} (n : ℕ) : ℝ :=
  ((n : ℕ) : ℝ) ^ (-(1/2 : ℝ))
    * Real.cos ((({Mn} : ℕ) : ℝ) * {f'(Real.log ((n : ℕ)) / {den})' if half else 'Real.log ((n : ℕ))'} - (({PSI} : ℚ) : ℝ))

"""
    def bracket_haves(n):
        if den == 8 and n <= 500 and n >= 2 and EPSDEN > 10000:
            lo, hi, mm = tight_br(n)
            return f"""  have hbr : (({s(lo)} : ℚ) : ℝ) ≤ Real.log ({n} : ℕ)
      ∧ Real.log ({n} : ℕ) ≤ (({s(hi)} : ℚ) : ℝ) :=
    log_bracket {mm} (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [expTaylor, Finset.sum_range_succ])
      (by norm_num [expTaylor, Finset.sum_range_succ])
      (by norm_num [expTaylor, Finset.sum_range_succ])
  have hlo : (({s(lo/den)} : ℚ) : ℝ) ≤ Real.log (({n} : ℕ)) / {den} := by
    have h := hbr.1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (({n} : ℕ)) / {den} ≤ (({s(hi/den)} : ℚ) : ℝ) := by
    have h := hbr.2
    push_cast at h ⊢
    linarith
"""
        lo, hi = logbr[n]
        lo2, hi2 = s(lo/den), s(hi/den)
        return f"""  have hlo : (({lo2} : ℚ) : ℝ) ≤ Real.log (({n} : ℕ)) / {den} := by
    have h := (log_br_{n}).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (({n} : ℕ)) / {den} ≤ (({hi2} : ℚ) : ℝ) := by
    have h := (log_br_{n}).2
    push_cast at h ⊢
    linarith
"""
    for (n, k, r, dq, v) in rows:
        if half:
            body += f"""theorem st{name}_c{n} :
    |Real.cos ((({Mn} : ℕ) : ℝ) * {LARG(n)} - (({PSI} : ℚ) : ℝ))
      - (({s(v)} : ℚ) : ℝ)| ≤ ((1/{EPSDEN} : ℚ) : ℝ) := by
{bracket_haves(n)}  exact cosMulShift_eval (r := {s(r)}) (δ := {s(dq)}) (ψ := {PSI}) {Mn} {k}
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

"""
        else:
            body += f"""theorem st{name}_c{n} :
    |Real.cos ((({Mn} : ℕ) : ℝ) * {LARG(n)} - (({PSI} : ℚ) : ℝ))
      - (({s(v)} : ℚ) : ℝ)| ≤ ((1/{EPSDEN} : ℚ) : ℝ) :=
  cosMulShift_eval (r := {s(r)}) (δ := {s(dq)}) (ψ := {PSI}) {Mn} {k}
    (log_br_{n}).1 (log_br_{n}).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

"""
        clo = v - EPS
        tlo = term_lo[n]
        if clo >= 0:
            body += f"""theorem st{name}_t{n} : (({s(tlo)} : ℚ) : ℝ) ≤ stT{name} {n} := by
  have hc : (({s(clo)} : ℚ) : ℝ)
      ≤ Real.cos ((({Mn} : ℕ) : ℝ) * {LARG(n)} - (({PSI} : ℚ) : ℝ)) := by
    have h := (abs_le.mp st{name}_c{n}).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_{n}).1
  have hw2 : (({n} : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ (({s(sq[n][0])} : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc (({s(tlo)} : ℚ) : ℝ)
      = (({s(sq[n][0])} : ℚ) : ℝ) * (({s(clo)} : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

"""
        else:
            body += f"""theorem st{name}_t{n} : (({s(tlo)} : ℚ) : ℝ) ≤ stT{name} {n} := by
  have hc : (({s(clo)} : ℚ) : ℝ)
      ≤ Real.cos ((({Mn} : ℕ) : ℝ) * {LARG(n)} - (({PSI} : ℚ) : ℝ)) := by
    have h := (abs_le.mp st{name}_c{n}).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_{n}).2
  have h0 : (0:ℝ) ≤ (({n} : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc (({s(tlo)} : ℚ) : ℝ)
      = (({s(sq[n][1])} : ℚ) : ℝ) * (({s(clo)} : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

"""
    acc = term_lo[1]
    body += f"""theorem st{name}_p1 : (({s(acc)} : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 1, stT{name} (i+1) := by
  rw [Finset.sum_range_one]
  exact st{name}_t1

"""
    for j in range(2, N+1):
        acc = acc + term_lo[j]
        body += f"""theorem st{name}_p{j} : (({s(acc)} : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range {j}, stT{name} (i+1) := by
  have hsplit : (∑ i ∈ Finset.range {j}, stT{name} (i+1))
      = (∑ i ∈ Finset.range {j-1}, stT{name} (i+1)) + stT{name} {j} := by
    have h := Finset.sum_range_succ (fun i => stT{name} (i+1)) {j-1}
    simpa using h
  have hprev := st{name}_p{j-1}
  have hstep := st{name}_t{j}
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

"""
    assert acc == SLO
    if half:
        body += f"""theorem st{name}_s{N} :
    |Real.sin ((({Mn} : ℕ) : ℝ) * {LARG(N)} - (({PSI} : ℚ) : ℝ))
      - (({s(vs)} : ℚ) : ℝ)| ≤ ((1/{EPSDEN} : ℚ) : ℝ) := by
{bracket_haves(N)}  exact sinMulShift_eval (r := {s(rs)}) (δ := {s(ds)}) (ψ := {PSI}) {Mn} {ks}
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, cosTaylor, Finset.sum_range_succ, Nat.factorial])

"""
    else:
        body += f"""theorem st{name}_s{N} :
    |Real.sin ((({Mn} : ℕ) : ℝ) * {LARG(N)} - (({PSI} : ℚ) : ℝ))
      - (({s(vs)} : ℚ) : ℝ)| ≤ ((1/{EPSDEN} : ℚ) : ℝ) :=
  sinMulShift_eval (r := {s(rs)}) (δ := {s(ds)}) (ψ := {PSI}) {Mn} {ks}
    (log_br_{N}).1 (log_br_{N}).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, cosTaylor, Finset.sum_range_succ, Nat.factorial])

"""
    if ORDER == 2:
        COSTBLOCK = f"""  have hcost : (({N}:ℕ):ℝ) ^ (-(1/2:ℝ)) / 2
      + (({MhL})+1) * (({N}:ℕ):ℝ) ^ (-(3/2:ℝ)) / 12
      + (({MhL})+1) * (({MhL})+2) * (({MhL})+3) / 48
        * ((({N}:ℕ):ℝ) ^ (-(7/2:ℝ)) + (({N}:ℕ):ℝ) ^ (-(5/2:ℝ)) / (5/2))
      ≤ (({s(COSTQ)} : ℚ) : ℝ) := by
    rw [hsh.2.1, hsh.2.2, rpow_half_shift_seven (N := {N}) (by norm_num)]
    have hx := hsq.2
    have hx0 := hsq.1
    push_cast at hx hx0 ⊢
    nlinarith [hx, hx0]"""
    else:
        COSTBLOCK = f"""  have hcost : (({N}:ℕ):ℝ) ^ (-(1/2:ℝ)) / 2
      + (({MhL})+1) * (({MhL})+2) / 8
        * ((({N}:ℕ):ℝ) ^ (-(5/2:ℝ)) + (({N}:ℕ):ℝ) ^ (-(3/2:ℝ)) / (3/2))
      ≤ (({s(COSTQ)} : ℚ) : ℝ) := by
    rw [hsh.2.1, hsh.2.2]
    have hx := hsq.2
    have hx0 := hsq.1
    push_cast at hx hx0 ⊢
    nlinarith [hx, hx0]"""
    sign_stmt = (f'hardyG ({TEXP}) < 0' if sgn < 0 else f'0 < hardyG ({TEXP})')
    phi_expr = (f'(({PSI} : ℚ) : ℝ) + (({J}:ℤ)) * (2*Real.pi) - Real.pi' if sgn < 0
                else f'(({PSI} : ℚ) : ℝ) + (({J}:ℤ)) * (2*Real.pi)')
    proj = '2' if sgn < 0 else '1'
    elo_block = (f"""    have hElopos : (({s(Elo)} : ℚ) : ℝ) ≥ 0 := by
      push_cast
      norm_num""" if Elo > 0 else f"""    have hEloneg : (({s(Elo)} : ℚ) : ℝ) ≤ 0 := by
      push_cast
      norm_num""")
    body += f"""set_option maxHeartbeats 6400000 in
/-- **The certified detector sign at `t = {Mn}{'/2' if half else ''}`** (evaluated boundary). -/
theorem station_{name}_sign : {sign_stmt} := by
  have hcore := {core} (by norm_num) (by norm_num)
    (({PSI} : ℚ) : ℝ)
  have hchain := st{name}_p{N}
  have hbridge : (∑ i ∈ Finset.range {N}, stT{name} (i+1))
      = ∑ i ∈ Finset.range {N},
          (((i+1 : ℕ)) : ℝ) ^ (-(1/2 : ℝ))
            * Real.cos ((({Mn} : ℕ) : ℝ) * {f'(Real.log ((i+1 : ℕ)) / {den})' if half else 'Real.log ((i+1 : ℕ))'}
              - (({PSI} : ℚ) : ℝ)) := rfl
  rw [hbridge] at hchain
  have hsq := sq_br_{N}
  have hsh := rpow_half_shifts (N := {N}) (by norm_num)
  have hcosb := abs_le.mp st{name}_c{N}
  have hsinb := abs_le.mp st{name}_s{N}
  have hbdy_lo : (({s(BLO)} : ℚ) : ℝ)
      ≤ (({N}:ℕ):ℝ) ^ ((1/2:ℝ))
        * (-(Real.cos ((({Mn} : ℕ) : ℝ) * {LARG(N)} - (({PSI} : ℚ) : ℝ))) / 2
          - ({MhL})
            * Real.sin ((({Mn} : ℕ) : ℝ) * {LARG(N)} - (({PSI} : ℚ) : ℝ)))
        / ((1/4 : ℝ) + ({MhL}) ^ 2) := by
    rw [hsh.1]
    have hx := hsq.2
    have hx0 := hsq.1
    push_cast at hx hx0 hcosb hsinb ⊢
    have hE : -(Real.cos (({Mn}:ℝ) * {LPUSH(N)} - (({PSI} : ℚ) : ℝ))) / 2
        - ({MhP}) * Real.sin (({Mn}:ℝ) * {LPUSH(N)} - (({PSI} : ℚ) : ℝ))
        ≥ (({s(Elo)} : ℚ) : ℝ) := by
      push_cast
      nlinarith [hcosb.2, hsinb.2]
    have hsqpos : (0:ℝ) ≤ ({N}:ℝ) * (({N}:ℝ) ^ (-(1/2:ℝ))) := by
      have := Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ ({N}:ℝ)) (-(1/2:ℝ))
      positivity
    push_cast
    rw [le_div_iff₀ (by norm_num : (0:ℝ) < 1/4 + ({MhP}) ^ 2)]
    have h1 := mul_le_mul_of_nonneg_left hE hsqpos
{elo_block}
    have h2 : ({N}:ℝ) * ({s(xq)})
          * (({s(Elo)} : ℚ) : ℝ)
        ≤ ({N}:ℝ) * (({N}:ℝ) ^ (-(1/2:ℝ)))
          * (({s(Elo)} : ℚ) : ℝ) := by
      push_cast
      nlinarith [hx, hx0]
    push_cast at h1 h2 ⊢
    linarith [h1, h2]
{COSTBLOCK}
  have hm : (0:ℝ) < (({s(SLO)} : ℚ) : ℝ) + (({s(BLO)} : ℚ) : ℝ)
      - (({s(COSTQ)} : ℚ) : ℝ) := by
    push_cast
    norm_num
  have hP0 : (0:ℝ) < (Complex.exp ((({PSI} : ℚ) : ℝ) * Complex.I)
      * riemannZeta (line ({TEXP}))).re := by
    linarith [hcore, hchain, hbdy_lo, hcost, hm]
  have hP : 0 < Real.cos (({PSI} : ℚ) : ℝ)
        * (riemannZeta (line ({TEXP}))).re
      - Real.sin (({PSI} : ℚ) : ℝ)
        * (riemannZeta (line ({TEXP}))).im := by
    rw [← re_phase_eq]
    exact hP0
  have hθ30 := theta30_enclosure
  have hinc := theta_increment_enclosure_from (T₁ := (30:ℝ))
    (T := ({TEXP})) (by norm_num) (by norm_num)
  have hπ := Real.pi_pos
  have hMainM : thetaMain ({TEXP})
      = (({TEXP}) * (Real.log ({TEXP}) - Real.log 2
          - Real.log Real.pi) - ({TEXP})) / 2 := by
    rw [thetaMain, Real.log_div (by norm_num) (by positivity),
      Real.log_mul (by norm_num) hπ.ne']
    ring
  have hMain30 : thetaMain (30:ℝ)
      = ((30:ℝ) * (Real.log (30:ℝ) - Real.log 2 - Real.log Real.pi) - 30) / 2 := by
    rw [thetaMain, Real.log_div (by norm_num) (by positivity),
      Real.log_mul (by norm_num) hπ.ne']
    ring
  rw [hMainM, hMain30] at hinc
"""
    if half:
        if Mn in logbr:
            lo, hi = logbr[Mn]
            hMline = f"    have hM := log_br_{Mn}\n"
        else:
            lo, hi, mmM = tight_br(Mn)
            hMline = f"""    have hM : (({s(lo)} : ℚ) : ℝ) ≤ Real.log ({Mn} : ℕ)
        ∧ Real.log ({Mn} : ℕ) ≤ (({s(hi)} : ℚ) : ℝ) :=
      log_bracket {mmM} (by norm_num) (by norm_num) (by norm_num)
        (by norm_num [expTaylor, Finset.sum_range_succ])
        (by norm_num [expTaylor, Finset.sum_range_succ])
        (by norm_num [expTaylor, Finset.sum_range_succ])
"""
        lo2q, hi2q = s(lo - logbr[den][1]), s(hi - logbr[den][0])
        body += f"""  have hlM : (({lo2q} : ℚ) : ℝ) ≤ Real.log ({TEXP})
      ∧ Real.log ({TEXP}) ≤ (({hi2q} : ℚ) : ℝ) := by
    have hsplit : Real.log ({TEXP})
        = Real.log (((({Mn}:ℕ)):ℝ)) - Real.log {den} :=
      Real.log_div (by norm_num) (by norm_num)
{hMline}    have h2 := log_br_{den}
    rw [hsplit]
    push_cast at hM h2 ⊢
    constructor <;> linarith [hM.1, hM.2, h2.1, h2.2]
"""
    else:
        body += f"""  have hlM := log_br_{Mn}
"""
    body += f"""  have hl30 : ((34011973/10000000 : ℚ) : ℝ) ≤ Real.log (30:ℝ)
      ∧ Real.log (30:ℝ) ≤ ((17005987/5000000 : ℚ) : ℝ) := by
    have h := log_br_30
    norm_num at h ⊢
    exact h
  have hl2 : ((6931471/10000000 : ℚ) : ℝ) ≤ Real.log (2:ℝ)
      ∧ Real.log (2:ℝ) ≤ ((433217/625000 : ℚ) : ℝ) := by
    have h := log_br_2
    norm_num at h ⊢
    exact h
  have hlπ := log_pi_enclosure
  have hπ6l := Real.pi_gt_d6
  have hπ6u := Real.pi_lt_d6
  have hθb := abs_le.mp hθ30
  have hincb := abs_le.mp hinc
  have hθwin : |({phi_expr}) - theta ({TEXP})| < Real.pi / 2 := by
    rw [abs_lt]
    push_cast at hincb hlM ⊢
    constructor <;> nlinarith [hθb.1, hθb.2, hincb.1, hincb.2,
      hlM.1, hlM.2, hl30.1, hl30.2, hl2.1, hl2.2, hlπ.1, hlπ.2,
      hπ6l, hπ6u]
  have hprox := (hardyG_sign_of_proxy (t := ({TEXP}))
    (φ := {phi_expr}) hθwin).{proj}
  apply hprox
"""
    if sgn < 0:
        body += f"""  rw [show ({phi_expr})
      = (((({PSI} : ℚ)) : ℝ) - Real.pi) + (({J}:ℤ)) * (2*Real.pi) by ring,
    (cos_sin_shift (((({PSI} : ℚ)) : ℝ) - Real.pi) {J}).1,
    (cos_sin_shift (((({PSI} : ℚ)) : ℝ) - Real.pi) {J}).2]
  exact cos_sin_flip (({PSI} : ℚ) : ℝ) _ _ hP
"""
    else:
        body += f"""  rw [(cos_sin_shift ((({PSI} : ℚ)) : ℝ) {J}).1,
    (cos_sin_shift ((({PSI} : ℚ)) : ℝ) {J}).2]
  exact hP
"""
    body += f"""
end CriticalLinePhasor.DVP

section AxiomAudit
#print axioms CriticalLinePhasor.DVP.station_{name}_sign
end AxiomAudit
"""
    open(f'RequestProject/DVPStation{name}.lean','w').write(body)
    return name

if __name__ == '__main__':
    prefix = sys.argv[1]
    rung = sys.argv[2]
    for w in sys.argv[3:]:
        n = gen(prefix, w, rung)
        print(f'DVPStation{n}.lean written')
