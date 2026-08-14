"""VARIANT: the certified baseline with EVERYTHING multiplied by pi/3.

Same 54 quantities as zeta23_baseline.py, same paper targets.  Each row prints:
    baseline value | that value x pi/3 | paper's printed target | which one matches.
No interpretation, no selection.  Every computed quantity is scaled.
"""
import math

C = math.pi/3
def H(l):  return 2.0 - 1.0/l - l/3.0
def Hd(l): return (1.0 + H(l))/2.0
def F(l):  return l/(1.0 + l*l/3.0)

rows = []
def q(name, base, want, tol):
    """record: quantity, baseline, baseline*pi/3, paper target"""
    rows.append((name, base, base*C, want, tol))

# ---- (1.3) the three laws -------------------------------------------------------------
q("H(1)",            H(1.0),            2/3,    1e-4)
q("Hd(1)",           Hd(1.0),           5/6,    1e-4)
q("F(1)",            F(1.0),            0.75,   1e-4)
q("3 - sqrt(6)",     3-math.sqrt(6),    0.5505, 1e-4)

# ---- section 8(2) ---------------------------------------------------------------------
S82 = [((9000,10000),0.70,5.12,168,0.602), ((9000,10000),0.85,6.22,504,0.685),
       ((9000,10000),1.00,7.32,1510,0.750),((48000,50000),0.85,7.62,2033,0.685),
       ((48000,50000),1.00,8.96,7797,0.750),((998000,1000000),0.85,10.18,26374,0.685),
       ((998000,1000000),1.00,11.98,158996,0.750)]
for (T1,T2),lam,Lp,Xp,Fp in S82:
    l = math.log(math.sqrt(T1*T2)/(2*math.pi)); L = lam*l
    t = f"8(2) [{T1},{T2}] lam={lam:.2f}"
    q(f"{t}  l",      l,           Lp/lam,  5e-3)
    q(f"{t}  L",      L,           Lp,      5e-3)
    q(f"{t}  X",      math.exp(L), Xp,      max(2,0.002*Xp))
    q(f"{t}  F(lam)", F(lam),      Fp,      1e-3)

# ---- section 8(4) ---------------------------------------------------------------------
S84 = [(2000.0,0.571,2.225,708,1834,0.368),(2000.0,0.150,4.409,1403,1834,0.640),
       (1e4,0.501,3.314,5274,11734,0.421),(1e4,0.150,5.640,8976,11734,0.640)]
for T,eta_p,L0p,dp,Np,Fp in S84:
    l = math.log(T/(2*math.pi))
    eta = 1/math.log(l) if eta_p in (0.571,0.501) else eta_p
    L0 = (1-eta)*0.9*l; lam0 = (1-eta)*0.9
    t = f"8(4) T={T:g} eta={eta_p}"
    q(f"{t}  L0",       L0,                    L0p, 2e-3)
    q(f"{t}  d",        math.floor(T*L0/(2*math.pi)), dp, 1)
    q(f"{t}  N=Tl/2pi", T*l/(2*math.pi),       Np,  1)
    q(f"{t}  F(lam0)",  F(lam0),               Fp,  1e-3)
    q(f"{t}  eta",      eta,                   eta_p, 1e-3)

# ---- headline constants ---------------------------------------------------------------
q("Thm A/B  H(1)",     H(1.0),          0.6667, 1e-4)
q("Thm C   Hd(1)",     Hd(1.0),         0.8333, 1e-4)
q("prior on-line 5/12", 5/12,           0.4167, 1e-4)
q("prior distinct",     0.6603,         0.6603, 1e-4)
q("Thm D optimised",    0.6725,         0.6725, 1e-4)
q("Rmk 1.1 ceiling",    0.68185,        0.68185,1e-5)
q("c(GL2) = 6/13",      0.5/(1+0.25/3), 6/13,   1e-6)

# ---- report ---------------------------------------------------------------------------
nb = ns = 0
print("=" * 108)
print(f"{'quantity':<34}{'baseline':>13}{'x pi/3':>14}{'paper target':>15}   matches")
print("=" * 108)
for name, base, scaled, want, tol in rows:
    ok_b = abs(base - want) <= tol
    ok_s = abs(scaled - want) <= tol
    nb += ok_b; ns += ok_s
    m = "BASELINE" if ok_b and not ok_s else ("x pi/3" if ok_s and not ok_b else
        ("both" if ok_b else "NEITHER"))
    print(f"{name:<34}{base:>13.4f}{scaled:>14.4f}{want:>15.4f}   {m}")
print("=" * 108)
n = len(rows)
print(f"baseline matches paper : {nb}/{n}")
print(f"x pi/3   matches paper : {ns}/{n}")
print("=" * 108)
