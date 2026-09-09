#!/usr/bin/env python3
"""
att666 — T2a: where are the cusped two-ended sums' missing zeros?  (burndown 2026-09-08)
Readout F(z) = 2∫_0^U K(u) cos(zu) du, K ∈ {Φ, P_1 (Pólya), C_1, C_2, C_3}, C_N = Σ_{m≤N} g_m(|u|).
Band B = {Re z ∈ [−0.5, 60], Im z ∈ [0.05, 8]}: every zero counted there is NON-REAL (its conjugate is at the same
height below the axis).  Count by the argument principle on ∂B (adaptive), locate by Newton from a seed grid.
Full-precision composite Gauss–Legendre nodes (mpmath calc_nodes), dps = 40.
PRE-REGISTERED
  R1 Φ: 0 zeros in B.   R2 P_1: 0 zeros in B.
  R3 C_1: ≥ 10 zeros in B (its 12 missing real zeros below 60 reappear as conjugate pairs), all with Im ≥ 1.
  R4 C_2: ≥ 5 zeros in B.   R5 C_3: ≤ 1 zero in B (crossover ≈ 75 > 60).
  If C_1 shows < 10 in B, extend Im to 20 before concluding.
OUTPUT tmp/att666_results.txt
"""
import math, time
import mpmath as mp
from mpmath.calculus.quadrature import GaussLegendre
mp.mp.dps = 40
out = open("tmp/att666_results.txt", "w")
def say(*a):
    s = " ".join(str(x) for x in a); print(s); out.write(s + "\n"); out.flush()

def g(m, u):
    return (2*mp.pi**2*m**4*mp.exp(mp.mpf(9)/2*u) - 3*mp.pi*m**2*mp.exp(mp.mpf(5)/2*u))*mp.exp(-mp.pi*m**2*mp.exp(2*u))
def C(N): return lambda u: sum(g(m, u) for m in range(1, N+1))
def P1(u): return (4*mp.pi**2*mp.cosh(mp.mpf(9)/2*u) - 6*mp.pi*mp.cosh(mp.mpf(5)/2*u))*mp.exp(-2*mp.pi*mp.cosh(2*u))

# full-precision composite GL nodes on [0, 2.5]
gl = GaussLegendre(mp.mp)
base = gl.calc_nodes(6, mp.mp.prec)     # nodes on [-1,1] at working precision
U = mp.mpf(2.5); PANELS = 10
nodes, weights = [], []
for p in range(PANELS):
    a, b = U*p/PANELS, U*(p+1)/PANELS
    for x, w in base:
        nodes.append((a+b)/2 + (b-a)/2*x); weights.append((b-a)/2*w)
say("nodes: %d at dps %d" % (len(nodes), mp.mp.dps))

def make(K):
    Kw = [2*w*K(u) for u, w in zip(nodes, weights)]
    def F(z):  return sum(kw*mp.cos(z*u) for kw, u in zip(Kw, nodes))
    def dF(z): return -sum(kw*u*mp.sin(z*u) for kw, u in zip(Kw, nodes))
    return F, dF

RE0, RE1, IM0, IM1 = mp.mpf(-0.5), mp.mpf(60), mp.mpf(0.05), mp.mpf(8)
def winding(F, h=0.05):
    corners = [mp.mpc(RE0, IM0), mp.mpc(RE1, IM0), mp.mpc(RE1, IM1), mp.mpc(RE0, IM1), mp.mpc(RE0, IM0)]
    pts = []
    for a, b in zip(corners[:-1], corners[1:]):
        n = int(mp.ceil(abs(b-a)/h)); pts += [a + (b-a)*mp.mpf(i)/n for i in range(n)]
    pts.append(pts[0])
    for _ in range(5):
        vals = [F(z) for z in pts]
        d = [mp.arg(vals[i+1]/vals[i]) for i in range(len(vals)-1)]
        bad = [i for i, x in enumerate(d) if abs(x) > 0.8]
        if not bad: break
        new = []
        for i in range(len(pts)-1):
            new.append(pts[i])
            if i in bad: new += [pts[i] + (pts[i+1]-pts[i])*mp.mpf(k)/6 for k in range(1, 6)]
        new.append(pts[-1]); pts = new
    return int(mp.nint(sum(d)/(2*mp.pi)))

def locate(F, dF):
    roots = []
    seeds = [mp.mpc(re, im) for re in [1.5*i for i in range(0, 41)] for im in [0.3 + 0.7*j for j in range(0, 12)]]
    for z in seeds:
        try:
            for _ in range(30):
                f = F(z); df = dF(z)
                if df == 0: break
                step = f/df
                if abs(step) > 2: step = step/abs(step)*2
                z = z - step
                if abs(step) < mp.mpf(10)**(-20): break
        except Exception:
            continue
        if RE0 <= z.real <= RE1 and IM0 <= z.imag <= IM1 and abs(F(z)) < mp.mpf(10)**(-15)*(1 + abs(dF(z))):
            if all(abs(z - r) > 1e-8 for r in roots): roots.append(z)
    return sorted(roots, key=lambda z: z.real)

t0 = time.time()
for name, K in [("Φ", C(8)), ("P_1", P1), ("C_1", C(1)), ("C_2", C(2)), ("C_3", C(3))]:
    F, dF = make(K)
    W = winding(F)
    roots = locate(F, dF)
    say("%-4s  non-real zeros in band (winding): %2d ; located: %2d   (%.0fs)" % (name, W, len(roots), time.time()-t0))
    for r in roots[:14]:
        say("       %8.4f %+8.4f i" % (r.real, r.imag))
