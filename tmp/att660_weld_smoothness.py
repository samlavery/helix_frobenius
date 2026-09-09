#!/usr/bin/env python3
"""
att660 — is weld smoothness the mechanism?  Truncations of the fiber kernel with a CUSPED weld versus a SMOOTH weld,
same site count N, and the count of non-real zeros of their readouts F(z) = 2∫_0^U K(u) cos(zu) du in the box
Re z ∈ [0, 60], |Im z| ≤ 0.8 (argument principle on the rectangle; real zeros by sign changes on the axis).

  cusped   C_N(u) = Σ_{m≤N} g_m(|u|),  g_m(u) = (2π²m⁴e^{9u/2} − 3πm²e^{5u/2}) e^{−πm²e^{2u}}   (two-ended sites; Φ = C_∞)
  smooth   P_N(u) = Σ_{m≤N} (4π²m⁴ cosh(9u/2) − 6πm² cosh(5u/2)) e^{−2πm² cosh 2u}           (Pólya-type product weld)
  control  Φ itself (C_8), and Pólya's P_1 (real-rooted by Pólya's theorem — positive control).
PRE-REGISTERED
  Q1 Φ (C_8): 0 non-real zeros in the box (RH in range).  P_1: 0 non-real zeros (Pólya).
  Q2 C_1, C_2, C_3: non-real zeros present, the lowest one moving UP with N (residual cusp ∝ g_{N+1}′(0⁺) ~ 2e−2, 4e−8, 7e−17
     against Ξ ~ e^{−πt/4}: predicted onset t ≈ 19 (C_1), ≈ 37 (C_2), ≈ 75 > 60 so none for C_3 in the box).
  Q3 P_2, P_3 (smooth weld, no cusp): prediction — fewer non-real zeros than C_N at the same N; if ZERO, weld smoothness
     is the mechanism at truncation level (closest source: Hejhal 1990 on Pólya-type approximants — not re-read).
OUTPUT tmp/att660_results.txt
"""
import math, time
import mpmath as mp
mp.mp.dps = 30
out = open("tmp/att660_results.txt", "w")
def say(*a):
    s = " ".join(str(x) for x in a); print(s); out.write(s + "\n"); out.flush()

def g(m, u):
    return (2*mp.pi**2*m**4*mp.exp(mp.mpf(9)/2*u) - 3*mp.pi*m**2*mp.exp(mp.mpf(5)/2*u))*mp.exp(-mp.pi*m**2*mp.exp(2*u))
def C(N): return lambda u: sum(g(m, abs(u)) for m in range(1, N+1))
def P(N): return lambda u: sum((4*mp.pi**2*m**4*mp.cosh(mp.mpf(9)/2*u) - 6*mp.pi*m**2*mp.cosh(mp.mpf(5)/2*u))*mp.exp(-2*mp.pi*m**2*mp.cosh(2*u)) for m in range(1, N+1))

# composite Gauss–Legendre on [0, U]
U = 4; PANELS = 16; ORDER = 40
nodes, weights = [], []
gl_x, gl_w = zip(*[(x, w) for x, w in zip(*mp.gauss_legendre_nodes(ORDER))]) if hasattr(mp, "gauss_legendre_nodes") else (None, None)
if gl_x is None:
    # fall back: nodes via mp.legendre roots
    import numpy as np
    xs, ws = np.polynomial.legendre.leggauss(ORDER)
    gl_x, gl_w = [mp.mpf(float(x)) for x in xs], [mp.mpf(float(w)) for w in ws]
for p in range(PANELS):
    a, b = mp.mpf(U)*p/PANELS, mp.mpf(U)*(p+1)/PANELS
    for x, w in zip(gl_x, gl_w):
        nodes.append((a+b)/2 + (b-a)/2*x); weights.append((b-a)/2*w)

def make_F(K):
    Kw = [2*w*K(u) for u, w in zip(nodes, weights)]
    def F(z):
        return sum(kw*mp.cos(z*u) for kw, u in zip(Kw, nodes))
    return F

def count_zeros(F, T=60, H=0.8, h=0.05):
    # real zeros on [0,T] by sign changes
    ts = [mp.mpf(i)*h for i in range(int(T/h)+1)]
    vals = [F(t).real for t in ts]
    real = sum(1 for i in range(len(vals)-1) if vals[i]*vals[i+1] < 0)
    # winding on rectangle [−0.5, T] × [−H, H] (avoid the axis point 0 where F is real and nonzero)
    corners = [mp.mpc(-0.5, -H), mp.mpc(T, -H), mp.mpc(T, H), mp.mpc(-0.5, H), mp.mpc(-0.5, -H)]
    pts = []
    for a, b in zip(corners[:-1], corners[1:]):
        n = int(mp.ceil(abs(b-a)/h))
        pts += [a + (b-a)*mp.mpf(i)/n for i in range(n)]
    pts.append(pts[0])
    for _ in range(4):
        vals = [F(z) for z in pts]
        d = [mp.arg(vals[i+1]/vals[i]) for i in range(len(vals)-1)]
        bad = [i for i, x in enumerate(d) if abs(x) > 0.8]
        if not bad: break
        new = []
        for i in range(len(pts)-1):
            new.append(pts[i])
            if i in bad:
                new += [pts[i] + (pts[i+1]-pts[i])*mp.mpf(k)/6 for k in range(1, 6)]
        new.append(pts[-1]); pts = new
    W = int(mp.nint(sum(d)/(2*mp.pi)))
    return real, W

t0 = time.time()
say("box Re∈[0,60], |Im|≤0.8 ; quadrature %d nodes on [0,%d], dps=%d" % (len(nodes), U, mp.mp.dps))
for name, K in [("Φ (C_8)", C(8)), ("P_1 Pólya", P(1)), ("C_1", C(1)), ("C_2", C(2)), ("C_3", C(3)), ("P_2", P(2)), ("P_3", P(3))]:
    F = make_F(K)
    r, W = count_zeros(F)
    say("   %-10s real zeros on axis: %2d ; winding (all zeros in box): %2d ; NON-REAL: %2d   (%.0fs)" % (name, r, W, W - r, time.time()-t0))
