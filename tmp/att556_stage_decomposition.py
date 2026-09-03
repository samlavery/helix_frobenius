#!/usr/bin/env python3
"""
att556 — item 1 as construction: the θ-stage decomposed into BULK (the completed fiber, ξ) minus the
FRONT TERM (the growth front's boundary), the transition where the escort pair forms, and a
continuous-U scan of the pair count.

  Ξ_U(z) = 2∫_0^U Φ(u) cos(zu) du = Ξ(z) − R_U(z),   Ξ(z) = ξ(½+iz) (bulk),   R_U(z) = 2∫_U^∞ Φ(u)cos(zu)du (front term)
  Φ(u) = 4 Σ_n (2π²n⁴e^{9u/2} − 3πn²e^{5u/2}) e^{−πn²e^{2u}}

(A) EXACT: with v = e^{2u},  R_U(z) = Σ_n Σ_± [4π²(πn²)^{−(9/4 ± iz/2)} Γ(9/4 ± iz/2, πn²e^{2U})
                                        − 6π(πn²)^{−(5/4 ± iz/2)} Γ(5/4 ± iz/2, πn²e^{2U})]
    (upper incomplete gammas); Ξ_U is the same sum with LOWER incomplete gammas.  Check vs quadrature.
(B) FRONT-TERM MODEL near and above the front: Φ(u) ≈ Φ(U)e^{−λ(u−U)}, λ = −Φ′(U)/Φ(U), gives
    R_U(z) ≈ Φ(U)[e^{izU}/(λ − iz) + e^{−izU}/(λ + iz)] — real zeros at tan(tU) = −λ/t, one per π/U.
    Above the front the bulk is exponentially smaller (|Ξ(t+iy)| ≲ C t^{7/4+y/2} e^{−πt/4}), so by
    Rouché every zero there is a (real) zero of the front term.  Check: relative error of the model.
(C) THE TRANSITION: the pair is where bulk and front term balance, Ξ(z) = R_U(z) with Im z ≠ 0.
    Solve the balance equation with the EXACT bulk (mpmath ξ) and the MODEL front term; compare to
    the census pairs (14.54+2.36i, 21.34+0.35i, 31.28+1.11i, 44.81+6.94i, 83.02+0.82i).
(D) CONTINUOUS U SCAN, U = 0.5 … 1.6 step 0.05: count zeros in the front window
    Re ∈ [0.6 t*, 1.6 t*], Im ∈ [−10, 10] minus real zeros; track (t*, y*) by continuation.
PRE-REGISTERED: P3 (A) matches quadrature to 1e−25 relative; P4 (B) model within 2% of exact R_U on
[t*, 3t*]; P5 (C) predicts each census pair to 1% in t and 15% in y; P1 (D) exactly one pair at EVERY
U on the grid — if the count is 0 or ≥ 2 at any U, the "exactly one pair per stage" claim DIES there
and the U is reported; P2 y*(U) varies continuously (no creation/annihilation on the axis).
OUTPUT tmp/att556_results.txt
"""
import sys, math, time
import mpmath as mp

out = open("tmp/att556_results.txt", "a")
def say(*a):
    s = " ".join(str(x) for x in a); print(s, flush=True); out.write(s + "\n"); out.flush()

def setup(U, dps):
    mp.mp.dps = dps; PI = mp.pi; U = mp.mpf(U)
    def phi(u):
        e2 = mp.exp(2*u); e9 = mp.exp(mp.mpf(9)/2*u); e5 = mp.exp(mp.mpf(5)/2*u)
        return 4*mp.fsum((2*PI**2*n**4*e9 - 3*PI*n**2*e5)*mp.exp(-PI*n*n*e2) for n in range(1, 16))
    def dphi(u):
        return mp.diff(phi, u)
    nodes = mp.calculus.quadrature.GaussLegendre(mp.mp).get_nodes(mp.mpf(0), U, 7, mp.mp.prec)
    PW = [(x, phi(x)*w) for (x, w) in nodes]
    xi_stage = lambda z: 2*mp.fsum(pw*mp.cos(z*x) for (x, pw) in PW)
    # the house Φ carries a factor 4 relative to Titchmarsh's: 2∫_0^∞ Φ cos(zu) du = 2·ξ(½+iz) (measured ratio 2.000)
    xi_bulk = lambda z: 2*(mp.mpf(1)/2*(mp.mpf(1)/2+1j*z)*(mp.mpf(1)/2+1j*z-1)*mp.pi**(-(mp.mpf(1)/2+1j*z)/2)*mp.gamma((mp.mpf(1)/2+1j*z)/2)*mp.zeta(mp.mpf(1)/2+1j*z))
    lam = -dphi(U)/phi(U)
    def R_exact(z, nmax=8):
        s = mp.mpc(0)
        for n in range(1, nmax + 1):
            x = PI*n*n*mp.exp(2*U)
            for sg in (+1, -1):
                a1 = mp.mpf(9)/4 + sg*1j*z/2; a2 = mp.mpf(5)/4 + sg*1j*z/2
                s += 4*PI**2*n**4*(PI*n*n)**(-a1)*mp.gammainc(a1, x) - 6*PI*n**2*(PI*n*n)**(-a2)*mp.gammainc(a2, x)
        return s
    def R_model(z):
        return phi(U)*(mp.exp(1j*z*U)/(lam - 1j*z) + mp.exp(-1j*z*U)/(lam + 1j*z))
    return dict(U=U, phi=phi, lam=lam, xi_stage=xi_stage, xi_bulk=xi_bulk, R_exact=R_exact, R_model=R_model)

def newton(f, z0, tol_exp):
    z = mp.mpc(z0)
    for _ in range(120):
        fz = f(z); h = mp.mpf(10)**(-(mp.mp.dps//2))
        df = (f(z + h) - f(z - h))/(2*h)
        if df == 0: break
        st = fz/df; z -= st
        if abs(st) < mp.mpf(10)**(-tol_exp): break
    return z

def winding(f, a, b, n):
    PI = mp.pi
    for _ in range(4):
        tot = mp.mpf(0); prev = None; ok = True
        for k in range(n + 1):
            z = a + (b - a)*mp.mpf(k)/n; ph = mp.arg(f(z))
            if prev is not None:
                d = ph - prev
                while d > PI: d -= 2*PI
                while d < -PI: d += 2*PI
                if abs(d) > PI/2: ok = False; break
                tot += d
            prev = ph
        if ok: return tot
        n *= 2
    raise RuntimeError("winding")

def box_count(f, T0, T1, H, per_unit=20):
    c = [mp.mpc(T0, -H), mp.mpc(T1, -H), mp.mpc(T1, H), mp.mpc(T0, H), mp.mpc(T0, -H)]
    ns = [max(20, int((T1 - T0)*per_unit)), max(40, int(2*H*per_unit))]*2
    return int(mp.nint(sum(winding(f, a, b, n) for (a, b), n in zip(zip(c[:-1], c[1:]), ns))/(2*mp.pi)))

def real_count(f, T0, T1, step):
    n = int((T1 - T0)/step) + 1; prev = None; cnt = 0
    for k in range(n):
        v = f(mp.mpc(T0 + k*step, 0)).real
        if prev is not None and v*prev < 0: cnt += 1
        prev = v
    return cnt

mode = sys.argv[1] if len(sys.argv) > 1 else "ABC"

if "A" in mode or "B" in mode or "C" in mode:
    census = {0.6: (14.53643777, 2.3607908), 0.8: (21.33629521, 0.35242542), 1.0: (31.27936586, 1.1095835),
              1.2: (44.81182684, 6.9373268), 1.5: (83.01725804, 0.8247056)}
    say("=== (A)(B)(C) for the five census stages")
    for U, (tp, yp) in census.items():
        tstar = 4*math.exp(2*U); dps = int(30 + math.pi*tstar/(4*math.log(10)) + 12)
        S = setup(U, dps)
        # (A) exactness: stage = bulk − R_exact
        errs = []
        for z in (mp.mpc(0.5*tstar, 0), mp.mpc(tstar, 0.7), mp.mpc(tp, yp), mp.mpc(2*tstar, 2)):
            lhs = S["xi_stage"](z); rhs = S["xi_bulk"](z) - S["R_exact"](z)
            errs.append(abs(lhs - rhs)/max(abs(lhs), mp.mpf(10)**-300))
        # (B) model vs exact front term on [t*, 3t*]
        rel = []
        for t in [tstar*(1 + 2*k/12) for k in range(13)]:
            z = mp.mpc(t, 0); rel.append(abs(S["R_model"](z) - S["R_exact"](z))/abs(S["R_exact"](z)))
        # (C) transition: ALL complex solutions of  bulk = model front term  in the window
        f = lambda z: S["xi_bulk"](z) - S["R_model"](z)
        cands = []
        for i in range(1, 25):
            y = mp.mpf(8)*i/24
            for j in range(0, 41):
                x = 0.8*tstar + 0.5*tstar*j/40
                cands.append((abs(f(mp.mpc(x, y)))/mp.cosh(y*S["U"]), mp.mpc(x, y)))
        cands.sort(key=lambda p: p[0])
        sols = []
        for _, z0 in cands[:12]:
            zc = newton(f, z0, dps - 10)
            if abs(f(zc)) < mp.mpf(10)**(-(dps//2)) and zc.imag > 0.05 and 0.7*tstar <= zc.real <= 1.5*tstar:
                if all(abs(zc - w) > 1e-6 for w in sols): sols.append(zc)
        sols.sort(key=lambda w: w.real)
        soltxt = "; ".join("%s + %s i" % (mp.nstr(w.real, 7), mp.nstr(w.imag, 5)) for w in sols) or "none"
        best = min(sols, key=lambda w: abs(w - mp.mpc(tp, yp))) if sols else None
        say(" U=%.1f t*=%.2f λ=%.2f | (A) max rel err %.1e | (B) model rel err max %.3f mean %.3f | (C) complex balance solutions in [0.7t*,1.5t*]×(0,8]: %s | census %.4f + %.4f i%s"
            % (U, tstar, float(S["lam"]), max(float(e) for e in errs), max(float(r) for r in rel), sum(float(r) for r in rel)/len(rel),
               soltxt, tp, yp, ("  (nearest: dt %.2f%%, dy %.1f%%)" % (100*abs(float(best.real)-tp)/tp, 100*abs(float(best.imag)-yp)/yp)) if best else ""))

if "D" in mode:
    say("=== (D) continuous-U scan of the front window: count and track the pair")
    Us = [0.5 + 0.05*k for k in range(23)]
    prev = None
    for U in Us:
        t0 = time.time()
        tstar = 4*math.exp(2*U); dps = int(30 + math.pi*tstar/(4*math.log(10)) + 12)
        S = setup(U, dps); f = S["xi_stage"]
        T0, T1, H = 0.6*tstar, 1.6*tstar, 10.0
        nb = box_count(f, mp.mpf(T0), mp.mpf(T1), mp.mpf(H)); nr = real_count(f, mp.mpf(T0), mp.mpf(T1), mp.mpf("0.01"))
        # track the pair by continuation from the previous U (or from the balance-equation guess)
        guess = prev if prev is not None else mp.mpc(1.08*tstar, 1.5)
        z = newton(f, guess, dps - 10)
        okz = abs(f(z)) < mp.mpf(10)**(-(dps//2)) and abs(z.imag) > 1e-6 and T0 <= z.real <= T1
        if not okz:   # fall back: grid + Newton in the window
            best = []
            for i in range(1, 41):
                y = H*mp.mpf(i)/40
                for j in range(0, 81):
                    x = T0 + (T1 - T0)*mp.mpf(j)/80
                    best.append((abs(f(mp.mpc(x, y)))/mp.cosh(y*S["U"]), mp.mpc(x, y)))
            best.sort(key=lambda p: p[0])
            for _, z0 in best[:8]:
                z = newton(f, z0, dps - 10)
                if abs(f(z)) < mp.mpf(10)**(-(dps//2)) and abs(z.imag) > 1e-6 and T0 <= z.real <= T1: okz = True; break
        prev = mp.mpc(z.real, abs(z.imag)) if okz else None
        verdict = "one pair" if nb - nr == 2 else ("NO pair in window" if nb - nr == 0 else "COUNT %d — claim dies here" % (nb - nr))
        say(" U=%.2f t*=%7.2f window [%.1f, %.1f]×[−10,10] dps=%d : N_box−N_real = %d (%s) ; pair %s + %s i  t/t*=%.3f  (%.0fs)"
            % (U, tstar, T0, T1, dps, nb - nr, verdict, mp.nstr(z.real, 8) if okz else "—", mp.nstr(abs(z.imag), 5) if okz else "—",
               float(z.real)/tstar if okz else float('nan'), time.time() - t0))
if "E" in mode:
    say("=== (E) TALL-BOX census: Re ∈ [0.5t*, 2t*], Im ∈ [−20, 20]; every non-real zero located")
    for U in [float(a) for a in sys.argv[2:]] or [1.0, 1.2, 1.5]:
        t0 = time.time()
        tstar = 4*math.exp(2*U); dps = int(30 + math.pi*tstar/(4*math.log(10)) + 20)
        S = setup(U, dps); f = S["xi_stage"]
        T0, T1, H = 0.5*tstar, 2.0*tstar, 20.0
        nb = box_count(f, mp.mpf(T0), mp.mpf(T1), mp.mpf(H)); nr = real_count(f, mp.mpf(T0), mp.mpf(T1), mp.mpf("0.01"))
        found = []
        if nb - nr > 0:
            panels = 8
            edges = [mp.mpf(T0) + (T1 - T0)*mp.mpf(k)/panels for k in range(panels + 1)]
            for a, b in zip(edges[:-1], edges[1:]):
                pb = box_count(f, a, b, mp.mpf(H)); pr = real_count(f, a, b, mp.mpf("0.01"))
                if pb - pr > 0:
                    best = []
                    for i in range(1, 61):
                        y = mp.mpf(H)*i/60
                        for j in range(0, 41):
                            x = a + (b - a)*j/40
                            best.append((abs(f(mp.mpc(x, y)))/mp.cosh(y*S["U"]), mp.mpc(x, y)))
                    best.sort(key=lambda p: p[0])
                    for _, z0 in best[:14]:
                        z = newton(f, z0, dps - 12)
                        if abs(f(z)) < mp.mpf(10)**(-(dps//2)) and z.imag > 1e-6 and a - 1 <= z.real <= b + 1:
                            if all(abs(z - w) > 1e-6 for w in found): found.append(z)
        found.sort(key=lambda w: w.real)
        say(" U=%.2f t*=%.2f box [%.1f, %.1f]×[−20, 20] dps=%d : N_box − N_real = %d  ⇒ %d pair(s) ; located: %s  (%.0fs)"
            % (U, tstar, T0, T1, dps, nb - nr, (nb - nr)//2,
               "; ".join("%s + %s i (t/t*=%.3f)" % (mp.nstr(z.real, 8), mp.nstr(z.imag, 5), float(z.real)/tstar) for z in found) or "—",
               time.time() - t0))
out.close()
