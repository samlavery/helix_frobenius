#!/usr/bin/env python3
"""
att555 — census of the NON-REAL zeros of the θ-stages Ξ_U (the fiber grown to front U in the θ
register), as a test allowed to come out either way (Sam: "let our testing show RH true or false").

Stage:  Ξ_U(z) = 2 ∫_0^U Φ(u) cos(zu) du,  Φ(u) = 4 Σ_n (2π²n⁴e^{9u/2} − 3πn²e^{5u/2}) e^{−πn²e^{2u}}
(Pólya's truncation; Ξ_∞(t) = ξ(½+it)).  Entire of exponential type U; on the real axis its ξ-like
part decays like e^{−πt/4} while the truncation tail decays like Φ(U)/t, so the stage carries an
escort pair near the amplitude front t* ≈ 4e^{2U} (ledger 519).  Compiled Hurwitz + the escape law
say: if every stage has ONLY escaping non-real zeros, every zero of ξ is real.

PRE-REGISTERED, per stage U ∈ {0.6, 0.8, 1.0, 1.2, 1.5}:
  box  Re ∈ [0, T], T = 3 t*, Im ∈ [−3, 3];  N_box by the argument principle; N_real by sign changes.
  P1  N_box − N_real = 2: EXACTLY one conjugate pair per stage.       (≥ 4 ⟹ the one-pair law dies)
  P2  the pair's height t*(U) fits c·e^{aU} with a = 2 ± 0.15 and c ≈ 4 — the pair ESCAPES.
  P3  no non-real zero with Re z < t*/2 for any U — nothing forms at bounded height.
  VERDICT RULE: a non-real zero that persists at bounded height across increasing U, or a pair whose
  height stops growing, is the RH-FALSE signature in this register; all pairs escaping with none
  forming is the RH-TRUE reading at these stages.  Either is reported as read.
OUTPUT tmp/att555_results.txt
"""
import sys, math, time
import mpmath as mp

Us = [float(a) for a in sys.argv[1:]] or [0.6, 0.8, 1.0, 1.2, 1.5]
out = open("tmp/att555_results.txt", "a")
def say(*a):
    s = " ".join(str(x) for x in a); print(s, flush=True); out.write(s + "\n"); out.flush()

def make_stage(U, dps):
    mp.mp.dps = dps
    PI = mp.pi
    def phi(u):
        e2 = mp.exp(2*u); e9 = mp.exp(mp.mpf(9)/2*u); e5 = mp.exp(mp.mpf(5)/2*u)
        return 4*mp.fsum((2*PI**2*n**4*e9 - 3*PI*n**2*e5)*mp.exp(-PI*n*n*e2) for n in range(1, 16))
    nodes = mp.calculus.quadrature.GaussLegendre(mp.mp).get_nodes(mp.mpf(0), mp.mpf(U), 7, mp.mp.prec)
    PW = [(x, phi(x)*w) for (x, w) in nodes]
    def xi(z):
        return 2*mp.fsum(pw*mp.cos(z*x) for (x, pw) in PW)
    return xi, phi

def winding(xi, a, b, n):
    """total phase change of xi along the segment a→b sampled at n+1 points; refines on large steps"""
    PI = mp.pi
    for attempt in range(4):
        tot = mp.mpf(0); prev = None; ok = True
        for k in range(n + 1):
            z = a + (b - a)*mp.mpf(k)/n
            ph = mp.arg(xi(z))
            if prev is not None:
                d = ph - prev
                while d > PI: d -= 2*PI
                while d < -PI: d += 2*PI
                if abs(d) > PI/2: ok = False; break
                tot += d
            prev = ph
        if ok: return tot
        n *= 2
    raise RuntimeError("winding did not converge")

def box_count(xi, T0, T1, H, per_unit):
    c = [mp.mpc(T0, -H), mp.mpc(T1, -H), mp.mpc(T1, H), mp.mpc(T0, H), mp.mpc(T0, -H)]
    ns = [max(20, int((T1 - T0)*per_unit)), max(40, int(2*H*per_unit)),
          max(20, int((T1 - T0)*per_unit)), max(40, int(2*H*per_unit))]
    tot = mp.mpf(0)
    for (a, b), n in zip(zip(c[:-1], c[1:]), ns):
        tot += winding(xi, a, b, n)
    return int(mp.nint(tot/(2*mp.pi)))

def real_count(xi, T0, T1, step):
    n = int((T1 - T0)/step) + 1
    prev = None; cnt = 0
    for k in range(n):
        v = xi(mp.mpc(T0 + k*step, 0)).real
        if prev is not None and v*prev < 0: cnt += 1
        prev = v
    return cnt

def newton_zero(xi, z0, H):
    z = z0
    for _ in range(100):
        f = xi(z); h = mp.mpf(10)**(-(mp.mp.dps//2))
        df = (xi(z + h) - xi(z - h))/(2*h)
        if df == 0: break
        st = f/df; z -= st
        if abs(st) < mp.mpf(10)**(-(mp.mp.dps - 8)): break
    return z

pairs_found = {}
for U in Us:
    t0 = time.time()
    import os
    tstar = 4*math.exp(2*U); T = 3*tstar; H = float(os.environ.get("BOX_H", "3.0"))
    dps = int(30 + math.pi*tstar/(4*math.log(10)) + 12)
    xi, phi = make_stage(U, dps)
    say("\n== U = %.2f  predicted front t* = 4e^{2U} = %.2f ; box Re ∈ [0, %.1f], Im ∈ [−%.0f, %.0f] ; dps = %d ; Φ(U) = %s"
        % (U, tstar, T, H, H, dps, mp.nstr(phi(mp.mpf(U)), 4)))
    Nbox = box_count(xi, mp.mpf(0), mp.mpf(T), mp.mpf(H), per_unit=20)
    Nreal = real_count(xi, mp.mpf(0), mp.mpf(T), mp.mpf("0.01"))
    excess = Nbox - Nreal
    say("   N_box = %d   N_real = %d   non-real = %d  (%s)" % (Nbox, Nreal, excess,
        "exactly one conjugate pair" if excess == 2 else ("NONE in box" if excess == 0 else "MORE THAN ONE PAIR — law dies")))
    # localize non-real zeros by panel counts, then Newton
    found = []
    if excess > 0:
        panels = 12
        edges = [mp.mpf(T)*k/panels for k in range(panels + 1)]
        for a, b in zip(edges[:-1], edges[1:]):
            nb = box_count(xi, a, b, mp.mpf(H), per_unit=20)
            nr = real_count(xi, a, b, mp.mpf("0.01"))
            if nb - nr > 0:
                # grid search in the upper half of the panel
                best = []
                for i in range(1, 31):
                    y = mp.mpf(H)*i/30
                    for j in range(0, 61):
                        x = a + (b - a)*j/60
                        best.append((abs(xi(mp.mpc(x, y))), mp.mpc(x, y)))
                best.sort(key=lambda p: p[0])
                for _, z0 in best[:10]:
                    z = newton_zero(xi, z0, H)
                    if abs(xi(z)) < mp.mpf(10)**(-(dps//2)) and z.imag > mp.mpf("1e-6") and a - 1 <= z.real <= b + 1:
                        if all(abs(z - w) > mp.mpf("1e-6") for w in found):
                            found.append(z)
        found.sort(key=lambda w: w.real)
        for z in found:
            say("   non-real zero: t = %s  y = %s   (t/t* = %.3f ; below t*/2: %s)"
                % (mp.nstr(z.real, 10), mp.nstr(z.imag, 8), float(z.real)/tstar, "YES" if float(z.real) < tstar/2 else "no"))
        pairs_found[U] = [(float(z.real), float(z.imag)) for z in found]
    say("   (%.0f s)" % (time.time() - t0))

# P2: escape law fit on the highest-y (front) pair per stage
say("\nESCAPE LAW FIT: t*(U) = c·e^{aU} on the front pair of each stage")
Uf, tf = [], []
for U, zs in pairs_found.items():
    if zs:
        zs_sorted = sorted(zs, key=lambda p: -p[1]); Uf.append(U); tf.append(zs_sorted[0][0])
if len(Uf) >= 3:
    import numpy as np
    a, lc = np.polyfit(Uf, np.log(tf), 1)
    say("   fitted a = %.3f (predicted 2), c = %.3f (predicted 4) over U = %s" % (a, math.exp(lc), Uf))
    say("   P2 %s" % ("CONFIRMED" if abs(a - 2) <= 0.15 else "DIED"))
p1 = all(len(v) == 1 for v in pairs_found.values()) and len(pairs_found) == len(Us)
p3 = all(all(p[0] >= 2*math.exp(2*U) for p in v) for U, v in pairs_found.items())
say("P1 exactly one pair per stage: %s ; P3 nothing below t*/2: %s" % ("CONFIRMED" if p1 else "DIED", "CONFIRMED" if p3 else "DIED"))
out.close()
