"""C3 batch 3 — the Xi-ONLY, cancellation-free bench.

Derivation (transcript, batch 3).  With C(u,x) the cell density,
    int_R e^{-i lam u} C(u,x) du = Xi(x + lam/2) Xi(x - lam/2) =: R(lam,x)
(the Wigner distribution of phi).  Using |u-r| = (1/pi) int (1-cos(lam(u-r)))/lam^2 dlam
and int u C du = 0 (C even), int C du = Xi(x)^2, the ramp form collapses to

    T(r,x) := int_r^inf (u-r) C(u,x) du
            = (1/2pi) int_R cos(lam r) * D(lam,x) dlam ,     r >= 0
    D(lam,x) := [ Xi(x)^2 - Xi(x+lam/2) Xi(x-lam/2) ] / lam^2 ,   D(0,x) = L_1(x)/8.

So T(.,x) is the FOURIER COSINE TRANSFORM of D(.,x).  Everything is now expressed in
Xi alone: no phi, no 2-D grid, NO CANCELLATION.  The chain that would give RH:

    (P)  D(.,x) even, >= 0, convex decreasing on [0,inf)      [POLYA's criterion]
      => T(r,x) >= 0 for all r >= 0                            [(S2)]
      => J_{m_y}(x) = 2 int_0^inf m_y''(r) T(r,x) dr >= 0      [m_y'' >= 0]
      => d/dy |Xi(x+iy)|^2 >= 0                                [= the RH target]

This script hostile-tests each link at arbitrary precision.
"""
import mpmath as mp

mp.mp.dps = 40


def xi(s):
    return mp.mpf(1) / 2 * s * (s - 1) * mp.pi ** (-s / 2) * mp.gamma(s / 2) * mp.zeta(s)


def Xi(x):
    """xi(1/2 + i x); real for real x."""
    return mp.re(xi(mp.mpf(1) / 2 + mp.mpc(0, 1) * x))


def say(tag, s):
    print(f"[{tag}] {s}", flush=True)


HH = mp.mpf(10) ** (-12)


def derivs(x):
    """Xi, Xi', Xi'' by central differences at dps 40 (trunc ~1e-24, roundoff ~1e-16 rel)."""
    x = mp.mpf(x)
    f0 = Xi(x)
    fp = Xi(x + HH)
    fm = Xi(x - HH)
    fp2 = Xi(x + 2 * HH)
    fm2 = Xi(x - 2 * HH)
    d1 = (fm2 - 8 * fm + 8 * fp - fp2) / (12 * HH)
    d2 = (-fp2 + 16 * fp - 30 * f0 + 16 * fm - fm2) / (12 * HH ** 2)
    return f0, d1, d2


# ============================================================== attack B1 ===
say("B1", "POINTWISE L_1(x) = 2(Xi'^2 - Xi Xi'') at dps=40 -- the batch-2 'pointwise L1'.")
say("B1", "   reported scale-free as L_1 / (2 Xi'^2 + 2|Xi Xi''|) in [-1,1].")
worst = (mp.mpf(10), None)
negs = []
x = mp.mpf(0)
step = mp.mpf("0.5")
while x <= 200:
    f0, d1, d2 = derivs(x)
    L1 = 2 * (d1 ** 2 - f0 * d2)
    scale = 2 * d1 ** 2 + 2 * abs(f0 * d2)
    rat = L1 / scale if scale != 0 else mp.mpf(1)
    if rat < worst[0]:
        worst = (rat, x)
    if L1 < 0:
        negs.append((x, L1, rat))
    x += step
say("B1", f"   min scale-free L_1 ratio over x in [0,200] step 0.5 : {mp.nstr(worst[0], 8)} at x={worst[1]}")
say("B1", f"   number of x with L_1 < 0 : {len(negs)}")
for t in negs[:10]:
    say("B1", f"     x={t[0]}  L_1={mp.nstr(t[1],8)}  ratio={mp.nstr(t[2],6)}")
say("B1", "   SPECIFIC hostile points flagged in att537 (double precision said L_1<0 at x=60):")
for xv in ["40", "60", "60.5", "90", "120", "150", "199.5"]:
    f0, d1, d2 = derivs(xv)
    L1 = 2 * (d1 ** 2 - f0 * d2)
    say("B1", f"     x={xv:>7}  Xi={mp.nstr(f0,6)}  L_1={mp.nstr(L1,10)}  sign={'+' if L1>0 else '-'}")

# ============================================================== attack C1 ===
say("C1", "D(lam,x) >= 0  <=>  Xi(x+t)Xi(x-t) <= Xi(x)^2  for all t  (two-point log-concavity)")
say("C1", "   reported as max over t of Xi(x+t)Xi(x-t)/Xi(x)^2 ; must be <= 1")


def D(lam, x):
    lam = mp.mpf(lam)
    x = mp.mpf(x)
    if lam == 0:
        f0, d1, d2 = derivs(x)
        return 2 * (d1 ** 2 - f0 * d2) / 8
    return (Xi(x) ** 2 - Xi(x + lam / 2) * Xi(x - lam / 2)) / lam ** 2


xprobe = ["0", "5", "9", "14.134725", "17", "21.022", "25.011", "30.425", "40", "60", "90"]
badD = []
for xv in xprobe:
    mn = mp.mpf("1e300")
    arg = None
    lam = mp.mpf("0.05")
    while lam <= 60:
        v = D(lam, xv)
        if v < mn:
            mn = v
            arg = lam
        lam += mp.mpf("0.05")
    say("C1", f"   x={xv:>10}  min_lam D = {mp.nstr(mn,8)} at lam={mp.nstr(arg,6)}  "
              f"D(0)=L_1/8={mp.nstr(D(0,xv),8)}")
    if mn < 0:
        badD.append((xv, mn, arg))
say("C1", f"   x-values where D dips negative: {len(badD)}")

# ============================================================== attack B3 ===
say("B3", "POLYA CRITERION on D(.,x): even, >=0, CONVEX and decreasing on [0,inf) => T>=0.")
say("B3", "   testing monotonicity and convexity of lam -> D(lam,x) by second differences.")
for xv in ["0", "5", "14.134725", "21.022", "30.425", "60"]:
    dl = mp.mpf("0.1")
    lam = dl
    badconv = None
    baddec = None
    nconv = 0
    ndec = 0
    while lam <= 25:
        a, b, c = D(lam - dl, xv), D(lam, xv), D(lam + dl, xv)
        sec = (a - 2 * b + c) / dl ** 2
        if sec < 0:
            nconv += 1
            if badconv is None:
                badconv = (lam, sec)
        if c > b:
            ndec += 1
            if baddec is None:
                baddec = (lam, b, c)
        lam += dl
    say("B3", f"   x={xv:>10}  concave samples: {nconv:4d} (first at lam={mp.nstr(badconv[0],5) if badconv else '--'}) ;"
              f"  increasing samples: {ndec:4d} (first at lam={mp.nstr(baddec[0],5) if baddec else '--'})")

# ============================================================== attack B2 ===
say("B2", "RAMP FORM T(r,x) = (1/pi) int_0^inf cos(lam r) D(lam,x) dlam, arbitrary precision.")


def T(r, x, LAM=None):
    r = mp.mpf(r)
    x = mp.mpf(x)
    if LAM is None:
        LAM = 2 * (abs(mp.mpf(x)) + 90)
    pts = [mp.mpf(0)] + [mp.mpf(k) for k in range(1, int(LAM) + 1)]
    head = mp.quad(lambda l: mp.cos(l * r) * D(l, x), pts) / mp.pi
    X2 = Xi(x) ** 2
    L = mp.mpf(LAM)
    if r == 0:
        tail = X2 / L
    else:
        tail = X2 * (mp.cos(L * r) / L - r * (mp.pi / 2 - mp.si(L * r)))
    return head + tail / mp.pi


say("B2", "   sanity: int_0^inf T(r,x) dr must equal L_1(x)/16")
for xv in ["0", "5", "14.134725"]:
    f0, d1, d2 = derivs(xv)
    L1 = 2 * (d1 ** 2 - f0 * d2)
    val = mp.quad(lambda r: T(r, xv), [0, 0.5, 1, 2, 4])
    say("B2", f"   x={xv:>10}  int T dr = {mp.nstr(val,10)}   L_1/16 = {mp.nstr(L1/16,10)}")

say("B2", "   sign of T(r,x) -- the hostile points from the double-precision run")
for xv in ["0", "14.134725", "30.425", "40", "60", "90"]:
    row = f"   x={xv:>10} "
    for rv in ["0", "0.05", "0.2", "0.5", "1.0", "1.5"]:
        v = T(rv, xv)
        row += f"  T({rv})={mp.nstr(v, 6)}"
    print(row, flush=True)
