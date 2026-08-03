"""eta_fiber_ledger.py — the same eta fiber, summed by its own ledger.

The bank at head height Z = e^y holds one phasor per carrier site n <= Z:

    g(x) = x^{-s} w(x/Z),   s = 1/2 + i y,   w(u) = exp(-u^2/(1-u^2))

    T = sum_{n<=N} g(n)          (all sites,   N = floor(Z))
    E = sum_{m<=N/2} g(2m)       (even sites)
    R_odd = T - E,  R_even = E,  F = T - 2E,  c = |F| / max(|R_odd|,|R_even|)

Brute force costs O(Z) phasors and dies past ~1e11.  But above a split point M
the sites stop resolving individually: the phase step between neighbours is
y/n << 1, so the bank is smooth there and its exact sum is the continuum
integral plus a Bernoulli ledger,

    sum_{n=M}^{N} g(n) = J + g(M)/2 - sum_k c_k g^{(2k-1)}(M),
    J = int_M^Z g dx,   c_k = B_{2k}/(2k)!

whose leading entry c_0 = B_1 = -1/2 is the same mean-of-drift the clock chart
books for an event-free cell.  Doing this for both lanes, THE CONTINUUM PART
CANCELS: J appears in T once and in 2E once, so

    F = sum_{n<M} (-1)^{n-1} g(n) - g(M)/2 + sum_k c_k (2^{2k}-1) g^{(2k-1)}(M)

with no integral at all.  The 2e14 phasors above M reach the lane difference
only through the ledger at the split.  J is still needed for the individual
lane resultants (the balance exhibit), and is done by quadrature.

This is the same finite sum the C brute-force engine computes, to the EM
remainder (< 1e-25 at M=5000, K=6).  `validate` checks that claim against the
C engine.  No L-function, no functional equation, no continuation, no
reference ordinate enters anywhere.

Run:
    python3 eta_fiber_ledger.py validate
    python3 eta_fiber_ledger.py scan  <y0> <y1> <npts>
    python3 eta_fiber_ledger.py value <y>
"""

import sys

from mpmath import mp, mpf, mpc, exp, log, sqrt, pi, taylor, binomial, bernoulli, quad, fabs

mp.dps = 50

M_SPLIT = 5000          # site split: below, term by term; above, the ledger
K_EM = 6                # Bernoulli ledger depth
NW = 10                 # window derivatives retained


def window(u):
    """growth window w(u) = exp(1 - 1/(1-u^2)) = exp(-u^2/(1-u^2)).

    A site past the head has not been reached yet: w = 0 for u >= 1.  Off the
    real axis the closed form is the analytic continuation, which is what
    `taylor` needs at the split point.
    """
    d = 1 - u * u
    if d.imag == 0 and d.real <= 0:
        return mpf(0)
    return exp(-u * u / d)


def g_derivs(M, s, Z, jmax):
    """g(x) = x^{-s} w(x/Z) and its derivatives at x = M, exactly.

    Leibniz over the two factors: the power's derivatives are the Pochhammer
    closed form, the window's come from its Taylor series at u = M/Z.
    """
    u0 = mpf(M) / Z
    wt = taylor(window, u0, jmax)              # wt[i] = w^{(i)}(u0)/i!
    wd = [wt[i] * mp.factorial(i) / Z ** i for i in range(jmax + 1)]  # d^i/dx^i

    pw = []                                    # d^m/dx^m of x^{-s} at M
    poch = mpc(1)
    for m in range(jmax + 1):
        pw.append((-1) ** m * poch * mpf(M) ** (-s - m))
        poch *= (s + m)

    out = []
    for j in range(jmax + 1):
        acc = mpc(0)
        for i in range(j + 1):
            acc += binomial(j, i) * pw[j - i] * wd[i]
        out.append(acc)
    return out


def ledger_F(y, M=M_SPLIT, K=K_EM):
    """the lane difference F = R_odd - R_even, exactly, with no integral"""
    s = mpf(1) / 2 + 1j * mpf(y)
    Z = exp(mpf(y))
    gd = g_derivs(M, s, Z, 2 * K)

    head = mpc(0)
    for n in range(1, M):
        t = mpf(n) ** (-s) * window(mpf(n) / Z)
        head += t if (n & 1) else -t

    F = head - gd[0] / 2
    for k in range(1, K + 1):
        ck = bernoulli(2 * k) / mp.factorial(2 * k)
        F += ck * (2 ** (2 * k) - 1) * gd[2 * k - 1]
    return F


def tail_integral(y, M=M_SPLIT):
    """J = int_M^Z x^{-s} w(x/Z) dx, by x = Z e^{-v}:
       J = Z^{1-s} int_0^V e^{(-1/2+iy)v} w(e^{-v}) dv,  V = log(Z/M)"""
    s = mpf(1) / 2 + 1j * mpf(y)
    Z = exp(mpf(y))
    V = log(Z / M)
    integrand = lambda v: exp((-mpf(1) / 2 + 1j * mpf(y)) * v) * window(exp(-v))
    npan = int(mp.floor(y * V / mp.pi)) + 2
    pts = [V * i / npan for i in range(npan + 1)]
    return Z ** (1 - s) * quad(integrand, pts)


def lanes(y, M=M_SPLIT, K=K_EM):
    """the two lane resultants and the closure measure"""
    s = mpf(1) / 2 + 1j * mpf(y)
    Z = exp(mpf(y))
    gd = g_derivs(M, s, Z, 2 * K)
    J = tail_integral(y, M)

    head_all = mpc(0)
    head_even = mpc(0)
    for n in range(1, M):
        t = mpf(n) ** (-s) * window(mpf(n) / Z)
        head_all += t
        if not (n & 1):
            head_even += t

    corr_T = mpc(0)
    corr_E = mpc(0)
    for k in range(1, K + 1):
        ck = bernoulli(2 * k) / mp.factorial(2 * k)
        corr_T += ck * gd[2 * k - 1]
        corr_E += ck * 2 ** (2 * k - 1) * gd[2 * k - 1]

    T = head_all + J + gd[0] / 2 - corr_T
    E = head_even + J / 2 + gd[0] / 2 - corr_E

    R_odd, R_even = T - E, E
    F = T - 2 * E
    mx = max(abs(R_odd), abs(R_even))
    return R_odd, R_even, F, (abs(F) / mx if mx > 0 else mpf(1))


def carrier_gauge(y):
    """the global (pi/3)^{-s} factor the C engine carries and the ledger drops;
    projective in c, but restored here so the two agree term for term"""
    s = mpf(1) / 2 + 1j * mpf(y)
    return (pi / 3) ** (-s)


def cmd_value(y):
    R_odd, R_even, F, c = lanes(mpf(y))
    G = carrier_gauge(mpf(y))
    print(f"y        {y}")
    print(f"Z        {mp.nstr(exp(mpf(y)), 10)}")
    print(f"N        {int(exp(mpf(y)))}")
    print(f"R_odd    {mp.nstr(R_odd * G, 18)}   |R|={mp.nstr(abs(R_odd), 12)}")
    print(f"R_even   {mp.nstr(R_even * G, 18)}   |R|={mp.nstr(abs(R_even), 12)}")
    print(f"F        {mp.nstr(F * G, 12)}")
    print(f"c(Z)     {mp.nstr(c, 10)}")


def cmd_scan(y0, y1, n):
    """|F| along the growth path; minima are focal closures"""
    for i in range(n):
        y = mpf(y0) + (mpf(y1) - mpf(y0)) * i / (n - 1)
        F = ledger_F(y)
        print(f"{mp.nstr(y, 15)} {mp.nstr(abs(F), 8)}")
        sys.stdout.flush()


def secant(ya, yb, steps=6, verbose=True):
    """complex secant on F: F is analytic in y and vanishes at the event"""
    ya, yb = mpf(ya), mpf(yb)
    fa, fb = ledger_F(ya), ledger_F(yb)
    for i in range(steps):
        d = fb - fa
        if d == 0:
            break
        yn = yb - (fb * (yb - ya) / d).real
        ya, fa = yb, fb
        yb = yn
        fb = ledger_F(yb)
        if verbose:
            print(f"  secant {i+1}: y={mp.nstr(yb, 20)}  |F|={mp.nstr(abs(fb), 6)}")
            sys.stdout.flush()
    return yb


def cmd_locate(y0, y1, n):
    ys, fs = [], []
    for i in range(n):
        y = mpf(y0) + (mpf(y1) - mpf(y0)) * i / (n - 1)
        ys.append(y)
        fs.append(abs(ledger_F(y)))
    med = sorted(fs)[len(fs) // 2]
    step = ys[1] - ys[0]
    for i in range(1, n - 1):
        if fs[i] < fs[i - 1] and fs[i] < fs[i + 1] and fs[i] < med / 4:
            y = secant(ys[i] - step / 2, ys[i] + step / 2)
            R_odd, R_even, F, c = lanes(y)
            print(f"event  y={mp.nstr(y, 20)}  Z={mp.nstr(exp(y), 8)}  "
                  f"N={int(exp(y))}")
            G = carrier_gauge(y)
            print(f"   R_odd  {mp.nstr(R_odd * G, 18)}  |R|={mp.nstr(abs(R_odd * G), 12)}")
            print(f"   R_even {mp.nstr(R_even * G, 18)}  |R|={mp.nstr(abs(R_even * G), 12)}")
            print(f"   |F|    {mp.nstr(abs(F * G), 8)}")
            print(f"   c(Z)   {mp.nstr(c, 8)}")
            sys.stdout.flush()


def cmd_validate():
    """the ledger engine must reproduce the C brute-force bank exactly"""
    import subprocess

    tests = [12.5, 14.134725141734694, 18.25, 21.022039638771555]
    print(f"{'y':>20} {'|F| ledger':>16} {'|F| brute':>16} {'rel diff':>11} "
          f"{'c ledger':>13} {'c brute':>13}")
    for y in tests:
        R_odd, R_even, F, c = lanes(mpf(y))
        G = carrier_gauge(mpf(y))
        Fg = F * G
        out = subprocess.run(["./eta_fiber", "value", repr(y)],
                             capture_output=True, text=True,
                             env={"ETA_THREADS": "10", "PATH": "/usr/bin:/bin"})
        br, bi, bc = None, None, None
        for line in out.stdout.splitlines():
            p = line.split()
            if p and p[0] == "F":
                br, bi = float(p[1]), float(p[2])
            if p and p[0] == "c(Z)":
                bc = float(p[1])
        bF = abs(complex(br, bi))
        rel = float(abs(abs(Fg) - bF) / max(bF, 1e-300))
        print(f"{y:>20.15g} {mp.nstr(abs(Fg), 10):>16} {bF:>16.9e} "
              f"{rel:>11.2e} {mp.nstr(c, 8):>13} {bc:>13.6e}")


if __name__ == "__main__":
    if len(sys.argv) < 2:
        print(__doc__)
        sys.exit(2)
    cmd = sys.argv[1]
    if cmd == "validate":
        cmd_validate()
    elif cmd == "value":
        cmd_value(sys.argv[2])
    elif cmd == "scan":
        cmd_scan(sys.argv[2], sys.argv[3], int(sys.argv[4]))
    elif cmd == "locate":
        cmd_locate(sys.argv[2], sys.argv[3], int(sys.argv[4]))
    else:
        print(f"unknown mode {cmd}")
        sys.exit(2)
