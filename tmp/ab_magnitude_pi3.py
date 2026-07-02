"""A/B tests for the focal-closure growth scanner.

Q1 (magnitude): does each phasor need to enter at zero and GROW to completion?
Compare four magnitude laws at the same closure events:
    bump      self-similar C-inf window  w(n/Z)=exp(1-1/(1-u^2))   (current)
    hard      instant entry, no growth   w=1 for n<=Z              (untapered)
    linear    self-similar linear ramp   w=clip(2(1-u),0,1)        (complete by n=Z/2)
    tau400    fixed-length ramp          w=clip((Z-n)/400,0,1)     (model.py law)

Q2 (pi/3): is the pi/3 scaling load-bearing in the ARROWS?  Same scan with
    x_n=(pi/3)n (carrier coordinate) vs x_n=n (bare index)
-- prediction: constant amplitude factor + global phase, cancels in closure.
"""
import math
import sys

import numpy as np

sys.path.insert(0, "/Users/samuellavery/work/helix_frobenius/carrier_fiber")

PI3 = math.pi / 3.0

CHI = {
    "chi3": lambda n: np.where(n % 3 == 1, 1.0, np.where(n % 3 == 2, -1.0, 0.0)),
    "eta": lambda n: np.where(n % 2 == 1, 1.0, -1.0),
}


def window(u, law):
    if law == "bump":
        return np.where(u < 1.0, np.exp(1.0 - 1.0 / np.clip(1.0 - u * u, 1e-300, None)), 0.0)
    if law == "hard":
        return np.ones_like(u)
    if law == "linear":
        return np.clip(2.0 * (1.0 - u), 0.0, 1.0)
    raise ValueError(law)


def closure(name, y, law, scale=PI3, tau=None):
    Z = math.exp(y)
    N = int(Z)
    n = np.arange(1, N + 1, dtype=np.float64)
    c = CHI[name](n.astype(np.int64))
    if tau is not None:
        w = np.clip((Z - n) / tau, 0.0, 1.0)
    else:
        w = window(n / Z, law)
    x = scale * n
    amp = w * x ** (-0.5)
    ph = np.exp(-1j * y * np.log(x))
    P = complex(np.sum(np.where(c > 0, amp, 0.0) * ph))
    M = complex(np.sum(np.where(c < 0, amp, 0.0) * ph))
    d = max(abs(P), abs(M))
    return abs(P - M) / d if d > 0 else 1.0


def golden(f, a, b, iters=60):
    gr = (5.0 ** 0.5 - 1.0) / 2.0
    c, d = b - gr * (b - a), a + gr * (b - a)
    fc, fd = f(c), f(d)
    for _ in range(iters):
        if fc < fd:
            b, d, fd = d, c, fc
            c = b - gr * (b - a)
            fc = f(c)
        else:
            a, c, fc = c, d, fd
            d = a + gr * (b - a)
            fd = f(d)
    return 0.5 * (a + b)


TRUE = {"chi3": 8.039737155681467, "eta": 14.134725141734694}

if __name__ == "__main__":
    print("Q1 -- magnitude law (locate first zero, no seeds: window +/-0.25 around scan dip)")
    print(f"   {'char':6} {'law':8} {'located y':>14} {'|err| vs true':>13} {'closure depth':>14}")
    for name in ("chi3", "eta"):
        g = TRUE[name]
        for law, tau in (("bump", None), ("hard", None), ("linear", None), ("tau400", 400.0)):
            lw = law if tau is None else "bump"
            f = lambda t: closure(name, t, law if tau is None else "hard", tau=tau)
            y = golden(f, g - 0.25, g + 0.25)
            print(f"   {name:6} {law:8} {y:>14.9f} {abs(y - g):>13.1e} {f(y):>14.2e}")
    print()
    print("Q2 -- pi/3 arrow scaling A/B (bump law)")
    print(f"   {'char':6} {'x_n':10} {'located y':>14} {'|err| vs true':>13} {'closure depth':>14}")
    for name in ("chi3", "eta"):
        g = TRUE[name]
        for lbl, sc in (("(pi/3)*n", PI3), ("n (bare)", 1.0)):
            f = lambda t: closure(name, t, "bump", scale=sc)
            y = golden(f, g - 0.25, g + 0.25)
            print(f"   {name:6} {lbl:10} {y:>14.9f} {abs(y - g):>13.1e} {f(y):>14.2e}")
