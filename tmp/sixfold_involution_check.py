"""Verify the hidden involution tau on C : t^3 = y, u^3 + x*u + c = 0 over E0.

tau: (u, y, t) -> (u, ybar, tbar),  ybar = -(2x+1) - y  (root sum; pole-free form),
                                    tbar = -x/t  (t != 0),  x = -(u^3+c)/u.
Claims (hand-derived, weil-sixfold-hunt dossier):
  (1) tau maps C(F_p) affine points (u != 0, t != 0) to C(F_p) points;
  (2) tau^2 = id;
  (3) tau . sigma . tau = sigma^2  where sigma: t -> zeta3 * t   (p = 1 mod 3);
  (4) consistency ybar * y = -x^3 whenever y != 0.
"""

def run(p, c=1):
    zeta = None
    if p % 3 == 1:
        for z in range(2, p):
            if pow(z, 3, p) == 1 and z != 1:
                zeta = z
                break
    pts = set()
    for u in range(1, p):
        x = (-(u * u * u + c) * pow(u, p - 2, p)) % p
        for y in range(p):
            if (y * y + (2 * x + 1) * y - x * x * x) % p:
                continue
            for t in range(p):
                if (t * t * t - y) % p == 0:
                    pts.add((u, y, t))
    n = len(pts)
    ok1 = ok2 = ok3 = ok4 = True
    for (u, y, t) in pts:
        x = (-(u * u * u + c) * pow(u, p - 2, p)) % p
        ybar = (-(2 * x + 1) - y) % p
        if t == 0:
            continue  # T-fiber: formula degenerates; involution well-defined via limit
        tbar = (-x * pow(t, p - 2, p)) % p
        img = (u, ybar, tbar)
        if img not in pts:
            ok1 = False
        # tau^2
        ybb = (-(2 * x + 1) - ybar) % p
        tbb = (-x * pow(tbar, p - 2, p)) % p if tbar else None
        if tbar and (u, ybb, tbb) != (u, y, t):
            ok2 = False
        if y != 0 and (ybar * y + x * x * x) % p != 0:
            ok4 = False
        if zeta and tbar:
            # tau(sigma(P)) vs sigma^2(tau(P))
            ts = (zeta * t) % p
            left = (u, ybar, (-x * pow(ts, p - 2, p)) % p)
            right = (u, ybar, (zeta * zeta * tbar) % p)
            if left != right:
                ok3 = False
    return n, ok1, ok2, ok3, ok4


if __name__ == "__main__":
    for p in [7, 13, 31, 37, 43]:
        n, o1, o2, o3, o4 = run(p)
        s3 = "n/a" if p % 3 != 1 else ("PASS" if o3 else "FAIL")
        print(f"p={p:>3}: {n:>5} affine pts | on-curve {'PASS' if o1 else 'FAIL'}"
              f" | tau^2=id {'PASS' if o2 else 'FAIL'} | tau.sig.tau=sig^2 {s3}"
              f" | y*ybar=-x^3 {'PASS' if o4 else 'FAIL'}")
