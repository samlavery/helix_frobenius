"""Verify the ray arg(eps(chi))/2 for chi_5 (order 4) and chi_7 (order 6).

eps(chi) = tau(chi) / (i^a sqrt(q)),  a = 0 if chi(-1)=1 else 1,
tau(chi) = sum_{n mod q} chi(n) e^{2 pi i n / q}.
The paper claims rays 0.0881*pi (chi_5) and 0.1868*pi (chi_7).
Pre-registered: agreement to < 0.0005 in units of pi CONFIRMS; otherwise REFUTED.
"""
import cmath, math

def chars(q, g, order):
    """characters mod q from a primitive root g, as dict n -> chi(n)"""
    out = []
    # discrete log table
    dlog, x = {}, 1
    for k in range(order):
        dlog[x] = k; x = (x*g) % q
    for j in range(1, order):            # skip principal
        chi = {n: cmath.exp(2j*math.pi*j*dlog[n]/order) for n in dlog}
        out.append((j, chi))
    return out

def gauss(q, chi):
    return sum(chi[n]*cmath.exp(2j*math.pi*n/q) for n in chi)

def report(q, g, order, claimed):
    print(f"--- q = {q}, primitive root {g}, group order {order}; claimed ray {claimed}*pi")
    best = None
    for j, chi in chars(q, g, order):
        ordj = order//math.gcd(j, order)
        a = 0 if abs(chi[q-1] - 1) < 1e-9 else 1
        eps = gauss(q, chi)/((1j**a)*math.sqrt(q))
        ray = cmath.phase(eps)/2/math.pi
        print(f"    j={j}  ord(chi)={ordj}  a={a}  |eps|={abs(eps):.12f}  ray={ray:+.6f}*pi")
        if ordj == order and (best is None or abs(ray-claimed) < abs(best-claimed)):
            best = ray
    print(f"    closest full-order ray: {best:+.6f}*pi   claimed {claimed}*pi   "
          f"diff {abs(best-claimed):.6f}")
    print("    VERDICT:", "CONFIRMED" if abs(best-claimed) < 5e-4 else "REFUTED")
    print()

report(5, 2, 4, 0.0881)
report(7, 3, 6, 0.1868)
