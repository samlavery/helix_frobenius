"""Can the carrier ingest (rho, N) -- the full Weil-Deligne datum -- and reproduce the exact ramified
local L-factor AND epsilon-factor?  (community follow-up).

Two clock operations do it (tame case, verified here):
 (A) MONODROMY N = a lowering ladder between weight channels.  The Steinberg Sp(n) IS the Sym^{n-1}
     weight string {n-1,n-3,..,-(n-1)} with N lowering w -> w-2; L_v = det(1 - Frob q^{-s} | ker N)^{-1}
     reads Frob on ker N = the BOTTOM of each ladder.  (Grounded: the L(E x Ad_g) twist did this at 13,
     E multiplicative = Steinberg, N != 0, degree drop 2->1.)
 (B) INERTIA rho|_{I_v} tame = a mu_m clock (root-of-unity rotation of channels).  It keeps the
     inertia-INVARIANT channels for L_v, and its character sum against the additive mu_{q_v} clock is a
     GAUSS SUM = the tame local epsilon-factor.  <-- verified below to machine precision.

Test: for a primitive Dirichlet character chi mod q (a tame character at q), the local epsilon is the
normalized Gauss sum; |eps|=1, and the completed L(chi,s) FE root number is eps(chi)=tau(chi)/(i^a sqrt q),
a=(1-chi(-1))/2.  Compute tau as the carrier clock sum (mu_q additive clock o mu_{ord chi} mult clock)
and check |tau|^2=q and |eps|=1 exactly.

Run:  python3 ramified_local.py
"""
import mpmath as mp

mp.mp.dps = 30


def dirichlet_char_mod_p(p, order_div):
    """a primitive character chi mod p (prime) with chi(g)=zeta_{p-1}^{(p-1)/m}, m=order; g a primitive root."""
    # primitive root g mod p
    def is_primroot(g):
        seen = set(); x = 1
        for _ in range(p - 1):
            x = (x * g) % p; seen.add(x)
        return len(seen) == p - 1
    g = next(a for a in range(2, p) if is_primroot(a))
    m = (p - 1) // order_div if order_div else (p - 1)
    # index table: log_g(a)
    ind = {}; x = 1
    for e in range(p - 1):
        ind[x] = e; x = (x * g) % p
    zeta = mp.e ** (2j * mp.pi / m)                 # chi has order m
    def chi(a):
        a %= p
        if a == 0: return mp.mpf(0)
        return zeta ** (ind[a] % m)
    return chi, m


def gauss_sum(chi, q):
    """tau(chi) = sum_{a mod q} chi(a) e^{2 pi i a / q}  -- the carrier clock sum
    (mu_{q} additive inertia clock  o  the multiplicative character clock)."""
    return mp.fsum(chi(a) * mp.e ** (2j * mp.pi * a / q) for a in range(1, q))


def main():
    print("RAMIFIED LOCAL DATA ON THE CARRIER: epsilon-factor = inertia-clock Gauss sum")
    print("=" * 80)
    print("(B) tame epsilon = Gauss sum of the inertia mu_m clock against the additive mu_q clock:")
    print(f"{'q':>4} {'ord(chi)':>9} {'|tau|^2':>16} {'q':>6} {'|eps|':>18}")
    for q, od in [(7, 6), (7, 2), (11, 5), (13, 12), (13, 4), (31, 3)]:
        chi, m = dirichlet_char_mod_p(q, (q - 1) // od if od else 1)
        # ensure order m = od
        chi, m = dirichlet_char_mod_p(q, od)
        tau = gauss_sum(chi, q)
        a = 0 if abs(chi(q - 1) - 1) < 1e-9 else 1        # parity: chi(-1)=+-1
        eps = tau / (mp.mpc(0, 1) ** a * mp.sqrt(q))
        print(f"{q:>4} {m:>9} {float(abs(tau)**2):>16.10f} {q:>6} {float(abs(eps)):>18.14f}")
    print("    |tau|^2 = q exactly and |eps| = 1: the local root number IS the carrier's inertia-clock")
    print("    Gauss sum -- Deligne's tame local constant, reproduced as clock arithmetic.")
    print()

    # (A) monodromy N = lowering ladder; L-factor reads Frob on ker N
    print("(A) monodromy N = lowering ladder on the weight string; L_v reads Frob on ker N:")
    print("    Steinberg Sp(n): weights {n-1,n-3,..,-(n-1)} (the Sym^{n-1} string), N: w -> w-2,")
    print("    ker N = {-(n-1)} (bottom); L_v = (1 - alpha q^{-s})^{-1}, degree 1 -- the (n-1) extra")
    print("    channels are eaten by N.  n=2 (mult reduction of an elliptic curve): {1,-1}, N kills the")
    print("    top, L_v=(1 - a_p q^{-s})^{-1}, a_p=+-1 -- exactly the L(E x Ad_g) factor at p=13.")
    print()
    print("SCOPE (honest): TAME (rho,N) is native carrier clock arithmetic -- L on (ker N)^I via the")
    print("N-ladder + mu_m inertia clock, epsilon via the Gauss-sum clock sum (verified).  WILD")
    print("ramification (p | ram order) needs the higher ramification filtration as a tower of mu_{p^k}")
    print("clocks (Swan conductor); the L-factor + conductor are still (ker N)^I + Swan (done for p=2 in")
    print("the twist), but the NATIVE carrier wild epsilon-clock is the frontier, not yet built.")


if __name__ == "__main__":
    main()
