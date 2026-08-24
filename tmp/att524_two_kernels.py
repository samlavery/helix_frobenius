"""
att524 — the two kernels of [H2], with controls.

Both are built from xi alone (no zero data):

  K_Phi(w,z) = Xi(z - conj w)
      = <g_w, g_z> in L^2(R, Phi du), g_w(u) = e^{i w u},  Phi = Riemann's kernel > 0.
      Since Phi decays like e^{-pi e^{2|u|}}, g_w in L^2(Phi) for EVERY w in C.
      PD unconditionally -- but PD(K_Phi) <=> Phi >= 0 (Bochner), which is classical,
      and its operator is multiplication by u on L^2(Phi): the WRONG measure.
      Its Stieltjes transform is int Phi/(u-z) du, NOT M = -A'/A.

  K_E(w,z) = [E(z) conj(E(w)) - E*(z) conj(E*(w))] / (2 pi i (conj w - z)),
      E = Xi + i Xi',  E* = Xi - i Xi'.
      Diagonal: K(w,w) = (|E|^2 - |E*|^2)/(4 pi Im w), so PD <=> IsHB <=> RH.

PURPOSE: check both numerically AND check that the K_E instrument is not blind --
i.e. that it actually goes indefinite when the A-component has a complex zero pair.
A blind instrument would make the whole de Branges route null.

PRE-REGISTERED (fixed before running):
  Xi   / K_Phi ..... PSD          (validates the Gram derivation)
  Xi   / K_E ....... PSD          (consistent with RH)
  NEG-A: F = 2cos z - cos 2z (signed measure) / K_Phi ..... INDEFINITE
  NEG-B: p = z^4 - 3z^2 - 4 (zeros +-2, +-i)  / K_E ....... INDEFINITE
  POS-B: p = z^4 - 5z^2 + 4 (zeros +-1, +-2)  / K_E ....... PSD
If NEG-B is PSD the instrument is blind and the route is null.
"""
import mpmath as mp

mp.mp.dps = 30


def xi(s):
    return 0.5 * s * (s - 1) * mp.pi ** (-s / 2) * mp.gamma(s / 2) * mp.zeta(s)


def Xi(z):
    return xi(mp.mpf(1) / 2 + 1j * z)


def dXi(z):
    return mp.diff(Xi, z)


def gram(f, nodes):
    """K_Phi-type Gram: [f(z_j - conj z_i)]."""
    n = len(nodes)
    M = mp.matrix(n, n)
    for i in range(n):
        for j in range(n):
            M[i, j] = f(nodes[j] - mp.conj(nodes[i]))
    return M


def deBranges_gram(A, B, nodes):
    """K_E(w,z) with E = A - iB, E* = A + iB (A,B real entire)."""
    n = len(nodes)
    M = mp.matrix(n, n)

    def E(z):
        return A(z) - 1j * B(z)

    def Estar(z):
        return A(z) + 1j * B(z)

    for i in range(n):
        w = nodes[i]
        for j in range(n):
            z = nodes[j]
            num = E(z) * mp.conj(E(w)) - Estar(z) * mp.conj(Estar(w))
            den = 2j * mp.pi * (mp.conj(w) - z)
            M[i, j] = num / den
    return M


def hermitian_eigs(M):
    n = M.rows
    H = mp.matrix(n, n)
    for i in range(n):
        for j in range(n):
            H[i, j] = (M[i, j] + mp.conj(M[j, i])) / 2
    return mp.eigsy(mp.matrix([[mp.re(H[i, j]) for j in range(n)]
                               for i in range(n)]), eigvals_only=True)


def verdict(ev, tol=mp.mpf('1e-12')):
    lo = min(ev)
    scale = max(abs(e) for e in ev)
    if lo < -tol * max(scale, 1):
        return "INDEFINITE", lo
    return "PSD", lo


if __name__ == "__main__":
    nodes = [mp.mpc(0, 0.7), mp.mpc(1.3, 0.4), mp.mpc(-0.8, 1.1),
             mp.mpc(2.1, 0.9), mp.mpc(-1.7, 0.5)]
    print("nodes (upper half-plane):", [str(w) for w in nodes], "\n")

    # ---- K_Phi on Xi
    ev = hermitian_eigs(gram(Xi, nodes))
    v, lo = verdict(ev)
    print("K_Phi  Xi                      -> %-11s lambda_min = %s" % (v, mp.nstr(lo, 8)))

    # ---- NEG-A: signed measure
    F = lambda z: 2 * mp.cos(z) - mp.cos(2 * z)
    ev = hermitian_eigs(gram(F, nodes))
    v, lo = verdict(ev)
    print("K_Phi  NEG-A 2cos z - cos 2z   -> %-11s lambda_min = %s" % (v, mp.nstr(lo, 8)))

    # ---- K_E on Xi
    ev = hermitian_eigs(deBranges_gram(Xi, lambda z: -dXi(z), nodes))
    v, lo = verdict(ev)
    print("K_E    Xi  (A=Xi, B=-Xi')      -> %-11s lambda_min = %s" % (v, mp.nstr(lo, 8)))

    # ---- POS-B / NEG-B polynomial controls
    for label, coeffs in [("POS-B z^4-5z^2+4 (real zeros)", [1, 0, -5, 0, 4]),
                          ("NEG-B z^4-3z^2-4 (+-i pair)  ", [1, 0, -3, 0, -4])]:
        def p(z, c=coeffs):
            return mp.polyval(c, z)

        def dp(z, c=coeffs):
            d = [c[k] * (len(c) - 1 - k) for k in range(len(c) - 1)]
            return mp.polyval(d, z)

        ev = hermitian_eigs(deBranges_gram(p, lambda z: -dp(z), nodes))
        v, lo = verdict(ev)
        print("K_E    %s -> %-11s lambda_min = %s" % (label, v, mp.nstr(lo, 8)))
