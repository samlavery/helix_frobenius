"""att235: SEAT SIDE, move 1 — the Hankel->Toeplitz chart change (ledger 199).
Mobius w = 1/(s0 - s) sends the critical line to a circle; the zero-side data
should be TOEPLITZ (j-k) positive while Hankel (j+k) fails.  Test on the
ACTUAL zeros: is the Toeplitz form PSD, and does it DETECT an off-line
quadruple (the FE-respecting adversarial control)?"""
from mpmath import mp, mpf, mpc, matrix, eighe, nstr
mp.dps = 40
Z = [mpf(l.strip()) for l in open("tmp/zeros150_dps45.txt")][:40]
S0 = mpf(2)

def moeb(rho):  return 1/(S0 - rho)

def forms(extra=None, n=6):
    pts = [mpc(mpf(1)/2, g) for g in Z] + [mpc(mpf(1)/2, -g) for g in Z]
    if extra is not None:
        b, g = extra
        pts += [mpc(b, g), mpc(b, -g), mpc(1-b, g), mpc(1-b, -g)]
    ws = [moeb(p) for p in pts]
    T = matrix(n, n); H = matrix(n, n)
    for j in range(n):
        for k in range(n):
            T[j, k] = sum(w**j * w.conjugate()**k for w in ws)   # Toeplitz-type
            H[j, k] = sum(w**(j+k) for w in ws)                  # Hankel-type
    Th = (T + T.transpose_conj())/2
    evT = sorted(e.real for e in eighe(Th, eigvals_only=True))
    Hh = (H + H.transpose_conj())/2
    evH = sorted(e.real for e in eighe(Hh, eigvals_only=True))
    return evT, evH

print("radius check: |w - 1/(2*(S0-1/2))| for on-line points  (circle of radius r)")
c = 1/(2*(S0 - mpf(1)/2)); 
for g in Z[:3]:
    w = moeb(mpc(mpf(1)/2, g))
    print(f"   gamma={float(g):8.4f}: |w - {float(c):.4f}| = {nstr(abs(w - c),8)}  (r = {float(c):.4f})")

for label, extra in [("TRUE (all on-line)", None),
                     ("off-line quadruple beta=0.8, gamma=18", (mpf('0.8'), mpf('18')))]:
    evT, evH = forms(extra)
    nT = sum(1 for e in evT if e < -1e-25*max(abs(x) for x in evT))
    nH = sum(1 for e in evH if e < -1e-25*max(abs(x) for x in evH))
    print(f"\n{label}")
    print(f"   TOEPLITZ (Gram, j-k):  n_- = {nT}   min-eig {nstr(evT[0],5)}")
    print(f"   HANKEL   (moment, j+k): n_- = {nH}   min-eig {nstr(evH[0],5)}")
