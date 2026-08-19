"""att219: SEAT CLOSURE ATTEMPT, move 1 — sweep the FE-paired family's own
boundary detector along a realizable transport path.

Form: A_jk(s) = sum_rho (s-rho)^{-(j+1)} (sbar-1+rho)^{-(k+1)}  (hermitian by
FE+conjugation closure; on-line atoms contribute |P|^2 termwise).
Path: deep anchor (sigma=2, tau=0; Euler territory, positivity expected
unconditional) -> lift into the strip to a window seating (sigma=0.9,
tau=21.02 = gamma_2).  Detector: det A_{n+1}/det A_n (the boundary scalar of
this chart) and min-eig, n = 1..8, at stations along the path."""
from mpmath import mp, mpf, mpc, matrix, det, eighe, nstr

mp.dps = 60
Z = [mpf(l.strip()) for l in open("tmp/zeros150_dps45.txt")]
NMAX = 9

def form(s, n):
    A = matrix(n, n)
    for j in range(n):
        for k in range(n):
            tot = mpc(0)
            for g in Z:
                for sgn in (1, -1):
                    rho = mpc(mpf(1)/2, sgn*g)
                    tot += (s-rho)**(-(j+1)) * (s.conjugate()-(1-rho))**(-(k+1))
            A[j, k] = tot
    return (A + A.transpose_conj())/2

def station(s, label):
    A = form(s, NMAX)
    dets = []
    for n in range(1, NMAX+1):
        dets.append(det(A[:n, :n]).real)
    ratios = [dets[0]] + [dets[i]/dets[i-1] for i in range(1, NMAX)]
    ev = [e.real for e in eighe(A, eigvals_only=True)]
    nneg = sum(1 for e in ev if e < 0)
    # noise floor: entries scale
    scale = max(abs(A[i,j]) for i in range(NMAX) for j in range(NMAX))
    print(f"{label:28s} nneg={nneg}  min-eig={nstr(min(ev),3):>12}  "
          f"scale={nstr(scale,2):>9}  det-ratios(sign) "
          + "".join('+' if r > 0 else '-' for r in ratios), flush=True)

# path: leg 1 sigma 2 -> 0.9 at tau=0; leg 2 tau 0 -> 21.02 at sigma=0.9
print("=== leg 1: descend sigma at tau=0 (Euler -> strip edge) ===")
for sig in ['2.0','1.5','1.1','0.9']:
    station(mpc(mpf(sig), 0), f"s = {sig}")
print("=== leg 2: lift tau at sigma=0.9 (into the window, through seatings) ===")
for tau in ['2','8','13','14.13','16','19','21.02','23','25.01']:
    station(mpc(mpf('0.9'), mpf(tau)), f"s = 0.9 + {tau}i")
