"""
Exact root-number instrument for the CM tower psi^m / K=Q(sqrt-7), conductor 49.
Reads eps(f_m) from the epsilon-factor (archimedean phase x finite Gauss sum mod 7),
NOT from the AFE -- so there is NO precision wall: exact for ALL m, instantly.
 zeta_12-aware (tracks the mu4 quadratic-Gauss phase i explicitly).

Structure (derived):
  * ord of the finite char eps mod 7 is 2 (49a has trivial nebentypus) => eps = quadratic
    char mod 7, tau(eps)=i*sqrt7 (7=3 mod4).  The mu4 phase is exactly this.
  * m ODD  (even weight): trivial nebentypus, eps(f_m)=i^{m+1}*w_m, w_m the Atkin-Lehner sign.
  * m EVEN (odd weight):  quadratic nebentypus eps, eps(f_m)=i^{m+1}*(tau(eps)/sqrt7)*w'_m.
Goal: fit the exact formula to the 17 reliable measured signs, then EXTEND to settle
whether m=2 is the ONLY exception (Sam's doubt) or the even-m Atkin-Lehner sign varies.
"""
import mpmath as mp
mp.mp.dps = 40
I = mp.mpc(0, 1)
z7 = mp.e ** (2 * mp.pi * I / 7)

# quadratic residues mod 7: {1,2,4}; Legendre (a/7)
QR = {1, 2, 4}
def leg7(a):
    a %= 7
    return 0 if a == 0 else (1 if a in QR else -1)

# order-6 character mod 7, chi(3)=zeta6^j  (3 is a primitive root mod 7)
def ind3(a):
    a %= 7
    for k in range(6):
        if pow(3, k, 7) == a:
            return k
    raise ValueError
def chi6(a, j):
    return mp.e ** (2 * mp.pi * I * j * ind3(a) / 6)

def gauss6(j):   # sum_{a} chi6(a,j) z7^a  (j=0 -> trivial char -> -1)
    return sum((chi6(a, j) * z7 ** a for a in range(1, 7)), mp.mpc(0))
def gauss_quad():   # tau(eta7) = sum leg7(a) z7^a  == i*sqrt7
    return sum((leg7(a) * z7 ** a for a in range(1, 7)), mp.mpc(0))

tau_eta = gauss_quad()
print("tau(eta_7) = %s   (expect i*sqrt7 = %.6f i)" % (mp.nstr(tau_eta, 8), float(mp.sqrt(7))))
print("gauss6(j) phases /2pi, j=0..5:",
      [mp.nstr(mp.arg(gauss6(j) if abs(gauss6(j)) > 1e-9 else mp.mpc(-1)) / (2 * mp.pi), 4) for j in range(6)])

# measured reliable signs m=1..17
MEAS = {1:+1,2:-1,3:-1,4:-1,5:+1,6:+1,7:-1,8:-1,9:+1,10:+1,11:-1,12:-1,13:+1,14:+1,15:-1,16:-1,17:+1}

def sign_of(w):
    return +1 if w.real > 0 else -1

# ---- candidate epsilon-factor families -----------------------------------------
# W_m = kappa * i^{aexp*(m+1)} * (gauss factor)_m ;  kappa calibrated from m=1.
def gauss_factor(kind, m):
    if kind == "none":
        return mp.mpc(1)
    if kind == "quad_even":       # include tau(eta)/sqrt7 only for odd weight (m even)
        return (tau_eta / mp.sqrt(7)) if (m % 2 == 0) else mp.mpc(1)
    if kind == "quad_all":        # include for all m
        return tau_eta / mp.sqrt(7)
    if kind == "eps_m":           # normalized Gauss sum of eps^m ... eps quadratic so eps^m
        j = 3 * (m % 2)           # eps=eta=chi6^3 ; eps^m = trivial (m even) or eta (m odd)
        gg = gauss6(j)
        return gg / abs(gg)
    raise ValueError

def run_candidate(aexp, kind):
    # calibrate kappa so predicted(m=1) matches measured(m=1)
    raw1 = I ** (aexp * 2) * gauss_factor(kind, 1)          # m=1 -> i^{aexp*2}
    # choose kappa in {1,-1,i,-i} minimizing imaginary part & fixing sign
    best = None
    for kap in [mp.mpc(1), mp.mpc(-1), I, -I]:
        w1 = kap * raw1
        if abs(w1.imag) < 1e-6 and sign_of(w1) == MEAS[1]:
            best = kap
            break
    if best is None:
        return None, None, None
    preds, matches, realres = {}, 0, True
    for m in range(1, 18):
        w = best * I ** (aexp * (m + 1)) * gauss_factor(kind, m)
        if abs(w.imag) > 1e-6:
            realres = False
        s = sign_of(w)
        preds[m] = s
        if s == MEAS[m]:
            matches += 1
    return best, matches, (preds, realres)

print("\n== candidate fits to 17 measured signs ==")
print(" aexp  gaussKind      kappa     realQ  matches/17")
winners = []
for aexp in (+1, -1):
    for kind in ("none", "quad_even", "quad_all", "eps_m"):
        kap, matches, extra = run_candidate(aexp, kind)
        if kap is None:
            print(" %+d   %-11s   (no real calibration)" % (aexp, kind))
            continue
        preds, realQ = extra
        print(" %+d   %-11s  %8s   %-5s   %d/17" % (aexp, kind, mp.nstr(kap, 4), str(realQ), matches))
        if matches == 17 and realQ:
            winners.append((aexp, kind, kap))

print("\n== winners reproducing ALL 17 signs with real W_m ==", [(a, k) for a, k, _ in winners])
for (aexp, kind, kap) in winners[:2]:
    print("\n-- extending winner (aexp=%+d, kind=%s) to m=1..48 --" % (aexp, kind))
    seq, exc_even = [], []
    for m in range(1, 49):
        w = kap * I ** (aexp * (m + 1)) * gauss_factor(kind, m)
        s = sign_of(w)
        seq.append('+' if s > 0 else '-')
        if m % 2 == 0:                      # even m = odd weight = the frontier
            cong = +1 if (m % 4 == 2) else -1
            if s != cong:
                exc_even.append(m)
    print("  eps(psi^m), m=1..48:")
    print("   " + " ".join("%s%s" % (('%2d' % m), '') for m in range(1, 49)))
    print("   " + "  ".join(seq))
    print("  EVEN-m exceptions to the naive congruence (m==2 mod4 -> +):", exc_even)
