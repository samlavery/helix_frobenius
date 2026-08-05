"""Decisive test: does the cotangent addition law's reorganisation give an ADDITIVE bound?

Compare, for two rails p,q at depth 1:
   truth   = |exact joint count - N rho_p rho_q|
   B_prod  = (1/4pq) sum |csc x||csc y| min(N, M/2|A|)            <- product form
   B_cot   = (1/4pq) sum (|cot x|+|cot y|) min(N, M/2|A|)/|sin u| <- addition law
against  P1+P2 = p+q.

x = pi*alpha/(2p), y = pi*beta/(2q), u = x+y, theta = 2u/pi, A = theta*M.
Even frequencies use sec, not csc (the two lanes).
"""
import math

def rho(p): return (p + 1) / (2 * p)

def true_err(N, p, q):
    Dp, Dq = (p - 1) // 2, (q - 1) // 2
    c = sum(1 for n in range(N) if n % p <= Dp and n % q <= Dq)
    return c - N * rho(p) * rho(q)

def amp(alpha, p):
    """|chat_p(alpha)| via the two lanes; alpha signed, |alpha|<=(p-1)/2."""
    x = math.pi * alpha / (2 * p)
    return 1 / (2 * p * abs(math.sin(x))) if alpha % 2 else 1 / (2 * p * abs(math.cos(x)))

def bounds(N, p, q):
    M = p * q
    Bp = Bc = 0.0
    for alpha in range(-(p - 1) // 2, (p - 1) // 2 + 1):
        x = math.pi * alpha / (2 * p)
        for beta in range(-(q - 1) // 2, (q - 1) // 2 + 1):
            if alpha == 0 and beta == 0: continue
            y = math.pi * beta / (2 * q)
            u = x + y
            A = alpha * q + beta * p          # = theta * M, |theta| < 1
            if A == 0: continue
            Aabs = min(abs(A), M - abs(A))    # ||theta||*M
            SN = min(N, M / (2 * Aabs))
            Bp += amp(alpha, p) * amp(beta, q) * SN
            if u != 0:
                cx = abs(1 / math.tan(x)) if alpha else 0.0
                cy = abs(1 / math.tan(y)) if beta else 0.0
                Bc += (cx + cy) * SN / abs(math.sin(u)) / (4 * M)
    return Bp, Bc

N = 12000
print(f"N = {N}\n")
print(f"{'(p,q)':>12} {'M/N':>7} {'truth':>9} {'p+q':>7} {'B_prod':>12} {'B_prod/(p+q)':>13} "
      f"{'B_cot':>12} {'B_cot/(p+q)':>12}")
print("-" * 96)
for (p, q) in [(11, 13), (31, 37), (61, 67), (101, 103), (151, 157),
               (211, 223), (307, 311), (401, 409), (13, 401), (11, 601)]:
    t = abs(true_err(N, p, q))
    Bp, Bc = bounds(N, p, q)
    print(f"{'('+str(p)+','+str(q)+')':>12} {p*q/N:>7.2f} {t:>9.1f} {p+q:>7} "
          f"{Bp:>12.1f} {Bp/(p+q):>13.2f} {Bc:>12.1f} {Bc/(p+q):>12.2f}")
