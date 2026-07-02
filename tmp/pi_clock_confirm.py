"""Confirm the 4.206 line = ln(67) (split prime) not 4pi/3, and write final results."""
import math
import numpy as np

# rebuild a small chunk of coefficients to check a_67 directly
def eta_sq_dilated(N, d):
    c = np.zeros(N, dtype=np.float64); k = 0
    while True:
        done = True
        for kk in (k, -k) if k else (0,):
            m = d * (kk * (3 * kk - 1) // 2)
            if 0 <= m < N: c[m] += (-1) ** kk; done = False
        if k and done: break
        k += 1
    L = 1
    while L < 2 * N: L *= 2
    f = np.fft.rfft(c, L)
    return np.round(np.fft.irfft(f * f, L)[:N])
N = 200
A = eta_sq_dilated(N,3); B = eta_sq_dilated(N,9)
L=1
while L<2*N: L*=2
prod = np.round(np.fft.irfft(np.fft.rfft(A,L)*np.fft.rfft(B,L),L)[:N])
a = np.zeros(N+1); a[1:]=prod[:N]
# 67 = 1 mod 3 -> split prime, should be nonzero
print("a_67  =", int(a[67]), " (67 mod 3 =", 67%3, "-> split, expect nonzero)")
print("a_61  =", int(a[61]), " (61 mod 3 =", 61%3, ")")
print("a_31  =", int(a[31]), " (31 mod 3 =", 31%3, "-> inert, expect 0)")
print("a_64  =", int(a[64]), " (2-tower k=6: 2^6)")
print("check: 4pi/3=%.5f  ln67=%.5f  ln64=%.5f  measured peak~4.2065" % (4*math.pi/3, math.log(67), math.log(64)))
print("  -> ln67 is the match (d=%.4f vs 4pi/3 d=%.4f)" % (abs(math.log(67)-4.2065), abs(4*math.pi/3-4.2065)))
