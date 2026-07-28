# 2026-07-29 — coupled/ledgered version of the depth-2 carrier test.
# Claims to check:
# (1) x=0 crossings with theta_n = (pi/3)*H_n occur EXACTLY at
#     H_n = 3/2 + 3k  (pure phase arithmetic, RADIUS-IMMUNE:
#     R cos(theta) = 0 iff cos(theta) = 0 for R != 0)  -> the observed
#     1.5, 4.5, 7.5 are real phase events, NOT shrinkage artifacts.
# (2) Closure (return-to-start) DOES need the ledger: unnormalized
#     residue shrinks with R (fake closure); radius-booked residue
#     (unit-normalized phasor) shows the true rotational state.
# (3) H*H_n phases are the corpus phases up to Euler-Mascheroni:
#     H_n = log n + gamma + O(1/n) -> their "imposed" law converges to
#     the carrier's t*log n law; and R = n^{-1/2} is the area-balanced
#     exponent. Their guesses were the corpus laws in disguise.
import numpy as np
H = np.pi/3
Hn = 0.0
crossings = []
prev = None
gamma = 0.5772156649
print("n     H_n      theta/pi   x-sign  |  H_n - (log n + gamma)")
for n in range(1, 2001):
    Hn += 1.0/n
    theta = H*Hn
    x = np.cos(theta)          # unit-normalized (radius booked out)
    if prev is not None and np.sign(x) != np.sign(prev):
        crossings.append(Hn)
    prev = x
    if n in (2, 5, 33, 226, 1014):
        print(f"{n:<5} {Hn:.4f}  {theta/np.pi:.4f}    {np.sign(x):+.0f}    |  {Hn - (np.log(n)+gamma):+.5f}")
pred = [1.5 + 3*k for k in range(4)]
print("\ncrossing H_n values:", [round(c,4) for c in crossings[:4]])
print("predicted 3/2 + 3k :", pred)
# (2) closure residue: return of the composite configuration after one mu6
# cell, unnormalized vs radius-booked
for style in ("unnormalized", "ledgered"):
    res = []
    for n0 in (10, 100, 1000):
        R = n0**-0.5
        # six harmonic steps from n0: accumulated phase increments H/k
        dth = sum(H/k for k in range(n0, n0+6))
        v_un = R*np.array([np.cos(dth)-1, np.sin(dth)])     # displacement incl radius
        v_led = np.array([np.cos(dth)-1, np.sin(dth)])      # radius booked out
        res.append(np.linalg.norm(v_un if style=="unnormalized" else v_led))
    print(f"{style:>13} residues at n0=10,100,1000: " + "  ".join(f"{r:.5f}" for r in res))
