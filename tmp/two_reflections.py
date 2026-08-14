"""What does the FE ACTUALLY do to the cell-channel vector?
Hurwitz:  zeta(1-s,a) = (Gamma(s)/(2pi)^s)[e^{-i pi s/2} Li_s(e^{2 pi i a}) + e^{+i pi s/2} Li_s(e^{-2 pi i a})]
With a = r/6, e^{2 pi i a} = zeta_6^r, and
    Li_s(zeta_6^k) = sum_n zeta_6^{kn}/n^s = sum_r zeta_6^{kr} C_r(s)   = the DFT on Z/6 of the bank.
So the FE carries the bank at s to the bank at 1-s THROUGH THE DFT.  Test it."""
import mpmath as mp
mp.mp.dps = 30
z6 = mp.exp(2j*mp.pi/6)

def C(s, r):                                  # channel r = n mod 6
    a = mp.mpf(r)/6 if r else mp.mpf(1)
    return mp.power(6,-s)*mp.zeta(s, a)

def Chat(s, k):                               # DFT on Z/6
    return sum(mp.power(z6, k*r)*C(s, r) for r in range(6))

s = mp.mpc('2.3','4.0')
print("(1) indexing check:  DFT of the bank  ==  Li_s at the 6th roots of unity")
for k in range(6):
    print(f"    k={k}:  |Chat - Li_s(z6^k)| = {float(abs(Chat(s,k) - mp.polylog(s, mp.power(z6,k)))):.2e}")

print("\n(2) THE FUNCTIONAL EQUATION IN THE CELL BASIS")
print("    claim:  C_k(1-s) = 6^{s-1} Gamma(s)/(2pi)^s [ e^{-i pi s/2} Chat(k) + e^{+i pi s/2} Chat(-k) ]")
pref = mp.power(6, s-1)*mp.gamma(s)/mp.power(2*mp.pi, s)
em, ep = mp.exp(-1j*mp.pi*s/2), mp.exp(1j*mp.pi*s/2)
for k in range(6):
    lhs = C(1-s, k)
    rhs = pref*(em*Chat(s,k) + ep*Chat(s,(-k) % 6))
    print(f"    k={k}:  |LHS-RHS| = {float(abs(lhs-rhs)):.2e}   (|LHS| = {float(abs(lhs)):.3f})")

print("\n(3) PROJECT ONTO THE R-EIGENSPACES  (R: k -> -k).  R-even picks e^-+e^+ = 2cos(pi s/2);")
print("    R-odd picks e^- - e^+ = -2i sin(pi s/2).  These are exactly the two FE trig factors.")
print(f"    2cos(pi s/2)   = {mp.nstr(2*mp.cos(mp.pi*s/2),12)}")
print(f"    -2i sin(pi s/2)= {mp.nstr(-2j*mp.sin(mp.pi*s/2),12)}")
print("    -> zeta's FE carries cos(pi s/2); an ODD character's carries sin(pi s/2).")
