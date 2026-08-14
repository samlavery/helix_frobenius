"""On Re(s)=1/2, 1-s = conj(s).  So the FE stops relating TWO points and becomes a
SELF-DUALITY CONDITION at ONE point:   conj(bank(s)) = FE-operator applied to bank(s).
Off the line 1-s != conj(s), so no such condition exists.  Test on and off."""
import mpmath as mp
mp.mp.dps = 30
z6 = mp.exp(2j*mp.pi/6)
def C(s,r):
    a = mp.mpf(r)/6 if r else mp.mpf(1)
    return mp.power(6,-s)*mp.zeta(s,a)
def Chat(s,k): return sum(mp.power(z6,k*r)*C(s,r) for r in range(6))
def FEimage(s,k):
    pref = mp.power(6,s-1)*mp.gamma(s)/mp.power(2*mp.pi,s)
    return pref*(mp.exp(-1j*mp.pi*s/2)*Chat(s,k) + mp.exp(1j*mp.pi*s/2)*Chat(s,(-k)%6))
def probe(s,tag):
    num = max(abs(mp.conj(C(s,k)) - FEimage(s,k)) for k in range(6))
    den = max(abs(C(s,k)) for k in range(6))
    print(f"  {tag:<34} max|conj(bank) - FE(bank)| / |bank| = {float(num/den):.3e}")
print("ON the critical line (1-s = conj s):")
for t in ('7.0','14.1347251417','23.5','40.0'): probe(mp.mpc('0.5',t), f"s = 1/2 + {t}i")
print("\nOFF the line (1-s != conj s):")
for sig in ('0.45','0.55','0.7','0.3'): probe(mp.mpc(sig,'14.1347251417'), f"s = {sig} + 14.1347i")
