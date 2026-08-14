"""Was my 'criterion' doing any work, or was it restating  conj(s) = 1-s ?
If the FE played NO role, then
     |conj(bank(s)) - FE(bank(s))|   ==   |bank(conj s) - bank(1-s)|
identically -- the second expression never mentions the functional equation, or zeta's
properties at all.  And the residual should depend ONLY on sigma, not on the function."""
import mpmath as mp
mp.mp.dps = 30
z6 = mp.exp(2j*mp.pi/6)
def C(s,r):
    a = mp.mpf(r)/6 if r else mp.mpf(1)
    return mp.power(6,-s)*mp.zeta(s,a)
def Chat(s,k): return sum(mp.power(z6,k*r)*C(s,r) for r in range(6))
def FEimage(s,k):
    pref = mp.power(6,s-1)*mp.gamma(s)/mp.power(2*mp.pi,s)
    return pref*(mp.exp(-1j*mp.pi*s/2)*Chat(s,k)+mp.exp(1j*mp.pi*s/2)*Chat(s,(-k)%6))

print("  sigma    t        my 'criterion'      bank(conj s) vs bank(1-s)     zeta(s)=0?")
for sig,t in [('0.5','7.0'),('0.5','14.1347251417'),('0.5','23.5'),('0.5','40.0'),
              ('0.45','14.1347251417'),('0.55','14.1347251417'),('0.7','14.1347251417')]:
    s = mp.mpc(sig,t)
    mine = max(abs(mp.conj(C(s,k))-FEimage(s,k)) for k in range(6))
    naive= max(abs(C(mp.conj(s),k)-C(1-s,k))    for k in range(6))
    den  = max(abs(C(s,k)) for k in range(6))
    isz  = "ZERO" if abs(mp.zeta(s))<1e-8 else "not a zero"
    print(f"  {sig:>5}  {t:>14}   {float(mine/den):.3e}          {float(naive/den):.3e}"
          f"        {isz}")
print("\nIf columns 3 and 4 agree, the functional equation contributed NOTHING:")
print("the test was measuring  conj(s) == 1-s,  i.e. the DEFINITION of the critical line.")
