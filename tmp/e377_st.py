import math, random
from mpmath import mp, siegeltheta, zetazero
mp.dps=30
C=[0,1,10,756,757,3160,3186,3187,3250,7560,7561,7651,20007,59548377,59548401,45773612811,45775397187]
C=[n for n in C if n>2]
print("census {3,5,7}, n>2 :",len(C),"values\n")
print("  n              log n     theta(log n)/pi   frac      n mod 6   nearest gamma_k gap")
zs=[float(zetazero(k).imag) for k in range(1,60)]
fr=[]
for n in C:
    t=math.log(n); th=float(siegeltheta(t))/math.pi; f=th-math.floor(th)
    g=min(zs,key=lambda z:abs(z-t)); fr.append(f)
    print("  %-14d %-9.4f %-17.5f %-9.5f %-9d %+.4f"%(n,t,th,f,n%6,t-g))
# pre-registered: KS test of frac(theta/pi) vs uniform, and of frac(log n / log 2)
def ks(x):
    x=sorted(x); m=len(x)
    return max(max(abs((i+1)/m-v),abs(v-i/m)) for i,v in enumerate(x))
print("\nPRE-REGISTERED uniformity tests (reject at KS > 1.36/sqrt(m) = %.4f for m=%d)"%(1.36/math.sqrt(len(C)),len(C)))
tests={"frac theta(log n)/pi":fr,
       "frac log n":[math.log(n)%1 for n in C],
       "frac log_2 n":[math.log(n,2)%1 for n in C],
       "frac log_3 n":[math.log(n,3)%1 for n in C]}
for name,v in tests.items():
    print("   %-24s KS = %.4f   %s"%(name,ks(v),"SIGNIFICANT" if ks(v)>1.36/math.sqrt(len(C)) else "null"))
random.seed(0)
ctrl=[ks([math.log(random.randrange(3,10**11))%1 for _ in C]) for _ in range(2000)]
print("   control (random n, frac log n): mean KS %.4f, 95th %.4f"%(sum(ctrl)/len(ctrl),sorted(ctrl)[1900]))
