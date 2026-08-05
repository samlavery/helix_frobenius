"""CARRIER-NATIVE SAMPLING.  Do not count in Lebesgue; count in rail 3's own measure.
   G_3 cap [1,3^k] is exactly 2^k points -- enumerate them, then read rail 5.
   If the residual is o(main term) the intersection resolves; if it is
   square-root in the SAMPLING measure it does not."""
import math
b=lambda p: math.log(2*p/(p+1))/math.log(p)
d35=1-b(3)-b(5)
print(f"beta_3={b(3):.6f}  beta_5={b(5):.6f}   dim{{3,5}}={d35:.6f}\n")
print(f"{'k':>3} {'N=3^k':>14} {'|G3|=2^k':>10} {'|G3^G5|':>9} {'N^dim':>9} "
      f"{'ratio':>7} {'resid':>9} {'sqrt|G3|':>9} {'resid/sqrt':>10}")
print("-"*98)
cur=[0]
for k in range(1,25):
    pw=3**(k-1)
    cur=[x for x in cur]+[x+pw for x in cur]      # all base-3 {0,1} numbers < 3^k
    N=3**k
    def bal5(n):
        while n:
            if n%5>2: return False
            n//=5
        return True
    c=sum(1 for x in cur if x>0 and bal5(x))
    main=N**d35
    resid=abs(c-main); s=math.sqrt(len(cur))
    if k>=8:
        print(f"{k:>3} {N:>14} {len(cur):>10} {c:>9} {main:>9.2f} "
              f"{c/main:>7.3f} {resid:>9.2f} {s:>9.1f} {resid/s:>10.4f}")
