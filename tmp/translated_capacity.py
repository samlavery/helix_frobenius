"""Corrected capacity: at step j, admissible set = union over translations
b in (lower-half p-cell mod p^{j-1}) reduced mod r^2 of rho_j^{-1}(L - b).
Intersection over j = true exclusion capacity of the rotated-cell mechanism."""
import numpy as np
from itertools import product
for (p,r) in [(3,5),(3,7),(5,7),(3,11),(7,11),(5,13)]:
    m=r*r
    L=np.array([(x%r<=(r-1)//2) and ((x//r)%r<=(r-1)//2) for x in range(m)],bool)
    cur=np.ones(m,bool)
    sizes=[]
    for j in range(1,12):
        # translations: lower-half p-digit values mod p^{j-1}, reduced mod m
        digs=range((p+1)//2)
        if j==1:
            B={0}
        else:
            B=set()
            for tup in product(digs,repeat=min(j-1,8)):   # cap enumeration
                v=0
                for t,d in enumerate(tup): v+=d*p**t
                B.add(v%m)
                if len(B)==m: break
        rot=pow(p,-(j-1),m) if j>1 else 1
        adm=np.zeros(m,bool)
        for b in B:
            for x in range(m):
                if adm[x]: continue
                if L[((x - 0) * 1)%m]: pass
            # q_j = (a - b)*p^{-(j-1)}; a in L. x=a admissible iff EXISTS...(no: identity holds
            # automatically). Exclusion only if we DEMAND q_j in L: admissible a iff
            # exists b in B with ((a-b)*rot)%m in L  -- union over translations
            pass
        for b in B:
            shifted=np.array([L[((a-b)*rot)%m] for a in range(m)],bool)
            adm|=shifted
            if adm.all(): break
        cur&=adm
        sizes.append(int(cur.sum()))
        if len(B)>=m and adm.all() and j>3: break
    print(f"(p,r)=({p},{r}): |Z/r^2|={m}, admissible-intersection sizes by j: {sizes}")
