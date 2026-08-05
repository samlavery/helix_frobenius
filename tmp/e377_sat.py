import sys, math
sys.setrecursionlimit(100000)
def cf(n,p):
    while n:
        if n%p>(p-1)//2: return False
        n//=p
    return True
def search(X, others):
    J=0
    while 3**(J+1)<=X: J+=1
    pw3=[3**i for i in range(J+2)]; maxadd=[(3**(i+1)-1)//2 for i in range(J+2)]
    res=[]; nodes=0; deepest=0
    def ok(v,hi,p):
        pm=1
        while pm<=hi:
            if v//pm==hi//pm and (v//pm)%p>(p-1)//2: return False
            pm*=p
        return True
    def rec(i,v):
        nonlocal nodes,deepest
        nodes+=1; deepest=max(deepest,J-i)
        if v>X: return
        hi=min(v+(maxadd[i] if i>=0 else 0),X)
        for p in others:
            if not ok(v,hi,p): return
        if i<0:
            if all(cf(v,p) for p in others): res.append(v)
            return
        rec(i-1,v+pw3[i]); rec(i-1,v)
    rec(J,0); return sorted(res),nodes,deepest

print("SATURATION TEST: does the pruned tree close?  (bounded nodes => finiteness PROOF)")
for others in [[5,7,11],[5,7,11,13]]:
    tag="{3,"+",".join(map(str,others))+"}"
    print("\n "+tag)
    print("   X        #sol   nodes   max depth   log3(X)")
    for e in [16,25,40,70,120,200]:
        X=10**e; r,nd,dp=search(X,others)
        print("   1e%-7d %-6d %-7d %-11d %d"%(e,len(r),nd,dp,int(math.log(X,3))))
print()
print("HARMONIC SCAN of the measured constants")
c={"band1 ratio N=1e7":1.041148,"kappa=3log(3/2)/log3":3*math.log(1.5)/math.log(3),
   "threshold 1/kappa":math.log(3)/(3*math.log(1.5)),
   "sum_j log j/2^j":sum(math.log(j)/2**j for j in range(2,300)),
   "max E(n) at 1e6":0.8046}
H={"pi/6":math.pi/6,"pi/3":math.pi/3,"pi/2":math.pi/2,"pi":math.pi,"2pi":2*math.pi,"3pi":3*math.pi}
for kn,kv in c.items():
    best=min(((abs(kv-hv)/hv,hn,hv) for hn,hv in H.items()))
    print("  %-24s = %.6f   nearest %-4s (%.6f)  rel err %+.2f%%"%(kn,kv,best[1],best[2],100*(kv-best[2])/best[2]))
