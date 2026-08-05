import sys; sys.setrecursionlimit(200000)
def cf(n,p):
    while n:
        if n%p>(p-1)//2: return False
        n//=p
    return True
def profile(X, others):
    J=0
    while 3**(J+1)<=X: J+=1
    pw3=[3**i for i in range(J+2)]; maxadd=[(3**(i+1)-1)//2 for i in range(J+2)]
    live={}; res=[]
    def ok(v,hi,p):
        pm=1
        while pm<=hi:
            if v//pm==hi//pm and (v//pm)%p>(p-1)//2: return False
            pm*=p
        return True
    def rec(i,v):
        if v>X: return
        hi=min(v+(maxadd[i] if i>=0 else 0),X)
        for p in others:
            if not ok(v,hi,p): return
        live[J-i]=live.get(J-i,0)+1
        if i<0:
            if all(cf(v,p) for p in others): res.append(v)
            return
        rec(i-1,v+pw3[i]); rec(i-1,v)
    rec(J,0); return live,sorted(res),J
X=10**200
for others in [[5,7,11],[5,7,11,13]]:
    live,res,J=profile(X,others)
    ls=[live.get(d,0) for d in range(1,J+2)]
    print("{3,"+",".join(map(str,others))+"}  depth %d, solutions %s"%(J,res))
    print("   live nodes per level (depth 1..%d):"%(J+1))
    print("   ",ls[:40])
    print("    tail:",ls[-40:])
    import collections
    print("    width histogram:",dict(sorted(collections.Counter(ls[20:]).items())))
    print()
