import sys
sys.setrecursionlimit(10000)
def cf(n,p):
    while n:
        if n%p>(p-1)//2: return False
        n//=p
    return True
def search(X, others):
    """all n<=X with base-3 digits in {0,1} and carry-free for each p in others"""
    J=0
    while 3**(J+1)<=X: J+=1
    pw3=[3**i for i in range(J+2)]
    maxadd=[(3**(i+1)-1)//2 for i in range(J+2)]
    res=[]; nodes=0
    def locked_ok(v,hi,p):
        pm=1
        while pm<=hi:
            if v//pm==hi//pm:
                if (v//pm)%p>(p-1)//2: return False
            pm*=p
        return True
    def rec(i,v):
        nonlocal nodes
        nodes+=1
        hi=v+(maxadd[i] if i>=0 else 0)
        if v>X: return
        if hi>X: hi=X
        for p in others:
            if not locked_ok(v,hi,p): return
        if i<0:
            if all(cf(v,p) for p in others): res.append(v)
            return
        rec(i-1,v+pw3[i]); rec(i-1,v)
    rec(J,0)
    return sorted(res), nodes

for X,others in [(10**13,[5,7]), (10**16,[5,7,11]), (10**16,[5,7,11,13])]:
    r,nd=search(X,others)
    tag="{3,"+",".join(map(str,others))+"}"
    print("%-16s up to %-6s : %3d solutions, %d tree nodes"%(tag,"1e%d"%len(str(X)[1:]),len(r),nd))
    print("     ",r if len(r)<30 else r[:12]+["..."]+r[-6:])
