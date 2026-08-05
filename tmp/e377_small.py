import math
X=10**9
def restricted(p,X):           # n<=X with all base-p digits <= (p-1)//2
    D=list(range(0,(p-1)//2+1)); out=[0]; pw=1
    while pw<=X:
        out=[a+d*pw for a in out for d in D if a+d*pw<=X]
        pw*=p
    return sorted(set(out))
def cf(n,p):
    while n:
        if n%p>(p-1)//2: return False
        n//=p
    return True
S=restricted(3,X)
print("n <= 1e9 with base-3 digits in {0,1}: %d of them"%len(S))
chain=[3]
cur=S
for p in [5,7,11,13,17,19,23]:
    cur=[n for n in cur if cf(n,p)]
    chain.append(p)
    Emin=sum(1.0/q for q in chain)
    big=[n for n in cur if n>0]
    print("  carry-free for %-22s : %6d values <= 1e9   max = %-12d  (E(n) >= %.4f)"
          %(str(chain),len(cur),max(big) if big else 0,Emin))
    if len(cur)<40: print("        all:",cur)
