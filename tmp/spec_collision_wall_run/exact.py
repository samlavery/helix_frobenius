import sympy as sp, itertools
def detH_exact(nodes,wts,n):
    m=[sp.expand(sum(w*x**k for x,w in zip(nodes,wts))) for k in range(2*n-1)]
    for k,mm in enumerate(m):
        assert sp.simplify(sp.im(sp.expand(sp.nsimplify(mm))))==0, ("m_%d not real"%k, mm)
    H=sp.Matrix([[m[i+j] for j in range(n)] for i in range(n)])
    return sp.simplify(sp.expand(H.det())), m

print("ATTACK A (exact): n=4, weights 1,1,1,1")
for lab,s in [("t=0   (tau=+1)",sp.Integer(1)),("t=1/2 (tau=0)",sp.Integer(0)),
              ("t=1   (tau=-1)",sp.I)]:
    nodes=[s,-s,3+s,3-s]
    d,m=detH_exact(nodes,[1,1,1,1],4)
    print("  %-16s nodes=%s"%(lab,[sp.nsimplify(x) for x in nodes]))
    print("      moments m0..m6 = %s"%[sp.nsimplify(mm) for mm in m])
    print("      det H = %s   (EXACT, >=0)"%d)

print("\nATTACK B (exact): n=3, nodes {5,s,-s}, weights {tau,1,1}, tau=s^2")
for lab,s,tau in [("t=0   (tau=+1/2)",sp.sqrt(sp.Rational(1,2)),sp.Rational(1,2)),
                  ("t=1/2 (tau=0)",sp.Integer(0),sp.Integer(0)),
                  ("t=1   (tau=-1/2)",sp.I*sp.sqrt(sp.Rational(1,2)),sp.Rational(-1,2))]:
    nodes=[sp.Integer(5),s,-s]; wts=[tau,1,1]
    d,m=detH_exact(nodes,wts,3)
    print("  %-17s nodes=%s  weights=%s"%(lab,[sp.nsimplify(x) for x in nodes],wts))
    print("      det H = %s   (EXACT, >=0)"%sp.nsimplify(d))

print("\nATTACK C (exact): n=4, t=3/4 -- moments real though nodes are NOT conj-paired")
u=sp.Rational(1,2)
nodes=[sp.Integer(-1),sp.Integer(0),1+sp.I*u,2-u*(1+sp.I)]
wts=[1,1,0,0]
d,m=detH_exact(nodes,wts,4)
print("  nodes =",nodes)
print("  conj of node3 =",sp.conjugate(nodes[2]),"; node4 =",nodes[3],
      "  equal?",sp.simplify(sp.conjugate(nodes[2])-nodes[3])==0)
print("  moments m0..m6 =",m,"  (ALL REAL)")
print("  det H =",d,"  -> identically 0 on the whole interval t in [1/2,1]")
print("  pairwise node gaps:",[sp.nsimplify(sp.Abs(nodes[i]-nodes[j])) for i,j in itertools.combinations(range(4),2)])
