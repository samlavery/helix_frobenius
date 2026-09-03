import sympy as sp

print("="*70); print("STEP 1: n=2, nodes +-s, unit weights")
s = sp.symbols('s')
nodes=[s,-s]; wts=[1,1]
m=[sp.simplify(sum(w*x**k for x,w in zip(nodes,wts))) for k in range(3)]
print("  m0,m1,m2 =", m)
H=sp.Matrix([[m[i+j] for j in range(2)] for i in range(2)])
dH=sp.simplify(H.det()); print("  det H =", sp.factor(dH))
tau=sp.symbols('tau')
dH_tau=sp.simplify(dH.subs(s**2,tau)); dH_tau=sp.expand(dH_tau.rewrite(sp.Pow))
dH_tau=sp.simplify(4*tau)  # det H = 4 s^2 = 4 tau
print("  in tau=s^2 :", dH_tau, "   d/dtau =", sp.diff(dH_tau,tau))
# sanity: tau<0 -> nodes +- i sqrt(-tau)
print("  check tau=-1 nodes:", [sp.simplify(x.subs(s, sp.I)) for x in nodes], " det H =", dH.subs(s,sp.I))

print("="*70); print("STEP 2: conjugate pair w d_z + wbar d_zbar")
x,y,u,v = sp.symbols('x y u v', real=True)
z=x+sp.I*y; w=u+sp.I*v
nodes=[z,sp.conjugate(z)]; wts=[w,sp.conjugate(w)]
m=[sp.simplify(sp.expand(sum(ww*xx**k for xx,ww in zip(nodes,wts)))) for k in range(3)]
print("  m0,m1,m2 =", [sp.simplify(sp.re(mm)) for mm in m])
H=sp.Matrix([[m[i+j] for j in range(2)] for i in range(2)])
dH=sp.factor(sp.simplify(sp.expand(H.det())))
print("  det H =", dH)

print("="*70); print("STEP 3: sign of disc for real monic p, by number r2 of conj pairs")
X=sp.symbols('X')
cases={
 "(a) n=4 all real distinct  (r2=0)": [1,2,3,4],
 "(b) n=4 one conj pair      (r2=1)": [1,2,sp.Rational(1,2)+sp.I, sp.Rational(1,2)-sp.I],
 "(c) n=4 two conj pairs     (r2=2)": [sp.I,-sp.I, 2+3*sp.I, 2-3*sp.I],
 "    n=3 all real           (r2=0)": [0,1,5],
 "    n=3 one conj pair      (r2=1)": [5,sp.I,-sp.I],
}
for name,rts in cases.items():
    p=sp.expand(sp.prod([X-r for r in rts]))
    D=sp.simplify(sp.discriminant(sp.Poly(p,X)))
    prod_diff=sp.simplify(sp.prod([(rts[i]-rts[j])**2 for i in range(len(rts)) for j in range(i+1,len(rts))]))
    print(f"  {name}: poly={sp.nsimplify(p)}")
    print(f"      disc={D}  sign={sp.sign(D)}   prod(xi-xj)^2={prod_diff}")

print("="*70); print("IDENTITY CHECK det H = (prod w_i) * disc(p)   [symbolic, n=3]")
a,b,c,w1,w2,w3=sp.symbols('a b c w1 w2 w3')
nodes=[a,b,c]; wts=[w1,w2,w3]
m=[sp.expand(sum(ww*xx**k for xx,ww in zip(nodes,wts))) for k in range(5)]
H=sp.Matrix([[m[i+j] for j in range(3)] for i in range(3)])
lhs=sp.factor(sp.expand(H.det()))
rhs=sp.factor(w1*w2*w3*sp.prod([(nodes[i]-nodes[j])**2 for i in range(3) for j in range(i+1,3)]))
print("  det H     =", lhs)
print("  prod w*disc=", rhs)
print("  difference =", sp.simplify(sp.expand(lhs-rhs)))
