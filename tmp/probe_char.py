from sage.all import *
import sys
sys.path.insert(0,'.')
from hida_family import chi_exp, chi_mod_p, zeta12_pow_mod_p, P
from rung3_lhs import _IND31

# Build chi mod 124 in Sage, values in Q(zeta12). Match in-house chi_exp:
#   chi(n) = zeta12^{ 6*[n%4==3] + 8*(ind31(n)%3) }  (n coprime to 124)
K = CyclotomicField(12)
z12 = K.gen()
G124 = DirichletGroup(124, K)
# find generators structure
print("DirichletGroup(124,K) order:", G124.order())
# Construct chi by specifying values on generators of (Z/124)*
Zmod = Integers(124)
U = Zmod.unit_gens()
print("unit gens of (Z/124)*:", U, "orders:", [u.multiplicative_order() for u in U])

def chi_target(n):
    n = int(n)%124
    if n%2==0 or n%31==0: return None
    e = (6*(1 if n%4==3 else 0) + 8*(_IND31[n%31]%3))%12
    return z12**e

# Build chi as a Dirichlet character matching chi_target on unit gens
vals=[]
for u in U:
    vals.append(chi_target(int(u)))
print("chi on gens:", vals)
chi = G124(vals) if False else None
# Instead search DirichletGroup for the matching character
found=None
for c in G124:
    ok=True
    for n in range(1,124):
        if gcd(n,124)!=1: continue
        if c(n)!=chi_target(n):
            ok=False;break
    if ok:
        found=c;break
print("chi found in DirichletGroup(124):", found is not None)
if found is not None:
    chi=found
    print("  order:", chi.order(), " conductor:", chi.conductor())
    print("  chi(3)=",chi(3)," expect z12^2=",z12**2)
    print("  chi(13)=",chi(13)," expect z12^4=",z12**4)
    print("  chi(-1)=",chi(-1)," (odd char => -1)")
