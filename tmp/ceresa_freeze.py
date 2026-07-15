"""
ceresa_freeze.py -- point the multi-rail freeze-mass meter at the Ceresa channel.
Uses ap_hecke(p,3) from ceresa_lside (L(psi^3,s) = 49.4.a.a, weight 4, CM by Q(sqrt-7)).
freeze mass = avg_p |a_p|^2 / p^(k-1),  k=4 => /p^3.  Reads the GRADE-1 rail count of the
Ceresa CHANNEL motive.  (The Ceresa CYCLE itself is grade 2, homologically trivial:
L'(center)=0.8299 != 0 detects it -- the jet/height channel, NOT the freeze mass.)
"""
import sys, importlib.util
spec = importlib.util.spec_from_file_location("cl", "/Users/samuellavery/work/helix_frobenius/tmp/ceresa_lside.py")
cl = importlib.util.module_from_spec(spec)
try:
    spec.loader.exec_module(cl)
except SystemExit:
    pass

def sieve(n):
    s = [True]*n; s[0]=s[1]=False
    for i in range(2,int(n**0.5)+1):
        if s[i]:
            for j in range(i*i,n,i): s[j]=False
    return [i for i in range(2,n) if s[i]]

P = [p for p in sieve(6000) if p != 7]
split = inert = 0
tot = 0.0
for p in P:
    a = cl.ap_hecke(p, 3)
    tot += (a*a) / p**3
    if abs(a) < 1e-9: inert += 1
    else: split += 1
mass = tot / len(P)
print("== Ceresa channel L(psi^3) freeze mass (grade-1 rail meter) ==")
print("primes: %d  (split=%d, inert/ram=%d)" % (len(P), split, inert))
print("freeze mass avg|a_p|^2/p^3 = %.4f   (irreducible CM form => 1 rail)" % mass)
print("--")
print("Ceresa CYCLE (grade 2, Griffiths, homolog. trivial): L'(center)=%.6f != 0" % cl.ORACLE_LDER_PSI3)
print("=> detected by the jet/height channel, NOT the freeze mass (grade-1 meter is silent on it).")
