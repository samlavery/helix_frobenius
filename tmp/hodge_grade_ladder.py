"""
hodge_grade_ladder.py -- compute the step-4 recognition signature UP THE GRADES.
CM channels psi^m over K=Q(sqrt-7): psi^m = the m-th cohomological grade (Sym^m-CM piece).
For each grade m:  sign eps(psi^m), central value L(1/2), central deriv L'(1/2) if L=0.
The signature: eps=-1  => L(center)=0 forced => a HIDDEN higher cycle fires (ord>=1);
               eps=+1  => L(center)!=0        => algebraic/decorated (ord 0).
Look for the PATTERN in eps(m) and the firing grade as m climbs -- the step-4 law.
"""
import importlib.util, sys
spec = importlib.util.spec_from_file_location("cl", "/Users/samuellavery/work/helix_frobenius/tmp/ceresa_lside.py")
cl = importlib.util.module_from_spec(spec); sys.modules["cl"] = cl
try:
    spec.loader.exec_module(cl)
except SystemExit:
    pass

print("== step-4 signature up the grades: CM channels psi^m / K=Q(sqrt-7) ==")
print(" m  weight  eps    L(1/2)        L'(1/2)      firing            reading")
rows = []
for m in range(1, 7):
    nmax = 1500 + 800 * m
    _, lam = cl.bank_hecke_unitary(m, nmax)
    G = cl.make_G(49, [('C', m / 2.0)])       # weight m+1 => GammaC shift m/2
    e, r, _ = cl.certify(G, lam, 2.5)
    L = cl.central_value(G, lam, e).real
    Ld = None
    fire = "grade<=1"
    reading = "algebraic/decorated"
    if abs(L) < 1e-3:
        Ld = cl.central_deriv(G, lam, e).real
        fire = "grade>=2 (delayed)"
        reading = "HIDDEN cycle fires" if abs(Ld) > 0.05 else "deeper (ord>=2)"
    lds = ("%+.5f" % Ld) if Ld is not None else "    --    "
    rows.append((m, e, L, Ld))
    print(" %d    %d    %+d   %+.4e   %s   %-17s %s" % (m, m + 1, e, L, lds, fire, reading))

print("\n-- pattern --")
signs = "".join(("-" if e < 0 else "+") for (m, e, L, Ld) in rows)
print("  eps(psi^m), m=1..6:  %s" % signs)
print("  hidden-cycle grades (eps=-1, higher cycle fires):  m in %s"
      % [m for (m, e, L, Ld) in rows if e < 0])
print("  decorated/algebraic grades (eps=+1):               m in %s"
      % [m for (m, e, L, Ld) in rows if e > 0])
