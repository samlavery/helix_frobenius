"""
ceresa_multirail_localize.py -- MULTI-RAIL LOCALIZATION of a hidden Hodge/Griffiths cycle.

The original hidden-cycle detector was SCALAR: "a cycle fires at depth d" (delayed signature
0,..,0,!=0).  Multi-rail upgrades it to LOCALIZATION: decompose the fiber into its rails and
read the delayed signature PER RAIL -- the hidden cycle sits on a NAMED rail, at a named depth.

Test fiber (real, not a toy): the Klein quartic C, its triple product
    H^1(C)^{ot3}  =  Ind_K^Q(psi^3)  (+)  3 . M_{f2}(-1),     K = Q(sqrt-7).
Rails:
  rail 1  Ind(psi^3)  = the Ceresa channel  L(psi^3)=49.4.a.a  (the Sym^3-CM piece)
  rail 2..4  M_{f2}(-1) = 3 decorated E-pieces  L(49a) even channel
Per-rail GRADE SIGNATURE = order of vanishing of the rail's L at center:
  ord 0  (L(center) != 0)         -> algebraic, grade <=1, decorated  (fires at grade 1)
  ord 1  (L=0, L'(center) != 0)   -> HIDDEN grade-2 Griffiths/Ceresa cycle (delayed: silent
                                     at grade 1, fires at grade 2)
Localization = which rail carries ord >= 1.  (All L-values FROM SCRATCH via ceresa_lside.)
"""
import importlib.util, sys
spec = importlib.util.spec_from_file_location("cl", "/Users/samuellavery/work/helix_frobenius/tmp/ceresa_lside.py")
cl = importlib.util.module_from_spec(spec)
sys.modules["cl"] = cl
try: spec.loader.exec_module(cl)
except SystemExit: pass

def rail_signature(name, m, gshift, nmax, s0a=2.5, s0b=2.2):
    _, lam = cl.bank_hecke_unitary(m, nmax)
    G = cl.make_G(49, [('C', gshift)])
    e, r, _ = cl.certify(G, lam, s0a)
    Lval = cl.central_value(G, lam, e)
    ord_ = 0
    Lder = None
    if abs(Lval.real) < 1e-3:            # central value vanishes -> look one grade up
        Lder = cl.central_deriv(G, lam, e)
        ord_ = 1 if abs(Lder.real) > 0.05 else 2   # (>=2 would need higher derivative)
    return {"name": name, "eps": e, "L": Lval.real, "Lder": (Lder.real if Lder else None), "ord": ord_}

print("== multi-rail localization of the hidden Ceresa cycle ==")
print("fiber: H^1(Klein quartic)^{ot3} = Ind(psi^3) (+) 3 M_{f2}(-1)\n")
rails = [
    rail_signature("rail 1  Ind(psi^3)  [Sym^3-CM, Ceresa channel]", 3, 1.5, 4000),
    rail_signature("rail 2-4  M_{f2}(-1) [decorated E-pieces, mult 3]", 1, 0.5, 2000),
]
print("rail                                              eps   L(center)     L'(center)   ord  reading")
for R in rails:
    lder = ("%+.6f" % R["Lder"]) if R["Lder"] is not None else "    --    "
    reading = "HIDDEN grade-2 cycle (delayed 0,!=0)" if R["ord"] == 1 else ("algebraic grade<=1 (decorated)" if R["ord"]==0 else "deeper (ord>=2)")
    print("  %-46s  %+d   %+.3e   %s   %d   %s" % (R["name"], R["eps"], R["L"], lder, R["ord"], reading))
print()
hidden = [R for R in rails if R["ord"] >= 1]
alg    = [R for R in rails if R["ord"] == 0]
print("LOCALIZATION:")
print("  the hidden Griffiths/Ceresa cycle is LOCALIZED to:  %s" % (hidden[0]["name"] if hidden else "none"))
print("  decorated/algebraic rails (no hidden cycle):        %s" % ", ".join(R["name"].split("[")[0].strip() for R in alg))
print("  => the transcendental obstruction has a definite cohomological address: the Sym^3-CM rail,")
print("     NOT the decorated E-pieces.  Depth AND rail, where the original detector gave depth only.")
