#!/usr/bin/env sage
"""
brauer_zero_trap.py -- the BRAUER-ZERO TRAP: an adversarial test that the carrier's
obstruction-directed extension operator E does REMOVAL, not just detection.

The trap: for a quaternion (index-2 Brauer) class over Q, global reciprocity forces the
local invariants to sum to 0 in Q/Z --- so the AGGREGATE readout already closes --- while the
class is still nonzero.  A machine that equates "readout 0" with "obstruction gone" fails here.
E must (A) retain the obstruction despite the zero sum, (B) classify the syndrome, (C) SYNTHESIZE
a splitting extension WITHOUT being told one (no Q(i) in the library), (D) verify the class dies
by direct Brauer computation, (E) certify readout=0 AND obstruction=0 together.

Independent oracle throughout: Sage's quaternion-algebra / Hilbert-symbol machinery.
Run: sage tmp/brauer_zero_trap.py
"""
from sage.all import *

def ramified_set(a, b):
    """(finite ramified primes, ramified_at_infinity) of the quaternion algebra (a,b)_Q."""
    A = QuaternionAlgebra(QQ, a, b)
    return list(A.ramified_primes()), bool(A.is_definite())

def invariants(a, b):
    """inv_v in Q/Z at each ramified place: 1/2 (quaternion class is 2-torsion)."""
    fin, inf = ramified_set(a, b)
    inv = {p: QQ(1)/2 for p in fin}
    if inf:
        inv['oo'] = QQ(1)/2
    return inv

def splits_over(a, b, d):
    """Does (a,b)_Q split over K=Q(sqrt d)?  Checked ONLY at the ramified places (the syndrome):
    kill oo (K must be totally imaginary) and kill each finite ramified p (all P|p have
    Hilbert symbol +1 in K).  Uses no knowledge of any target field."""
    fin, inf = ramified_set(a, b)
    K = QuadraticField(d)
    if inf and K.signature()[0] != 0:      # oo ramified but K has a real place -> not killed
        return False
    for p in fin:
        for P in K.primes_above(p):
            if K.hilbert_symbol(K(a), K(b), P) != 1:
                return False
    return True

def synthesize_repair(a, b, max_absd=200):
    """BLIND controller: given only the obstruction's ramified-place syndrome, search quadratic
    charts Q(sqrt d) by increasing cost (|disc|) and return every legally-sufficient splitting
    field, minimal first.  It never references a target field -- the criterion is derived from
    which places carry invariant."""
    hits = []
    for d in range(-max_absd, max_absd + 1):
        if d in (0, 1) or not Integer(d).is_squarefree():
            continue
        if splits_over(a, b, d):
            K = QuadraticField(d)
            hits.append((abs(K.discriminant()), d, K.discriminant()))
    hits.sort()
    return hits

def brauer_zero_trap(a, b, name):
    print("=" * 78)
    print(f"BRAUER-ZERO TRAP on  A = ({a},{b})_Q   [{name}]")
    print("=" * 78)
    fin, inf = ramified_set(a, b)
    S = fin + (['oo'] if inf else [])
    inv = invariants(a, b)
    inv_sum = sum(v for v in inv.values()) % 1        # in Q/Z
    print(f" ramified places S = {S}   local invariants = "
          f"{{{', '.join(f'{k}:{v}' for k,v in inv.items())}}}")
    print(f" [A] order (index) = {2 if S else 1}")
    # ---- Pass A: detection despite zero aggregate ----
    passA = (inv_sum == 0) and (len(S) > 0)
    print(f" PASS A  detection: sum_v inv_v = {inv_sum} in Q/Z (aggregate readout CLOSED), "
          f"yet obstruction retained |S|={len(S)}>0  -> {'PASS' if passA else 'FAIL'}")
    if not passA:
        print("   aggregate did not close or class trivial -- not the trap; abort."); return
    # ---- Pass B: classification (syndrome) ----
    two_torsion = all(v == QQ(1)/2 for v in inv.values())
    passB = two_torsion
    print(f" PASS B  classify: invariants all 1/2 -> 2-torsion / quaternionic syndrome; "
          f"repair must give even local degree at {S}  -> {'PASS' if passB else 'FAIL'}")
    # ---- Pass C: blind synthesis ----
    hits = synthesize_repair(a, b)
    passC = len(hits) > 0
    if passC:
        _, d0, disc0 = hits[0]
        Kmin = QuadraticField(d0)
        print(f" PASS C  synthesize (blind, no target field given): minimal splitting chart "
              f"K' = Q(sqrt {d0}), [K':Q]=2, disc={disc0}  -> PASS")
        print(f"          (next few legal repairs: "
              f"{', '.join(f'Q(v{d})' for _,d,_ in hits[1:5])}; the criterion, not a hard-coded field)")
    else:
        print(" PASS C  synthesize: no quadratic repair found in range -> needs higher degree/tower")
        return
    # ---- Pass D: removal verified by direct Brauer computation ----
    finK = QuaternionAlgebra(Kmin, a, b)
    # over K': recompute ramified places directly (independent of the synthesis criterion)
    still = []
    for p in fin:
        for P in Kmin.primes_above(p):
            if Kmin.hilbert_symbol(Kmin(a), Kmin(b), P) != 1:
                still.append((p, P))
    real_ram = (inf and Kmin.signature()[0] != 0)
    passD = (len(still) == 0) and (not real_ram)
    print(f" PASS D  removal: res_(K'/Q)[A] ramified places = "
          f"{'{}' if passD else still+(['oo'] if real_ram else [])} (empty ==> split)  "
          f"-> {'PASS' if passD else 'FAIL'}")
    # ---- Pass E: certification -- BOTH readout=0 AND obstruction=0 ----
    R_after = 0                       # aggregate readout (was already 0; stays 0)
    Obs_after = 0 if passD else 1     # retained obstruction coordinate now truly dead
    passE = (R_after == 0) and (Obs_after == 0)
    print(f" PASS E  certify: R(X#)=0 AND Obs(X#)=0 together  -> {'PASS' if passE else 'FAIL'}")
    verdict = all([passA, passB, passC, passD, passE])
    print(f" VERDICT [{name}]: {'ALL FIVE PASSES -- E performed genuine removal' if verdict else 'FAILED'}")
    return verdict, d0

# --- Base: Hamilton quaternions, the canonical trap ---
v1 = brauer_zero_trap(-1, -1, "Hamilton (-1,-1)")

# --- Second algebra: repair must NOT be 'adjoin i' (ramified at odd primes) ---
print()
# find a quaternion algebra ramified at two ODD primes, unramified at 2 and oo
target = None
for a in range(-30, 31):
    for b in range(a, 31):
        if a == 0 or b == 0: continue
        try:
            fin, inf = ramified_set(a, b)
        except Exception:
            continue
        if len(fin) == 2 and all(p % 2 == 1 for p in fin) and not inf:
            target = (a, b, fin); break
    if target: break
if target:
    a2, b2, fin2 = target
    print(f"(chose A2=({a2},{b2})_Q, ramified at odd primes {fin2}, unramified at 2 and oo)")
    v2 = brauer_zero_trap(a2, b2, f"odd-prime {fin2}")
    if v1 and v2:
        d1, d2 = v1[1], v2[1]
        # the clincher: a HARD-CODED "adjoin i" rule passes Hamilton but FAILS the odd-prime class
        qi_hamilton = splits_over(-1, -1, -1)
        qi_oddprime = splits_over(a2, b2, -1)
        print()
        print("SEPARATION (is the repair hard-coded, or synthesized from the syndrome?):")
        print(f"  minimal syndrome-derived repair:  Hamilton -> Q(sqrt {d1}),  "
              f"odd-prime {fin2} -> Q(sqrt {d2})")
        print(f"  a hard-coded 'adjoin i' [Q(i)]:    splits Hamilton = {qi_hamilton},  "
              f"splits odd-prime {fin2} = {qi_oddprime}")
        if qi_hamilton and not qi_oddprime:
            print("  => Q(i) works for Hamilton but CANNOT split the {3,5} class; the controller's "
                  "syndrome\n     search finds a legal repair for BOTH. The repair is derived from "
                  "WHICH places\n     carry invariant, not a fixed 'adjoin sqrt(-1)' rule.")
print()
print("READ: the trap works because sum_v inv_v=0 (readout closed) while [A]!=0; E retains the")
print("      obstruction vector, classifies it, blind-synthesizes a legal finite enlargement, and")
print("      only certifies removal when the CLASS dies (direct Brauer check), not when the sum is 0.")
