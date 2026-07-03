#!/usr/bin/env python3
"""Enumerate & classify rank-3 candidate groups for the Davenport hunt."""
import sys
sys.path.insert(0, '/Users/samuellavery/work/helix_frobenius/tmp')
from sympy import factorint


def is_prime_power(m):
    return len(factorint(m)) == 1


def rank3_groups(max_order):
    """All G = C_{n1} (+) C_{n2} (+) C_{n3}, 1<n1|n2|n3, |G|<=max_order."""
    out = []
    n1 = 2
    while n1**3 <= max_order:
        n2 = n1
        while n1 * n2 * n2 <= max_order:
            if n2 % n1 == 0:
                n3 = n2
                while n1 * n2 * n3 <= max_order:
                    if n3 % n2 == 0:
                        out.append((n1, n2, n3))
                    n3 += n2  # keep n2 | n3
                    # ensure n3 multiple of n2; increment by n2
                    # (loop advances; divisibility maintained)
                    # cap safety
                    if n3 > max_order:
                        break
            n2 += n1
        n1 += 1
    # dedup & sort by order
    out = sorted(set(out), key=lambda t: (t[0]*t[1]*t[2], t))
    return out


def classify(inv):
    n1, n2, n3 = inv
    order = n1 * n2 * n3
    p_group = is_prime_power(order)
    reasons = []
    if p_group:
        reasons.append("p-group(Olson:D=M)")
    if order < 32:
        reasons.append("|G|<32(GAP-exhausted)")
    # C_3 (+) C_3 (+) C_3d  resolved (Bhowmik-Schlage-Puchta)
    if n1 == 3 and n2 == 3 and n3 % 3 == 0:
        reasons.append("C3+C3+C3d(BP resolved)")
    # C_p^2 (+) C_{pq} family type C_p (+) C_p (+) C_{pq}: partially covered by
    # Biswas-Mazumdar sufficient condition (NOT a full resolution) -> do NOT exclude,
    # but flag.
    flags = []
    if n1 == n2 and is_prime_power(n1) and (n3 % n1 == 0):
        p = list(factorint(n1))[0]
        if n1 == p:  # C_p (+) C_p (+) C_{pq}
            flags.append("Cp+Cp+Cpq(BM-partial)")
    # n1=2 with odd cofactor structure: literature claims many resolved; flag
    if n1 == 2:
        flags.append("n1=2(often known)")
    resolved = len(reasons) > 0
    return resolved, reasons, flags, order, p_group


if __name__ == "__main__":
    maxo = int(sys.argv[1]) if len(sys.argv) > 1 else 400
    groups = rank3_groups(maxo)
    print(f"Rank-3 groups with |G| <= {maxo}: {len(groups)} total\n")
    print(f"{'group':22} {'|G|':>5} {'d*':>4} {'M':>4}  status")
    print("-" * 70)
    unresolved = []
    for inv in groups:
        resolved, reasons, flags, order, pg = classify(inv)
        dstar = sum(n-1 for n in inv)
        M = dstar + 1
        name = "C" + "+C".join(str(n) for n in inv)
        status = "RESOLVED: " + ",".join(reasons) if resolved else "OPEN"
        if flags:
            status += "  [" + ",".join(flags) + "]"
        print(f"{name:22} {order:5} {dstar:4} {M:4}  {status}")
        if not resolved:
            unresolved.append((order, inv, flags))
    print()
    print(f"UNRESOLVED candidates: {len(unresolved)}")
    print("Smallest 25 by order:")
    for order, inv, flags in unresolved[:25]:
        name = "C" + "+C".join(str(n) for n in inv)
        fl = ("  [" + ",".join(flags) + "]") if flags else ""
        print(f"  {name:22} |G|={order}{fl}")
