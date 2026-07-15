# Dimension-6 census over COMPOSITE (non-cyclotomic) degree-12 abelian CM fields.
# E = fixed field of H <= (Z/N)* (H = Gal(Q(zeta_N)/E)); [E:Q] = index(H) = 12.
# E is CM iff -1 not in H (totally imaginary).  Embeddings of E = cosets of H.
# CM type Phi = one coset per conjugate pair {gH, -gH}, |Phi|=6.  Balanced (3,3) over an
# imaginary quadratic K = fixed(H_K), H<=H_K index-2, -1 not in H_K.  Primitive Phi <=> E
# simple <=> stabilizer of Phi in (Z/N)*/H is trivial.
# Verdict target: does the dim-4 "simple => never balanced (abelian CM)" obstruction persist
# for composite degree-12 abelian CM fields, or dissolve as it does cyclotomically?
import itertools

def units(N):
    return [a for a in range(1, N) if gcd(a, N) == 1]

def subgroups_of_index(N, idx):
    """all subgroups H <= (Z/N)* of the given index (small N)."""
    U = units(N); G = len(U); order = G // idx
    if G % idx != 0: return []
    Uset = set(U)
    res = []
    # generate subgroups by closure of generator subsets (cheap for small G)
    from itertools import combinations
    elts = U
    seen = set()
    # BFS over subgroups via generating sets of size <=3 (enough for these ranks)
    def gen(gens):
        S = {1}
        changed = True
        while changed:
            changed = False
            new = set()
            for a in S:
                for b in gens:
                    v = (a*b) % N
                    if v not in S: new.add(v)
            if new:
                S |= new; changed = True
        return frozenset(S)
    cand = set()
    for r in range(0, 4):
        for gens in combinations(elts, r):
            H = gen(gens)
            if len(H) == order:
                cand.add(H)
    return [set(H) for H in cand]

def cosets(N, H):
    U = units(N); seen = set(); reps = []
    for g in U:
        if g in seen: continue
        c = frozenset((g*h) % N for h in H)
        reps.append((g, c)); seen |= c
    return reps  # list of (rep, coset-set)

def conj_pairs_cosets(N, H, reps):
    # pair coset of g with coset of -g
    cmap = {}
    for g, c in reps:
        for x in c: cmap[x] = c
    seen = set(); pairs = []
    for g, c in reps:
        if c in seen: continue
        cneg = cmap[(N-g) % N]
        seen.add(c); seen.add(cneg)
        pairs.append((c, cneg))
    return pairs

def is_CM(N, H):
    return (N-1) % N not in H  # -1 not in H

def imag_quad_over(N, H):
    """index-2 subgroups H_K with H <= H_K and -1 not in H_K (imaginary quad subfields)."""
    U = units(N); out = []
    for HK in subgroups_of_index(N, 2):
        if H <= HK and ((N-1) % N) not in HK:
            out.append(HK)
    return out

def signature(Phi_cosets, HK, N):
    # sigma-coset of K = HK (identity coset); count Phi cosets contained in HK vs not
    ins = sum(1 for c in Phi_cosets if next(iter(c)) in HK or (c & HK))
    return (ins, len(Phi_cosets) - ins)

def primitive(N, H, Phi_cosets):
    # stabilizer of Phi (as a set of cosets) under multiplication by g in (Z/N)*
    U = units(N)
    Phiset = set(Phi_cosets)
    cmap = {}
    for c in Phi_cosets:
        for x in c: cmap[x] = c
    # need full coset map
    reps = cosets(N, H); full = {}
    for g, c in reps:
        for x in c: full[x] = c
    for g in U:
        if g % N == 1: continue
        gPhi = set(frozenset((g*x) % N for x in c) for c in Phi_cosets)
        if gPhi == Phiset:
            # g stabilizes; but g in H is trivial. check g not in H
            if g not in H:
                return False
    return True

def census(N):
    out = []
    for H in subgroups_of_index(N, 12):
        if not is_CM(N, H): continue
        reps = cosets(N, H)
        pairs = conj_pairs_cosets(N, H, reps)
        if len(pairs) != 6: continue
        Ks = imag_quad_over(N, H)
        if not Ks: continue
        # enumerate CM types: one coset per conj pair
        cyclo = (len(H) == 1)
        for HK in Ks:
            prim_bal = 0; imp_bal = 0
            for choice in itertools.product(*[(p[0], p[1]) for p in pairs]):
                Phi = list(choice)
                sg = signature(Phi, HK, N)
                if sg == (3, 3):
                    if primitive(N, H, Phi): prim_bal += 1
                    else: imp_bal += 1
            out.append((N, len(H), tuple(sorted(HK)[:4]), prim_bal, imp_bal, cyclo))
    return out

print("SANITY (cyclotomic, H trivial, should match earlier 12-per-K):")
for N in [21, 28, 36]:
    for row in census(N):
        Nn, hlen, hk, pb, ib, cy = row
        print(f"  N={Nn} |H|={hlen} (cyclotomic={cy}) K~{hk}: primitive-balanced(3,3)={pb} imprimitive={ib}")

print()
print("COMPOSITE degree-12 abelian CM fields (H nontrivial, phi(N) in {24,36,48}):")
Ns = [N for N in range(20, 105) if euler_phi(N) in (24, 36, 48)]
any_field = False
for N in Ns:
    rows = [r for r in census(N) if r[1] > 1]  # H nontrivial => genuine subfield
    for Nn, hlen, hk, pb, ib, cy in rows:
        any_field = True
        print(f"  N={Nn} phi={euler_phi(Nn)} |H|={hlen} deg-12 subfield, K~{hk}: "
              f"primitive-balanced(3,3)={pb} imprimitive={ib}")
if not any_field:
    print("  (no degree-12 CM subfield with an imaginary quadratic K found in range)")
print()
print("VERDICT: composite-field primitive-balanced counts > 0 => obstruction dissolves there too.")
