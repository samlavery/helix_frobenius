# Independent oracle: Sage's BSD invariants for the calibration + target curves.
curves = {
  '11a1'  : [0,-1,1,-10,-20],
  '15a1'  : [1,1,1,-10,-10],
  '14a1'  : [1,0,1,4,-6],
  '571a1' : [0,-1,1,-929,-10595],
  '681b1' : [1,1,0,-1154,-15345],
  '960d1' : None,
  '960n1' : None,
  '2340i1': [0,0,0,-2532,-49039],
  '2849a1': None,
}
for lab, ai in curves.items():
    try:
        if ai is None:
            E = EllipticCurve(lab.replace('960d1','960d1'))
        else:
            E = EllipticCurve(ai)
        E = E.minimal_model()
        N = E.conductor()
        r = E.rank()
        om = E.period_lattice().omega()   # real period (least real period of the lattice)
        cp = E.tamagawa_product()
        tp = {int(p):int(E.tamagawa_number(p)) for p in N.prime_factors()}
        T  = E.torsion_order()
        L1 = E.lseries().L1_vanishes() if r>0 else E.lseries().at1()[0]
        sha= E.sha().an()
        print(f"{lab:8s} N={N} ai={E.ainvs()} rank={r} Omega={float(om):.10f} "
              f"prodcp={cp} cp={tp} T={T} L1={float(L1):.10f} Sha={float(sha):.6f}")
    except Exception as e:
        print(f"{lab:8s} ERROR {e}")
