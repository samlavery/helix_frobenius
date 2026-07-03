curves = {
  '11a1':[0,-1,1,-10,-20],'15a1':[1,1,1,-10,-10],'14a1':[1,0,1,4,-6],
  '571a1':[0,-1,1,-929,-10595],'681b1':[1,1,0,-1154,-15345],
  '960d1':[0,-1,0,-900,-10098],'960n1':[0,1,0,-20,-42],
  '2340i1':[0,0,0,-2532,-49039],'2849a1':[1,1,1,-53484,-4843180],
}
for lab,ai in curves.items():
    E=EllipticCurve(ai)
    L1=E.lseries().at1(300)[0]     # high number of terms
    # also the BSD-implied L1 = Omega*Sha*prodcp/T^2 for cross-check
    Om=E.period_lattice().omega(); cp=E.tamagawa_product(); T=E.torsion_order(); sha=E.sha().an()
    bsdL1=float(Om)*float(sha)*int(cp)/int(T)**2
    print(f'{lab:8s} L1_at1={float(L1):.10f}  L1_bsd={bsdL1:.10f}')
