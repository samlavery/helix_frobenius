import mpmath as mp
mp.mp.dps=30
def ch(s): return [mp.zeta(s, mp.mpf(r)/6) for r in range(1,7)]
print("Conjugate cell pairing  r <-> 6-r  (i.e. r <-> -r mod 6):")
print("  pairs (1,5) (2,4); self-conjugate 3 and 6\n")
for k in (1,2,3,5,10,20):
    g=mp.im(mp.zetazero(k)); s=mp.mpc(0.5,g); v=ch(s)
    p15=abs(v[0]+v[4]); p24=abs(v[1]+v[3]); s3=abs(v[2]); s6=abs(v[5])
    print(f"  zero #{k:2d} g={float(g):8.4f}  |v1+v5|={float(p15):.2e}  |v2+v4|={float(p24):.2e}"
          f"  |v3|={float(s3):.2e}  |v6|={float(s6):.2e}")
print("\nCONTROL, non-zeros on the line:")
for t in (17.0, 27.5, 45.0):
    s=mp.mpc(0.5,t); v=ch(s)
    print(f"  t={t:6.2f}  |v1+v5|={float(abs(v[0]+v[4])):.4f}  |v2+v4|={float(abs(v[1]+v[3])):.4f}"
          f"  |v3|={float(abs(v[2])):.4f}  |v6|={float(abs(v[5])):.4f}")
print("\nCONTROL, off the line at gamma_1:")
g=mp.im(mp.zetazero(1))
for sig in (0.3,0.45,0.55,0.7):
    s=mp.mpc(sig,g); v=ch(s)
    print(f"  sigma={sig}  |v1+v5|={float(abs(v[0]+v[4])):.4f}  |v2+v4|={float(abs(v[1]+v[3])):.4f}"
          f"  |v3|={float(abs(v[2])):.4f}  |v6|={float(abs(v[5])):.4f}")
