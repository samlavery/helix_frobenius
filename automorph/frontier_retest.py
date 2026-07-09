"""Targeted frontier retest with the fixed (adaptive-scan) inverse-Mellin kernel.
Sym^5 Delta x Sym^b f16 for b=1 (GL2, d=12), 2 (GL3, d=18), 3 (GL4, d=24).
Uses s0 nearer Re=1 to enlarge the reflected piece A(1-s0) (less cancellation)."""
import sys, time
import numpy as np
import sym5_close as S

N = int(sys.argv[1]) if len(sys.argv) > 1 else 6000
t0 = time.time()
tau = S.tau_exact(N)
Delta = S.HolForm("Delta", 12, S.eigenform_coeffs(tau, 12, N), N)
f16 = S.HolForm("f16", 16, S.eigenform_coeffs(tau, 16, N), N)
print(f"[setup] tau+forms N={N}  ({time.time()-t0:.1f}s)", flush=True)

s0_list = [1.06, 1.12, 1.22, 1.4, complex(1.15, 0.45)]
for r_sig, gl in ((1, 2), (2, 3), (3, 4)):
    S.analyze(Delta, 5, ("sym", f16, r_sig), N,
              f"Sym^5(Delta) x Sym^{r_sig}(f16)  [GL({gl}) sigma]",
              note=f"(FRONTIER GL({gl}), d={6*(r_sig+1)})", s0_list=s0_list)
    print("", flush=True)
print(f"[budget] {time.time()-t0:.1f}s")
