import math, sys
import numpy as np
sys.path.insert(0, ".")
sys.path.insert(0, "tmp")
from focal_closure import delta_lambda

print("[1] gauge check: F_s(y) = s^(-1/2) e^(-iy ln s) F_1(y) for Delta bank, y=300")
lam = delta_lambda(40000)[1:30001]
n = np.arange(1, 30001, dtype=np.float64)
u = n / 30000
w = np.where(u < 1, np.exp(1 - 1/np.clip(1 - u*u, 1e-300, None)), 0.0)
y = 300.0
for s in (1.0, math.pi/3, math.pi/6, math.pi/2, 2*math.pi/3):
    x = s * n
    F = np.sum(lam * w * x**-0.5 * np.exp(-1j*y*np.log(x)))
    F1 = np.sum(lam * w * n**-0.5 * np.exp(-1j*y*np.log(n)))
    pred = s**-0.5 * np.exp(-1j*y*math.log(s)) * F1
    print(f"    s={s:.4f}: |F_s|={abs(F):.10f}  |pred|={abs(pred):.10f}  |F_s-pred|={abs(F-pred):.2e}")
