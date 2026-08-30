# Off-line quadruple's mass contribution: m(u;b,d) = g(u)/u,
#   g(u) = (u-b)/((u-b)^2+d^2) + (u+b)/((u+b)^2+d^2),  b = beta-1/2 (depth), d = t-gamma.
# Pencil claim: m < 0 possible only when |d| < |b| (inside the depth-disk).
# Pre-registered: find min over u of m for each (b,d); claim holds iff min >= 0 whenever |d| >= |b|.
import numpy as np
viol_outside = 0
rows = []
for b in [0.05, 0.1, 0.2, 0.3, 0.45]:
    for dfac in [0.0, 0.5, 0.9, 0.99, 1.0, 1.01, 1.1, 2.0, 5.0]:
        d = b*dfac
        u = np.linspace(-0.499, 0.499, 4001); u = u[np.abs(u) > 1e-9]
        g = (u-b)/((u-b)**2+d**2) + (u+b)/((u+b)**2+d**2)
        m = g/u
        mn = m.min()
        inside = abs(d) < abs(b)
        if mn < -1e-12 and not inside: viol_outside += 1
        rows.append((b, dfac, mn, inside))
for b, dfac, mn, inside in rows:
    tag = "IN " if inside else "OUT"
    print(f"b={b:.2f} d/b={dfac:>5.2f} [{tag}] min_u m = {mn:>12.5f}")
print("claim violations (m<0 outside depth-disk):", viol_outside)
