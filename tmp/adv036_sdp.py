# AV5: independent SDP for Z(W,S).   Written from BGSTB (4.1)/(4.2)/(7.2) directly.
# NULLS (written before running):
#  P3 null: the discretised SDP at W=0,S=1 does NOT converge to Montgomery-Taylor
#           1.3274993.  Reject if it does (pipeline valid).
#  P4 null: at W=0,S=2 (dip allowed) the optimum does NOT reach ~1.3212.
#           Reject if it does (reproduces the reported CGdL-band value).
#  P5 null: the crossing A* where Z(2A,S=2) = 1.3274993 is NOT near 0.21.
import numpy as np, cvxpy as cp, math

def Z(W, S, N):
    # atoms x_k = k*D, k=0..N, N*D = S.  b_k = masses of even p.d. measure j.
    D = S/N
    x = np.arange(N+1)*D
    s = 1.0/np.cosh(W*x) if W>0 else np.ones(N+1)
    Q = cp.Variable((N+1,N+1), PSD=True)
    b = cp.hstack([cp.sum(cp.diag(Q, k)) for k in range(N+1)])   # Fejer-Riesz: jhat >= 0
    K = int(round(1/D))                       # x_K = 1 exactly when 1/D integral
    assert abs(K*D-1) < 1e-12, "grid must hit alpha=1"
    num = b[0]/D + 2*cp.sum(cp.multiply(x[1:K+1]*s[1:K+1], b[1:K+1]))
    den = b[0] + 2*cp.sum(cp.multiply(s[1:], b[1:]))
    cons = [den == 1]
    if S > 1: cons += [b[K+1:] <= 0]          # the CGdL dip, discarded against F >= 0
    p = cp.Problem(cp.Minimize(num), cons)
    p.solve(solver=cp.CLARABEL)
    return p.value, p.status

print("P3 positive control  W=0, S=1  -> must approach 1.3274992963")
v=[]
for N in [20,40,80]:
    z,st = Z(0,1,N); v.append(z); print(f"   N={N:4d} D={1/N:.3f}  Z={z:.7f}  [{st}]")
print(f"   Richardson(D^2) on last two: {(4*v[-1]-v[-2])/3:.7f}")
print()
print("P4  W=0, S=2 (dip)  -> reported 1.3212")
v2=[]
for N in [40,80]:
    z,st = Z(0,2,N); v2.append(z); print(f"   N={N:4d} D={2/N:.3f}  Z={z:.7f}  [{st}]")
print(f"   Richardson: {(4*v2[-1]-v2[-2])/3:.7f}")
print()
print("P5  strip toll, S=2, W=2A  (Richardson from N=100/200)")
print("     A      W       Z(A)        2-Z(A)")
for A in [0.0,0.05,0.10,0.15,0.20,0.208,0.25,0.30,0.50]:
    W=2*A
    z1,_=Z(W,2,40); z2,_=Z(W,2,80); z=(4*z2-z1)/3
    print(f"   {A:5.3f}  {W:5.3f}  {z:.7f}   {2-z:.7f}"
          + ("   <-- zeta23 Thm D = 1.3274993 / 0.6725007" if abs(z-1.3274993)<0.004 else ""))
