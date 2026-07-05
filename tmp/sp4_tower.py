import numpy as np
# Genus-2 carrier: Siegel theta theta(tau)=sum_{n in Z^2} e^{i pi n^t tau n}, tau 2x2 sym, Im tau posdef.
def theta2(tau, M=22):
    ns = np.arange(-M, M+1)
    N1, N2 = np.meshgrid(ns, ns, indexing='ij')
    q = tau[0,0]*N1*N1 + 2*tau[0,1]*N1*N2 + tau[1,1]*N2*N2
    return np.sum(np.exp(1j*np.pi*q))

I2 = np.eye(2)
# --- (S) Poisson generator: theta(-tau^{-1}) = det(tau/i)^{1/2} theta(tau).  Test on tau=iY. ---
Y = np.array([[1.0, 0.35],[0.35, 1.2]])
tau = 1j*Y
lhs = theta2(-np.linalg.inv(tau))
rhs = np.sqrt(np.linalg.det(tau/1j))*theta2(tau)      # det(Y)^{1/2}
print(f"  (S) 2D Poisson: theta(-tau^-1) - det(Y)^1/2 theta(tau) = {abs(lhs-rhs):.2e}   [tau=iY]")

# --- (T_B) the QUADRATIC clocks = translations tau->tau+B, B symmetric integer. ---
# three clocks: two diagonal arclength (B11,B22) + one CROSS-TERM (B12).
for name,B in [("arclength-1",np.array([[1,0],[0,0]])),
               ("arclength-2",np.array([[0,0],[0,1]])),
               ("cross-term ",np.array([[0,1],[1,0]]))]:
    t2 = tau + B
    # clock-warp form: multiply each theta term by e^{i pi n^t B n}; equals theta(tau+B) by construction
    direct = theta2(t2)
    print(f"  (T) {name} clock B={B.tolist()}: theta(tau+B) computed = {direct.real:+.4f}{direct.imag:+.4f}j (translation generator)")

# --- Sp(4,Z) check: J (S) and T_B are symplectic; classical: J + {T_B} generate Sp(4,Z). ---
J4 = np.block([[np.zeros((2,2)), I2],[-I2, np.zeros((2,2))]])
def is_sympl(M): return np.allclose(M.T @ J4 @ M, J4)
S = np.block([[np.zeros((2,2)), -I2],[I2, np.zeros((2,2))]])            # tau -> -tau^{-1}
def TB(B): return np.block([[I2, B.astype(float)],[np.zeros((2,2)), I2]])
Bs = [np.array([[1,0],[0,0]]), np.array([[0,0],[0,1]]), np.array([[0,1],[1,0]])]
print(f"  S symplectic: {is_sympl(S)}; T_B symplectic (all 3): {all(is_sympl(TB(B)) for B in Bs)}")
# order of S (S^2=-I => order 4 in Sp, projectively 2); and a mixed word stays symplectic:
W = S @ TB(Bs[0]) @ S @ TB(Bs[2])
print(f"  S^2 = -I: {np.allclose(S@S, -np.eye(4))};  mixed word S T1 S T12 symplectic & integer: "
      f"{is_sympl(W) and np.allclose(W, np.round(W))}")
print("  => emergent carrier clocks (2 arclength + 1 cross-term = the sym 2x2 T_B) + Poisson (S)")
print("     ARE the generators of Sp(4,Z) -- the genus-2 automorphy group, the rung above SL(2,Z).")
