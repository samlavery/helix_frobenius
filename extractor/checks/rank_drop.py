"""THE RANK DROP: what the singular-value profile actually detects.

A_m = sum_j mult_j * d_j^m  is a power sum.  The Hankel matrix built from A_1..A_{2K} has
rank = the number of DISTINCT node locations -- a node of multiplicity 2 contributes
2*d^m, which is still ONE exponential.  So:
    two separate events   -> rank 2
    the two merged        -> rank 1
Rank drop = coincidence.  This is the claim; here it is tested directly on synthetic power
sums where the truth is known.

PRE-REGISTERED: sigma_2/sigma_1 must fall to <=1e-12 as the two nodes merge, and a
multiplicity-2 node must give the SAME profile as a single node.  If sigma_2/sigma_1 stays
O(1) through the merger, the rank does not detect coincidence and the claim is REFUTED.
"""
import sys, math
sys.path.insert(0, 'extractor')
import numpy as np

def hankel_sv(A, K):
    N = 2*K+1; L = K
    a = np.array([A[k] for k in range(N)], dtype=complex)
    Y = np.array([[a[i+j] for j in range(L+1)] for i in range(N-L)], dtype=complex)
    return np.linalg.svd(Y, compute_uv=False)

def powersums(nodes, mults, N):
    return [sum(m*d**k for d, m in zip(nodes, mults)) for k in range(N)]

K = 4
print("=== two nodes merging: d1 = 0.5, d2 = 0.5 + eps ===")
print(f"{'eps':>10}  {'s2/s1':>12}  {'s3/s1':>12}   verdict")
for eps in [1e-1, 1e-2, 1e-3, 1e-4, 1e-6, 1e-8, 1e-10, 1e-12, 0.0]:
    A = powersums([0.5, 0.5+eps], [1, 1], 2*K+1)
    S = hankel_sv(A, K)
    r2, r3 = S[1]/S[0], S[2]/S[0]
    v = "RANK 1 (merged)" if r2 < 1e-12 else "rank >= 2"
    print(f"{eps:>10.0e}  {r2:>12.3e}  {r3:>12.3e}   {v}")

print()
print("=== a genuine DOUBLE node (mult 2) vs a single node ===")
for label, nodes, mults in [("single  d=0.5, mult 1", [0.5], [1]),
                            ("DOUBLE  d=0.5, mult 2", [0.5], [2]),
                            ("two distinct 0.5, 0.3", [0.5, 0.3], [1, 1])]:
    A = powersums(nodes, mults, 2*K+1)
    S = hankel_sv(A, K)
    print(f"  {label:<24} sv/s1 = " + " ".join(f"{v:.2e}" for v in S/S[0]))

print()
print("=== rank counts the number of DISTINCT nodes ===")
for n in range(1, 5):
    nodes = [0.5/(1+j) for j in range(n)]
    A = powersums(nodes, [1]*n, 2*K+1)
    S = hankel_sv(A, K)
    rank = int(np.sum(S > S[0]*1e-12))
    print(f"  {n} distinct node(s) -> numerical rank {rank}   sv/s1 = "
          + " ".join(f"{v:.1e}" for v in S/S[0]))
