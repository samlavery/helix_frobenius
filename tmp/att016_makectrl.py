"""ATTEMPT 016 -- generate and cache the control point processes.
CUE(4000): exact Haar unitary eigenphases, unfolded to density 1 (the sine-kernel
process with the same rigidity and the same U as the zeta windows, NO arithmetic).
Poisson(4000 on [0,4000]): the no-rigidity control (NULL: K = 1 everywhere, no ramp).
"""
import numpy as np, os, time
HERE = os.path.dirname(os.path.abspath(__file__))
rng = np.random.default_rng(20260812)
N = 4000
cue = []
for r in range(4):
    t0 = time.time()
    Z = (rng.standard_normal((N,N)) + 1j*rng.standard_normal((N,N)))/np.sqrt(2)
    Q,R = np.linalg.qr(Z); Q = Q*(np.diag(R)/np.abs(np.diag(R)))
    ev = np.linalg.eigvals(Q)
    ph = np.sort(np.angle(ev) % (2*np.pi)); x = N*ph/(2*np.pi)
    u = x - x[0]
    cue.append(u); print('cue', r, round(time.time()-t0,1),'s U=',u[-1], flush=True)
np.save(os.path.join(HERE,'att016_ctrl_CUE.npy'), np.array(cue, dtype=object), allow_pickle=True)
poi = []
for r in range(4):
    x = np.sort(rng.random(N)*float(N)); u = x-x[0]; poi.append(u)
np.save(os.path.join(HERE,'att016_ctrl_POI.npy'), np.array(poi, dtype=object), allow_pickle=True)
print('saved')
