"""EIGENCLOUD: measure the vanishing event as an EXTENDED object, not a root.

Object: the finite Weil/Gabor compression G(s) built from the ZERO side at complex s,
i.e. the same G whose det=0 we have been chasing -- but now we ask for the SHAPE of
||(G - z)^-1|| around the event, and the spectral measure, not just where det vanishes.

Two complementary probes:
 (A) PSEUDOSPECTRUM of the compression: level sets of sigma_min(G(s)) over complex s
     near a zeta zero.  Round contours  => normal/self-adjoint, cloud is a point.
     Elongated/structured => NON-NORMAL, there is shape being discarded.
 (B) NON-NORMALITY measure: ||G G^H - G^H G||_F / ||G||_F^2  (0 iff normal).
"""
import numpy as np, mpmath as mp
mp.mp.dps = 20

# ---- taper + phihat, matching the calibrated bench -------------------------
def rho(x):  return np.clip(x,0,1)**0  # placeholder replaced below
def phihat(r, L, w):
    r = np.asarray(r, dtype=float); out = np.empty_like(r)
    small = np.abs(r) < 1e-12
    out[small] = L - w
    rr = r[~small]
    out[~small] = (2.0/rr)*np.sin(rr*(L-w)/2.0)*np.sin(rr*w/2.0)/(rr*w/2.0)
    return out

def zeros_upto(T):
    g=[]; k=1
    while True:
        z=float(mp.im(mp.zetazero(k)))
        if z> T: break
        g.append(z); k+=1
    return np.array(g)

# ---- the compression at complex s = 1/2 + i*z  (z complex) -----------------
def Gmat(zc, gam, L, w, T, d, h):
    """G_kl = sum_rho phihat(gam - tau_k) phihat(gam - tau_l), with the zero ordinates
    shifted into the complex plane by zc: gam -> gam - (zc - center)."""
    tau = T + np.arange(d)*h
    # complex displacement of the spectral parameter
    g = gam.astype(complex) + zc
    M = np.empty((len(g), d), dtype=complex)
    for k in range(d):
        r = g - tau[k]
        rr = np.where(np.abs(r)<1e-12, 1e-12, r)
        M[:,k] = (2.0/rr)*np.sin(rr*(L-w)/2.0)*np.sin(rr*w/2.0)/(rr*w/2.0)
    return M.T @ M

T=200.0
l=np.log(T/(2*np.pi)); L=l; w=0.05*l/2
h=2*np.pi/L; d=int(T/h)
gam=zeros_upto(2*T+400)
print(f"T={T} l={l:.4f} L={L:.4f} d={d} zeros={len(gam)}")

G0=Gmat(0.0,gam,L,w,T,d,h)
nonnorm=np.linalg.norm(G0@G0.conj().T-G0.conj().T@G0)/np.linalg.norm(G0)**2
print(f"\n(B) NON-NORMALITY  ||[G,G^H]||_F/||G||_F^2 = {nonnorm:.3e}   (0 = normal)")
ev=np.linalg.eigvals(G0)
print(f"    eigenvalues: max|Im|/max|Re| = {np.abs(ev.imag).max()/np.abs(ev.real).max():.3e}")
print(f"    sigma_min={np.linalg.svd(G0,compute_uv=False)[-1]:.4e}  sigma_max={np.linalg.svd(G0,compute_uv=False)[0]:.4e}")

print("\n(A) PSEUDOSPECTRUM: sigma_min(G(s)) on a grid around s-displacement 0")
re=np.linspace(-0.6,0.6,13); im=np.linspace(-0.6,0.6,13)
grid=np.zeros((len(im),len(re)))
for i,y in enumerate(im):
    for j,x in enumerate(re):
        Gz=Gmat(x+1j*y,gam,L,w,T,d,h)
        grid[i,j]=np.linalg.svd(Gz,compute_uv=False)[-1]
np.save('eigencloud_grid.npy',grid)
g0=grid[len(im)//2,len(re)//2]
print("    sigma_min normalised to centre value:")
for i,y in enumerate(im):
    print("   ", f"{y:+.2f}", " ".join(f"{grid[i,j]/g0:7.3f}" for j in range(len(re))))
