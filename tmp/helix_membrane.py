# ATTEMPT #1 -- the winding-membrane constructor (carrier-native cl^-1 probe).
# FIBER: collective W-rail phasors. HELIX: retained phase PATH (partial-sum
# winding), not the endpoint class. READOUT: membrane interior area. Nonzero =>
# carrier retains the interior cohomology throws away. Cross-paired (sixfold)
# vs self-paired (fourfold): does cross-pairing enclose area where self-pairing
# cancels pairwise?
import numpy as np
w = np.exp(2j*np.pi/3)

# fourfold W-rail Pi_W = 49T^4-7T^3+2T^2-T+1 (RATIONAL coeffs => self-paired)
f4 = np.roots([49,-7,2,-1,1])
# sixfold B_{a=1} W-rail f_omega at p=7 (ZETA3 coeffs => cross-paired)
f6 = np.roots([1, -2*w, (-2*w+3), 9, (14*w+35), (98*w+98), 343])

def membrane(roots):
    ph = np.sort(np.angle(roots/np.abs(roots)))     # unit phasors -> phases
    S = np.cumsum(ph)                               # retained winding PATH
    endpoint = ((S[-1]+np.pi) % (2*np.pi)) - np.pi  # endpoint class mod 2pi
    chord = np.linspace(0, S[-1], len(ph))          # trivial (endpoint-only) path
    area = float(np.trapz(S - chord))               # enclosed interior
    return endpoint, area, ph

for name, roots in [("fourfold(self-paired)", f4), ("sixfold(cross-paired)", f6)]:
    e, a, ph = membrane(roots)
    print(f"MEMBRANE {name}: endpoint_winding(mod2pi)={e:+.4f}  "
          f"membrane_area={a:+.5f}  phases={np.round(ph,3).tolist()}", flush=True)

# geometric verdict
_, a4, _ = membrane(f4); _, a6, _ = membrane(f6)
print(f"VERDICT: |area6|/|area4| = {abs(a6)/(abs(a4)+1e-12):.3f}  "
      f"-> {'cross-pairing ENCLOSES interior (constructor has support)' if abs(a6)>10*abs(a4)+1e-6 else 'no separation'}",
      flush=True)
print("MEMBRANE DONE", flush=True)
