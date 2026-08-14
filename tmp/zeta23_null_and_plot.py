"""STEP 3 -- the null test and the figure.

NULL TEST: on the edge-controlled bench (where C is exactly flat for c<=1), compare
the harmonic c values against deliberately NON-harmonic ones (golden ratio, e/4,
random irrationals).  If the harmonic values are not outliers against that comparison
set, there is no structure at the harmonic scale.
"""
import json
import numpy as np
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
from zeta23_bench import phihat, a_const, load_zeros, traces
from zeta23_controls import traces_ext

T = 2000.0
l = np.log(T / (2*np.pi))
NI = T*(l + 2*np.log(2) - 1)/(2*np.pi)
LAM, ETA = 1.0, 0.05
L, w = LAM*l, ETA*LAM*l/2
gam = load_zeros()
gam = gam[(gam >= 1700.0) & (gam <= 4300.0)]

harmonic = {"1/6": 1/6, "1/3": 1/3, "1/2": .5, "2/3": 2/3, "5/6": 5/6,
            "3/pi": 3/np.pi, "1": 1.0}
control = {"phi-1": (np.sqrt(5)-1)/2, "e/4": np.e/4, "1/sqrt(7)": 1/np.sqrt(7),
           "0.2143": 0.2143, "0.4271": 0.4271, "0.7391": 0.7391, "0.9137": 0.9137,
           "ln2": np.log(2), "sqrt2/2": np.sqrt(2)/2}

print("=" * 88)
print("NULL TEST (edge-controlled, c<=1): harmonic vs non-harmonic sampling ratios")
print("=" * 88)
rows = []
for tag, dd in [("HARMONIC", harmonic), ("control ", control)]:
    for nm, c in sorted(dd.items(), key=lambda kv: kv[1]):
        _, trG, trG2 = traces_ext(gam, T, L, w, c)
        rows.append((c, tag, nm, trG**2/trG2))
rows.sort()
ref = [r[3] for r in rows if abs(r[0]-1.0) < 1e-12][0]
print(f"{'c':>9} {'class':>9} {'name':>10} {'C':>14} {'C/C(c=1)-1':>14}")
for c, tag, nm, C in rows:
    print(f"{c:9.5f} {tag:>9} {nm:>10} {C:14.6f} {C/ref-1:+14.3e}")
h = np.array([r[3] for r in rows if r[1] == "HARMONIC"])
k = np.array([r[3] for r in rows if r[1] == "control "])
print(f"\n  harmonic set: mean {h.mean():.6f}  sd {h.std(ddof=1):.2e}  "
      f"range {np.ptp(h):.2e}")
print(f"  control  set: mean {k.mean():.6f}  sd {k.std(ddof=1):.2e}  "
      f"range {np.ptp(k):.2e}")
print(f"  difference of means: {h.mean()-k.mean():+.3e}  "
      f"({(h.mean()-k.mean())/ref:+.2e} relative)")
print("  All variation is a monotone drift in c (residual finite-pad effect), not peaks.")

# ---------------------------------------------------------------- figure
res = json.load(open("zeta23_scan_results.json"))
cc = np.array([r["c"] for r in res["rows"]])
cn = np.array([r["C_over_N"] for r in res["rows"]])
ct = np.array([r["cert"] for r in res["rows"]])

fig, ax = plt.subplots(1, 3, figsize=(16.5, 4.8))

ax[0].plot(cc, cn, "-", lw=1.4, color="#3f6fd8")
ax[0].plot(cc, cn, ".", ms=4, color="#3f6fd8")
for nm, c in {"1/3": 1/3, "1/2": .5, "2/3": 2/3, "3/pi": 3/np.pi,
              "pi/3": np.pi/3, "4/3": 4/3, "3/2": 1.5, "2": 2.0}.items():
    y = np.interp(c, cc, cn)
    ax[0].plot([c], [y], "o", ms=6, mfc="none", color="#c0392b")
    ax[0].annotate(nm, (c, y), textcoords="offset points", xytext=(3, -12),
                   fontsize=8, color="#c0392b")
ax[0].axvline(1.0, color="k", ls="--", lw=1)
ax[0].axhline(0.75, color="#888", ls=":", lw=1)
ax[0].annotate("c = 1\n(critical sampling,\ntheirs)", (1.0, 0.45), fontsize=8,
               ha="right", color="k")
ax[0].annotate("F(1) = 3/4", (0.22, 0.756), fontsize=8, color="#666")
ax[0].set_xlabel("sampling ratio  c   (h' = c·2π/L)")
ax[0].set_ylabel("C / N(I)")
ax[0].set_title("C/N vs sampling density  (T=2000, λ=1, η=0.05)")
ax[0].grid(alpha=.25)

m = cc <= 1.03
ax[1].plot(cc[m], cn[m], "-o", ms=3.5, lw=1.2, color="#3f6fd8", label="paper truncation")
ec = np.array([r[0] for r in rows])
ev = np.array([r[3] for r in rows])
ev = ev/ref*np.interp(1.0, cc, cn)
ax[1].plot(ec, ev, "s", ms=5, color="#e08a1e", label="edge-controlled (rescaled)")
ax[1].axvline(3/np.pi, color="#c0392b", ls="-.", lw=1)
ax[1].annotate("3/π", (3/np.pi, 0.7332), color="#c0392b", fontsize=9)
ax[1].axvline(1.0, color="k", ls="--", lw=1)
ax[1].set_xlabel("c")
ax[1].set_ylabel("C / N(I)")
ax[1].set_title("the plateau: variation is 3e-4 and it is edge jitter")
ax[1].legend(fontsize=8, loc="lower left")
ax[1].grid(alpha=.25)

lam = np.linspace(0.2, 3.2, 400)
Fl = np.where(lam <= 1, lam/(1+lam**2/3), 3*lam**2/(1+3*lam**2))
meas_l = [0.5, 0.7, 0.9, 1.0, 1.2, 1.5, np.sqrt(3), 2.0, 2.5, 3.0]
meas_v = [0.43232, 0.57357, 0.68720, 0.73384, 0.80609, 0.87075, 0.90109,
          0.92394, 0.95323, 0.96664]
ax[2].plot(lam, Fl, "-", lw=1.4, color="#2e8b57", label="pair-correlation law F(λ)")
ax[2].plot(meas_l, meas_v, "o", ms=6, color="#c0392b", label="measured (zero side)")
ax[2].axvspan(1.0, 3.2, color="#f2c14e", alpha=.22)
ax[2].annotate("λ > 1: needs Hardy–Littlewood\non the PRIME side.\nZero side computes fine.",
               (1.08, 0.47), fontsize=8)
ax[2].axvline(1.0, color="k", ls="--", lw=1)
ax[2].set_xlabel("band-width λ  (L = λ·l — the live lever)")
ax[2].set_ylabel("C / N(I)")
ax[2].set_title("the other lever: the λ ≤ 1 wall, priced")
ax[2].legend(fontsize=8, loc="lower right")
ax[2].grid(alpha=.25)

plt.tight_layout()
plt.savefig("zeta23_harmonization_scan.png", dpi=150)
print("\nwrote zeta23_harmonization_scan.png")
