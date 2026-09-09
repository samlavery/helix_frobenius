#!/usr/bin/env python3
"""att679 — carrier log-mean vs WARPED-FIBER log-mean (Sam: "carrier log mean or fiber warped log mean?").
   Warped fiber F_Z(s) = Σ_{n<Z} (−1)^{n+1} w(n/Z) n^{−s}, w(u) = exp(1 − 1/(1−u²)) — entire, no pole, no continuation.
   Littlewood's lemma on [½,2]×[0,T] for F_Z:  2π Σ_{atoms∈R}(β−½) = ∫₀ᵀlog|F_Z(½+it)| − ∫₀ᵀlog|F_Z(2+it)| + ∫_{½}^{2}arg F_Z(σ+iT)dσ − ∫_{½}^{2}arg F_Z(σ)dσ.
   PRE-REGISTERED: (a) the pole's −π is GONE (bottom edge = 0 since F_Z(σ) > 0); the identity balances to 0.05 with atoms = the
   displaced events (near ζ zeros) + the alternation atoms (near 1 + 2πik/log 2, each ≈ +π);
   (b) the warped log-mean ∫₀ᵀ log|F_Z(½+it)| differs from the carrier's ∫₀ᵀ log|Z(t)| by < 0.5 (the warp leaves no remainder in the mean)."""
import numpy as np, mpmath as mp
mp.mp.dps = 20
out = open("tmp/att679_results.txt", "w")
def say(*a):
    s = " ".join(str(x) for x in a); print(s); out.write(s + "\n"); out.flush()
def make_fiber(Z):
    n = np.arange(1, int(Z))
    w = np.exp(1 - 1/(1 - (n/Z)**2)); sg = (-1.0)**(n+1); c = sg*w; ln = np.log(n)
    def F(s):   # complex s (python complex)
        return np.sum(c*np.exp(-s*ln))
    def Fmp(s): # for findroot (mp complex)
        return mp.mpc(F(complex(s)))
    return F, Fmp
def cont_arg(F, pts):
    prev = np.angle(F(pts[0])); tot = [prev]
    for p in pts[1:]:
        a = np.angle(F(p))
        while a - prev > np.pi: a -= 2*np.pi
        while a - prev < -np.pi: a += 2*np.pi
        tot.append(a); prev = a
    return np.array(tot)
for T in (100.3, 200.7):
    Z = 4*T; F, Fmp = make_fiber(Z)
    # atoms: Newton from ζ zeros (events) and from 1 + 2πik/log2 (alternation atoms)
    events = []; j = 1
    while True:
        g = float(mp.zetazero(j).imag)
        if g > T + 2: break
        r = mp.findroot(Fmp, mp.mpc(0.5, g)); events.append(complex(r)); j += 1
    alts = []
    k = 1
    while 2*np.pi*k/np.log(2) < T + 2:
        r = mp.findroot(Fmp, mp.mpc(1.0, 2*np.pi*k/np.log(2))); alts.append(complex(r)); k += 1
    inR = [z for z in events + alts if 0.5 < z.real < 2 and 0 < z.imag < T]
    lhs = 2*np.pi*sum(z.real - 0.5 for z in inR)
    ev_in = [z for z in events if 0 < z.imag < T]
    say("T=%.1f Z=%d  events≤T=%d  (right-displaced %d, max|Re δ|=%.1e)  alternation atoms≤T=%d (Re: %.4f..%.4f)"
        % (T, Z, len(ev_in), sum(1 for z in ev_in if z.real > 0.5), max(abs(z.real-0.5) for z in ev_in),
           sum(1 for z in alts if z.imag < T), min(z.real for z in alts if z.imag < T), max(z.real for z in alts if z.imag < T)))
    # carrier integrals
    bps = [0] + sorted(z.imag for z in ev_in) + [T]
    I_line = mp.quad(lambda t: float(np.log(abs(F(complex(0.5, float(t)))))), bps)
    I_two = mp.quad(lambda t: float(np.log(abs(F(complex(2.0, float(t)))))), [0, T/2, T])
    zbps = [0] + [float(mp.zetazero(i).imag) for i in range(1, len(ev_in)+1)] + [T]
    I_carrier = mp.quad(lambda t: mp.log(abs(mp.siegelz(t))), zbps)
    sig = np.linspace(2, 0.5, 3001)
    A_top = -np.trapz(cont_arg(F, [complex(s, T) for s in sig]), sig)   # ∫_{½}^{2} (sig decreasing → minus)
    A_bot = -np.trapz(cont_arg(F, [complex(s, 0.0) for s in sig]), sig)
    J = float(I_line) - float(I_two) + A_top - A_bot
    say("   ∫₀ᵀlog|F_Z(½+it)| = %+.4f   carrier ∫₀ᵀlog|Z| = %+.4f   difference = %+.4f" % (I_line, I_carrier, float(I_line) - float(I_carrier)))
    say("   ∫₀ᵀlog|F_Z(2+it)| = %+.4f   top-edge = %+.4f   bottom-edge = %+.4f" % (I_two, A_top, A_bot))
    say("   Littlewood: RHS J = %+.4f   LHS 2πΣ_atoms(β−½) = %+.4f   (alternation share %+.4f, event share %+.4e)   J − LHS = %+.2e"
        % (J, lhs, 2*np.pi*sum(z.real-0.5 for z in inR if z.real > 0.75), 2*np.pi*sum(z.real-0.5 for z in inR if z.real < 0.75), J - lhs))
