#!/usr/bin/env python3
"""att678 — the carrier log-mean and Littlewood's lemma on [½,2]×[0,T]:
   2π Σ_{ρ∈R}(β−½) = ∫₀ᵀ log|ζ(½+it)|dt − ∫₀ᵀ log|ζ(2+it)|dt + ∫_{½}^{2} arg ζ(σ+iT)dσ − ∫_{½}^{2} arg ζ(σ)dσ.
   In range (RH verified) the LHS is 0.  PRE-REGISTERED: the identity holds to 1e−6 at T ∈ {50.5, 100.3, 200.7, 400.2}
   (a check of the instrument), and |∫₀ᵀ log|Z(t)|dt| ≤ 3 log T there (the carrier log-mean is O(log T)/T)."""
import mpmath as mp
mp.mp.dps = 20
out = open("tmp/att678_results.txt", "w")
def say(*a):
    s = " ".join(str(x) for x in a); print(s); out.write(s + "\n"); out.flush()
def arg_zeta_top(T):     # continuous arg ζ(σ+iT) from σ=2 (principal, ≈0) down to σ=½, then ∫_{½}^{2}
    sig = [2 - 1.5*k/600 for k in range(601)]
    args = []; prev = mp.arg(mp.zeta(2 + 1j*T)); args.append(prev)
    for s in sig[1:]:
        a = mp.arg(mp.zeta(s + 1j*T))
        while a - prev > mp.pi: a -= 2*mp.pi
        while a - prev < -mp.pi: a += 2*mp.pi
        args.append(a); prev = a
    # trapezoid in σ (decreasing): ∫_{½}^{2} = Σ (Δσ)·(a_i + a_{i+1})/2
    h = 1.5/600
    return sum((args[i] + args[i+1])/2*h for i in range(600))
arg0 = mp.quad(lambda s: mp.arg(mp.zeta(s)), [0.5, 2])   # ζ(σ) real negative on (½,1)? arg = π there, 0 for σ>1
for T in (50.5, 100.3, 200.7, 400.2):
    zs = []
    j = 1
    while True:
        g = float(mp.zetazero(j).imag)
        if g > T: break
        zs.append(g); j += 1
    pts = [0] + zs + [T]
    I_line = mp.quad(lambda t: mp.log(abs(mp.siegelz(t))), pts)
    I_two = mp.quad(lambda t: mp.log(abs(mp.zeta(2 + 1j*t))), [0, T/2, T])
    A_top = arg_zeta_top(T)
    J = I_line - I_two + A_top - arg0
    say("T=%6.1f  zeros=%3d  ∫₀ᵀlog|Z|=%+9.4f  ∫₀ᵀlog|ζ(2+it)|=%+8.4f  ∫arg(top)=%+8.4f  ∫arg(bottom)=%+7.4f  Littlewood J=%+.2e ; |∫log|Z||/log T = %.3f"
        % (T, len(zs), I_line, I_two, A_top, arg0, J, abs(I_line)/mp.log(T)))
