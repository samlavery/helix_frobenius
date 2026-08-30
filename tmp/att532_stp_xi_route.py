"""att532 -- INDEPENDENT Xi-route evaluation of the second tail primitive S_x(r).

Route A (att531, existing): tensor quadrature of
    W_x(u) = 2 int Phi(u+w)Phi(u-w) cos(2xw) dw ,  S_x(r) = int_r^inf (u-r) W_x(u) du
over the Phi-plane.  Cancellation-limited: at x=60 the answer sits ~37 orders below
the integrand scale.

Route B (THIS FILE): closed form in Xi alone.  Derivation, all steps reversible:

  int h(u) W_x(u) du = iint h((a+b)/2) Phi(a)Phi(b) cos(x(a-b)) da db      [a=u+w,b=u-w]
  S_x(r) = int_0^inf (u-r)_+ W_x du = (1/2) int_R (|u|-r)_+ W_x du
         = (1/4) int rho_x(v) (|v|-2r)_+ dv ,   rho_x(v)=iint ... delta(a+b-v)
  rho_x^(tau) = G(x+tau) G(x-tau) =: g_x(tau)          [G = FT of Phi, real even]

  (|v|-c)_+ = |v| - c + (c-|v|)_+          -- both pieces have honest transforms
     |v|      = (2/pi) int_0^inf (1-cos(v tau)) tau^{-2} dtau
     FT[(c-|v|)_+] = 2(1-cos(c xi))/xi^2   -- L^1, no regularisation
  => int rho_x h_c = (2/pi) int_0^inf [G(x)^2 - g_x(tau) cos(c tau)] tau^{-2} dtau - c G(x)^2
  and with int_0^inf (1-cos(2 r tau)) tau^{-2} dtau = pi r the two linear terms cancel:

  ***  S_x(r) = (1/2pi) int_0^inf [G(x)^2 - G(x+tau)G(x-tau)] cos(2 r tau) tau^{-2} dtau  ***

  i.e.  S_x(r) = (1/4pi) * Dhat_x(2r)  with the WIGNER-NEWMAN DEFECT DENSITY
        D_x(tau) = [G(x)^2 - G(x+tau)G(x-tau)] / tau^2   (even, L^1).
  So global STP  <=>  D_x is a POSITIVE-DEFINITE function, for every x.
  Consistency check: S_x'(0) = -G(x)^2/2 = -int_0^inf W_x.

  ------------------------------------------------------------------------------
  REJECTED FORM -- DO NOT USE FOR r > 0  (recorded so it is not re-derived):

     (A0)   S_x(r) =? (1/2pi) int_0^inf [G(x)^2 - G(x+t)G(x-t) cos(2rt)] t^{-2} dt

  This is the "cosine inside the bracket" version WITHOUT the linear term.  It is
  WRONG for r > 0: it comes from applying a bare Hadamard finite part to the
  distributional transform FT[(|v|-c)_+] = -2cos(c xi)/xi^2 while assuming
  f.p. int_R xi^{-2} dxi = 0, which drops a term -c G(x)^2.  The correct
  "cosine inside" version is

     (A1)   S_x(r) = (1/2pi) int_0^inf [G(x)^2 - G(x+t)G(x-t) cos(2rt)] t^{-2} dt
                     - (r/2) G(x)^2 ,

  and (A1) == (B) identically, because int_0^inf (1-cos(2rt)) t^{-2} dt = pi r makes
  the two linear terms cancel.  THIS FILE IMPLEMENTS (B).

  EVIDENCE.  (A0) was implemented first and cross-checked against the independent
  direct-Phi-plane quadrature of tmp/att531_stp.py: at x=2 it missed by a factor 39
  at r=0.25 and by 2.2e4 at r=0.5.  Re-implemented as (B) it agrees with the same
  att531 checkpoints to 1.6e-4 and 7.0e-6 relative (att531 prints only 4 significant
  figures, so that is checkpoint-limited agreement, not method error).

  SCOPE OF THE CORRECTION.  At r = 0 all three forms coincide, since cos(0) = 1 and
  the linear term carries a factor r.  The r = 0 counterexample S_60(0) < 0 is
  therefore UNAFFECTED by this correction and stands on its own.
  ------------------------------------------------------------------------------

NORMALISATION.  Riemann: Xi(x) = xi(1/2+ix) = int_R Phi_R(u) e^{ixu} du with
Phi_R(u) = 2*P0(|u|).  att530/att531 use Ph = P0 (= 1/4 of Lean riemannXiKernel).
So G = Xi/2 in the Python convention and

  S^{Py}_x(r) = (1/(8 pi)) int_0^inf [Xi(x)^2 - Xi(x+tau)Xi(x-tau)] cos(2 r tau) tau^{-2} dtau

DC/AC SPLIT (harmonic discipline).  Own scale = Xi(x)^2 (2e-36 at x=60), never 1.
DC = Xi(x)^2/tau^2, integrated EXACTLY: int_T^inf = Xi(x)^2/T, and near 0 the DC is
cancelled by the AC to order tau^2.  AC = Xi(x+tau)Xi(x-tau)cos(2 r tau)/tau^2, which
decays like e^{-pi tau/2} past tau = x.  Only the AC is quadratured.

USAGE:  python3 att532_stp_xi_route.py [validate|scan|point x r]
"""
import sys
import mpmath as mp


def xi(s):
    """Completed zeta xi(s) = (1/2) s(s-1) pi^{-s/2} Gamma(s/2) zeta(s)."""
    return mp.mpf(1) / 2 * s * (s - 1) * mp.pi ** (-s / 2) * mp.gamma(s / 2) * mp.zeta(s)


def Xi(v):
    """Xi(v) = xi(1/2 + i v), real for real v."""
    return mp.re(xi(mp.mpf(1) / 2 + 1j * mp.mpf(v)))


# ---------------------------------------------------------------- Gauss-Legendre
_GL_CACHE = {}


def gl_nodes(n):
    key = (n, mp.mp.dps)
    if key not in _GL_CACHE:
        # mpmath's Gauss-Legendre degree-m rule has 3*2^m nodes on [-1,1]
        _GL_CACHE[key] = mp.calculus.quadrature.GaussLegendre(mp.mp).get_nodes(
            mp.mpf(-1), mp.mpf(1), n, mp.mp.prec)
    return _GL_CACHE[key]


def panel_int(f, a, b, deg=5):
    nodes = gl_nodes(deg)
    a, b = mp.mpf(a), mp.mpf(b)
    half, mid = (b - a) / 2, (a + b) / 2
    return half * mp.fsum(w * f(mid + half * t) for t, w in nodes)


# ---------------------------------------------------------------- the integral
def S_xi(x, r, T=150, deg=5, panel=mp.mpf('0.5'), xi_cache=None):
    """S^{Py}_x(r) via the Xi route.  Returns (value, diagnostics dict)."""
    x = mp.mpf(x)
    r = mp.mpf(r)
    T = mp.mpf(T)
    if xi_cache is None:
        xi_cache = {}

    def XX(v):
        k = mp.nstr(v, 30)
        if k not in xi_cache:
            xi_cache[k] = Xi(v)
        return xi_cache[k]

    Xx2 = XX(x) ** 2

    def integrand(tau):
        if tau == 0:
            return mp.mpf(0)
        return (Xx2 - XX(x + tau) * XX(x - tau)) * mp.cos(2 * r * tau) / tau ** 2

    # geometric panels near 0 (integrand is smooth & even there; the tau^2
    # cancellation is exact to O(tau^2) so no special handling is needed beyond dps)
    edges = [mp.mpf(0)]
    e = mp.mpf('1e-8')
    while e < panel:
        edges.append(e)
        e *= 10
    e = panel
    while e < T:
        edges.append(e)
        e += panel
    edges.append(mp.mpf(T))

    total = mp.mpf(0)
    for i in range(len(edges) - 1):
        total += panel_int(integrand, edges[i], edges[i + 1], deg)

    # DC tail, EXACT: int_T^inf cos(a tau)/tau^2 dtau = cos(aT)/T - a(pi/2 - Si(aT))
    a = 2 * r
    if a == 0:
        tail_dc = Xx2 / mp.mpf(T)
    else:
        tail_dc = Xx2 * (mp.cos(a * T) / T - a * (mp.pi / 2 - mp.si(a * T)))
    tail_ac = XX(x + T) * XX(x - T) / T  # crude bound on the neglected AC tail
    val = (total + tail_dc) / (8 * mp.pi)
    return val, {'quad': total, 'tail_dc': tail_dc, 'tail_ac_bound': tail_ac,
                 'Xi_x': XX(x), 'Xi_x_sq': Xx2}


# ---------------------------------------------------------------- entry points
def cmd_validate():
    """Cross-check route B against att531's double-precision route A at small x."""
    mp.mp.dps = 30
    ref = {  # from tmp/att531_stp.py, double precision, r = 0
        0.0: 0.003764, 2.0: 0.003160, 5.0: 0.001243, 9.0: 9.085e-05,
        14.0: 2.876e-07, 20.0: 1.595e-10,
    }
    print('# route B (Xi) vs route A (Phi tensor quadrature, att531), r = 0')
    print('#   x        route B                route A (dbl)      rel.diff')
    for x, a in sorted(ref.items()):
        v, d = S_xi(x, 0, T=120)
        print('  %5.1f   %-22s %-18.6g %.3g' % (x, mp.nstr(v, 12), a,
                                                abs(float(v) - a) / abs(a)))
    print('\n# r-dependence cross-check at x = 2 (route A: 1.636e-4, 5.887e-7 at r=.25,.5)')
    for r, a in ((0.25, 1.636e-4), (0.5, 5.887e-7)):
        v, _ = S_xi(2.0, r, T=120)
        print('   r=%.2f  route B = %-22s route A = %-12.6g rel=%.3g'
              % (r, mp.nstr(v, 12), a, abs(float(v) - a) / abs(a)))


def cmd_point(x, r, dps, T, deg, panel):
    mp.mp.dps = dps
    v, d = S_xi(x, r, T=T, deg=deg, panel=mp.mpf(panel))
    print('x=%s r=%s dps=%d T=%s deg=%d panel=%s' % (x, r, dps, T, deg, panel))
    print('  Xi(x)          = %s' % mp.nstr(d['Xi_x'], 20))
    print('  Xi(x)^2        = %s' % mp.nstr(d['Xi_x_sq'], 20))
    print('  quad[0,T]      = %s' % mp.nstr(d['quad'], 20))
    print('  DC tail  (exact)= %s' % mp.nstr(d['tail_dc'], 20))
    print('  AC tail  (bound)= %s' % mp.nstr(d['tail_ac_bound'], 10))
    print('  S_x(r)         = %s' % mp.nstr(v, 20))


def cmd_scan(dps, T, deg, panel, lo, hi, step):
    mp.mp.dps = dps
    print('# S_x(0) sign scan, Xi route, dps=%d T=%s deg=%d panel=%s' % (dps, T, deg, panel))
    print('#   x        Xi(x)                 S_x(0)                sign')
    x = mp.mpf(lo)
    while x <= mp.mpf(hi) + mp.mpf('1e-12'):
        v, d = S_xi(x, 0, T=T, deg=deg, panel=mp.mpf(panel))
        print('  %7s  %-21s %-21s %s'
              % (mp.nstr(x, 6), mp.nstr(d['Xi_x'], 10), mp.nstr(v, 12),
                 'NEG <<<' if v < 0 else '+'))
        sys.stdout.flush()
        x += mp.mpf(step)


if __name__ == '__main__':
    a = sys.argv[1:]
    if not a or a[0] == 'validate':
        cmd_validate()
    elif a[0] == 'point':
        cmd_point(a[1], a[2], int(a[3]) if len(a) > 3 else 50,
                  a[4] if len(a) > 4 else 150, int(a[5]) if len(a) > 5 else 5,
                  a[6] if len(a) > 6 else '0.5')
    elif a[0] == 'scan':
        cmd_scan(int(a[1]), a[2], int(a[3]), a[4], a[5], a[6], a[7])
