"""
att526 — Sam's condition #6: fixed sign of the vertical second variation for ALL d in (0,1/2).

SETUP.  Guinand-Weil test h = g.g*, g real-entire, g*(z) = conj(g(conj z)).
For real T, conj(g(T-id)) = g(T+id), so the off-line QUARTET {T±id, -T±id}
(spectral coords of rho, rho-bar, 1-rho, 1-rho-bar) contributes

    h(T+id) + h(T-id) = 2 Re[ g(T+id)^2 ].

If g(T) = 0 the on-line reference h(T) vanishes, so Sam's divided difference
    D_h(T,d) = [h(T+id)+h(T-id)-2h(T)] / d^2 = 2 Re[g(T+id)^2] / d^2.

CLAIM (to test).  Take g(z) = (z-T)*phi(z-T) with phi EVEN and REAL-entire.
Then g(T+id) = i*d*phi(id) with phi(id) REAL, so

    Re[g(T+id)^2] = -d^2 * phi(id)^2   EXACTLY,  <= 0 for every real d,

strict wherever phi(id) != 0.  If additionally phi-hat >= 0 then
phi(id) = int phi-hat(x) e^{-dx} dx > 0, so the sign is strict on all of (0,1/2).
No smallness in d  =>  no e^{1/d} prime cutoff; the band limit is phi's alone.

PRE-REGISTERED:
  (i)  identity Re[g(T+id)^2] = -d^2 phi(id)^2 holds to machine precision, phi = Fejer
  (ii) D_h < 0 at every tested d in (0, 1/2), and NOT tending to 0 as d grows
  (iii) CONTROL, phi NOT even (phi = 1 + 4z): the sign FLIPS inside (0,1/2)
        -- predicted flip at d = 1/4, since then g(T+id) = i d - 4 d^2 and
           Re(g^2) = 16 d^4 - d^2 < 0  iff  d < 1/4.
  If (iii) does not flip, evenness is decorative and the construction is not load-bearing.
"""
import mpmath as mp

mp.mp.dps = 30
T = mp.mpf('3.0000000001e12')      # above the verified band, value is irrelevant to the identity
A = mp.mpf('1.7')                  # Fejer scale


def phi_even(z):
    """Fejer kernel (sin(az)/(az))^2 : even, real-entire, phi-hat = triangle >= 0."""
    if z == 0:
        return mp.mpf(1)
    return (mp.sin(A * z) / (A * z)) ** 2


def phi_bad(z):
    """NOT even -- the control."""
    return 1 + 4 * z


def g(z, phi):
    return (z - T) * phi(z - T)


def report(name, phi, predicted=None):
    print("  %s" % name)
    print("     d        Re[g(T+id)^2]        -d^2*phi(id)^2       |diff|        D_h  sign")
    flips = []
    prev = None
    for ds in ('0.01', '0.05', '0.1', '0.2', '0.25', '0.3', '0.4', '0.49'):
        d = mp.mpf(ds)
        val = mp.re(g(T + 1j * d, phi) ** 2)
        pred = -d ** 2 * (phi(1j * d)) ** 2
        pred_re = mp.re(pred)
        Dh = 2 * val / d ** 2
        sg = '-' if val < 0 else '+'
        if prev is not None and sg != prev:
            flips.append(ds)
        prev = sg
        print("    %-6s  %-20s %-20s %-12s %-12s %s"
              % (ds, mp.nstr(val, 10), mp.nstr(pred_re, 10),
                 mp.nstr(abs(val - pred_re), 4), mp.nstr(Dh, 8), sg))
    print("     sign flips in (0,1/2) at d =", flips if flips else "NONE")
    print()


if __name__ == "__main__":
    print("### (i)+(ii)  phi EVEN real-entire (Fejer), a = %s\n" % A)
    report("phi = (sin(az)/(az))^2", phi_even)
    print("### (iii) CONTROL: phi NOT even (phi = 1 + 4z); predicted flip at d = 0.25\n")
    report("phi = 1 + 4z", phi_bad)
