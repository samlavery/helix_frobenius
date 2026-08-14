# AV6: THE BAND/DENSITY TRADE-OFF -- closed form, no SDP.
# The excised sum needs density exponent c > 2*lambda (lambda = normalised band =
# exponential type of the Tsang kernel).  Selberg/Simonic give c = 1/4 => lambda < 1/8.
# NULL (written before running): at the largest band the available density theorem
# permits, the Montgomery functional still certifies > 0.6725007 simple zeros.
import mpmath as mp
mp.mp.dps = 20
def invc(lam):                       # zeta23 (7.4): c*_lambda = sqrt2 tan(th)/(1+th tan th)
    th = lam/mp.sqrt(2)
    return (1 + th*mp.tan(th))/(mp.sqrt(2)*mp.tan(th))
print("band lam   type S=lam   c needed (>2S)   Z=1/c*_lam    2-Z = certified proportion")
for lam in ['1','0.5','0.25','0.125','0.1','0.05']:
    l = mp.mpf(lam); Z = invc(l)
    print(f"  {lam:<8}  {float(l):.4f}       c > {float(2*l):.3f}"
          f"        {mp.nstr(Z,8):>10}   {mp.nstr(2-Z,8):>10}")
print()
print("Selberg/Simonic c = 1/4  =>  largest admissible band lambda = 1/8:")
Z8 = invc(mp.mpf(1)/8)
print("   Z =", mp.nstr(Z8,10), "   2-Z =", mp.nstr(2-Z8,10), "  (a NEGATIVE proportion)")
print("   target 0.6725007 needs lambda = 1 exactly (Montgomery-Taylor), i.e. c > 2.")
print()
print("Break-even band: 2 - 1/c*_lam = 0.6725007  at lam =",
      mp.nstr(mp.findroot(lambda l: 2-invc(l)-mp.mpf('0.6725007'), 0.9),8))
print("Positive proportion at all requires 2 - 1/c*_lam > 0 at lam =",
      mp.nstr(mp.findroot(lambda l: 2-invc(l), 0.5),8), "-> needs c > ",
      mp.nstr(2*mp.findroot(lambda l: 2-invc(l), 0.5),6))
