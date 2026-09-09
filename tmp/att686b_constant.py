import mpmath as mp
mp.mp.dps = 20
I = mp.quad(lambda s: mp.log(abs(mp.zeta(s))), [0.5, 0.75, 1, 1.5, 2, 4, 8, 40])
print("(1/π)∫_{½}^{∞} log|ζ(σ)|dσ = %+.6f ;  minus that = %+.6f ; target constant S₁−R = -0.81735" % (I/mp.pi, -I/mp.pi))
# candidates with corner/pole terms
for name, val in (("−I/π", -I/mp.pi), ("−I/π − 1/2", -I/mp.pi - 0.5), ("−I/π + 1/2", -I/mp.pi + 0.5), ("−I/π − 1/4", -I/mp.pi - 0.25), ("−I/π − 1/8", -I/mp.pi - 0.125), ("−I/π − 1/(2π)", -I/mp.pi - 1/(2*mp.pi)), ("−I/π − 7/8", -I/mp.pi - 0.875)):
    print("  %-14s = %+.6f   diff from target %+.6f" % (name, val, val + 0.81735))
