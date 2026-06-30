# Carrier Fiber Harness

This directory is a clean finite Python harness for the `pi/3` carrier fiber.

It keeps three layers separate:

- `validate`: the promoted/default c1 cumulative carrier-clock test. This path does not reset by six-cell batches. It uses the continuous clock `exp(-i*(pi/3)*T*log n)`, maps `gamma` to carrier coordinate `T=gamma/(pi/3)`, keeps height scale `1` with `z=exp(gamma)`, and reports focal cancellation through `|B(T)|` plus the harmonic pencil determinant marker. The default `--mode analytic` matches the Lean channels exactly: `A=L(3/2+i gamma)` and `B=(pi/3)*L(1/2+i gamma)`. Use `--mode finite` to test the finite phasor bank with `1,623,346` phasors by default.
- Lean formalizes the crutch-free detector separately from the analytic calibration: `harmonicGram_rank_drop_iff_channel_zero` proves `det Gram = 0 ↔ B = 0` for any supplied harmonic channels `A,B` with `A != 0` and `lambda != mu`, without mentioning an L-function. The L-channel is then one downstream instantiation.
- `native`: no-log helix spin `exp(i n pi/3)`, pitch `1`, cell unit `pi/3`, and exact six-cell focal cancellation for the eta-regulated trivial channel. The readout is `log(z)`, where `z` is height; at pitch `1`, height `z` absorbs `floor(z)` integer slots, split into complete six-cell phasors and a trailing partial block.
- `pencil`: finite harmonic pencil family `[[A, B], [mu*A, lambda*B]]`; the marker is focal cancellation (`A != 0`, `B = 0`), and the command checks `det H = (lambda-mu) A B` plus `det(H* H) = |det H|^2` at each marker.
- `scan`: continuous native focal-height scan for the entire fiber. It advances height, absorbs complete integer slots plus the partial next phasor, and tests the whole-fiber signed channel `B(z)` for focal cancellation using phase `exp(i n pi/3)` and magnitude `((pi/3)n)^-1/2` by default. It also evaluates the harmonic Gram pencil family with unsigned channel `A(z)`, so `detGram=0` detects the same crossing when `A(z) != 0`. `log(z)` is only printed as the height readout coordinate.
- `validate-c1`: explicit alias for `validate`.
- `validate-native`: diagnostic command for the older no-log native replacement attempt.

Run the core requested test:

```bash
python3 carrier_fiber.py validate
python3 carrier_fiber.py native
python3 carrier_fiber.py pencil
```

The default trivial/eta height is `exp(14.134725...) = 1,376,046.570...`; at pitch `1` this absorbs `floor(z) = 1,376,046 = 229,341 * 6` integer slots, so there is no trailing partial block at the first focal marker.

Run the built-in checks:

```bash
python3 carrier_fiber.py test
```

Try another character:

```bash
python3 carrier_fiber.py native --char chi3 --count 600000
python3 carrier_fiber.py native --height 1376046.570
python3 carrier_fiber.py pencil --char eta_trivial --pair 0:1 --pair 1j:2-1j
python3 carrier_fiber.py scan --char eta_trivial --height-max 1376046.570489
python3 carrier_fiber.py validate --char chi4
python3 carrier_fiber.py validate --char chi3 --limit 10
python3 carrier_fiber.py validate --mode finite --limit 10 --count 1623346 --threshold 1e-3
python3 carrier_fiber.py validate-c1 --mode finite --limit 10 --count 1623346 --threshold 1e-3
python3 carrier_fiber.py validate-native --char eta_trivial --max-height 2000000
```

`eta_trivial` is the principal/zeta case with the alternating eta regulator. The raw trivial coefficient has only a positive lane, so it is also available as `trivial`, but it is not the two-lane cancellation channel.
