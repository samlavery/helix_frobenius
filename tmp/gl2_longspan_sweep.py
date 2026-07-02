"""Long-span GL(2) fiber sweep, chunked into aligned half-open segments.

Segment k of form <form> covers t in [t0 + k*W, t0 + (k+1)*W), half-open, with a
uniform dy grid so concatenation of consecutive segments is a single uniform grid.
Saves |F| (absF) for the segment to tmp/gl2long_<form>_<k>.npy.

Usage: python3 gl2_longspan_sweep.py <delta|e11> <k>
"""
import sys
import numpy as np

FORMS = {
    # form: (lambda_file, N, t0, t_end, dy, W)   -- W = segment width in t-units
    "delta": ("tmp/gl2long_delta_lambda.npy", 1_500_000, 200.0, 1200.0, 0.02, 200.0),
    "e11":   ("tmp/gl2long_e11_lambda.npy",   1_400_000,  80.0,  400.0, 0.01,  80.0),
    "cm32":  ("tmp/gl2long_cm32_lambda.npy",  5_000_000,  50.0,  450.0, 0.01, 100.0),
}


def build_amp(lam, N):
    lamv = lam[1:N + 1].astype(np.float64)
    n = np.arange(1, N + 1, dtype=np.float64)
    u = n / N
    w = np.where(u < 1.0, np.exp(1.0 - 1.0 / np.clip(1.0 - u * u, 1e-300, None)), 0.0)
    amp = lamv * w * n ** (-0.5)
    ln = np.log(n)
    return amp, ln


def main():
    form = sys.argv[1]
    k = int(sys.argv[2])
    lam_file, N, t0, t_end, dy, W = FORMS[form]

    seg_lo = t0 + k * W
    seg_hi = t0 + (k + 1) * W          # half-open upper bound
    if seg_lo >= t_end:
        print(f"segment {k} starts at {seg_lo} >= t_end {t_end}; nothing to do")
        return

    # Sample indices j on the GLOBAL uniform grid tau = t0 + j*dy, keep those in [seg_lo, seg_hi).
    j_lo = int(round((seg_lo - t0) / dy))
    j_hi = int(round((min(seg_hi, t_end) - t0) / dy))   # exclusive; last segment clamps to t_end
    # ensure half-open alignment: the sample at exactly seg_hi belongs to the next segment
    taus = t0 + dy * np.arange(j_lo, j_hi)
    if len(taus) == 0:
        print(f"segment {k}: empty")
        return

    lam = np.load(lam_file)
    amp, ln = build_amp(lam, N)

    start_t = taus[0]
    z = amp * np.exp(-1j * start_t * ln)
    step = np.exp(-1j * dy * ln)
    absF = np.empty(len(taus), dtype=np.float64)
    for i in range(len(taus)):
        absF[i] = abs(z.sum())
        z *= step

    out = f"tmp/gl2long_{form}_{k}.npy"
    np.save(out, absF)
    # also stash the global sample indices so we can assert alignment on collate
    np.save(f"tmp/gl2long_{form}_{k}_idx.npy", np.array([j_lo, j_hi], dtype=np.int64))
    print(f"[{form} seg {k}] t in [{taus[0]:.4f}, {taus[-1]:.4f}], "
          f"{len(taus)} samples (global j {j_lo}..{j_hi-1}), saved {out}")


if __name__ == "__main__":
    main()
