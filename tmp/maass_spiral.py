# hunt-spec 2026-07-26, session 18a3f704 — Campaign 3, round-1 harness
# Maass spiral hunt: per-prime Ramanujan scan + proximity telemetry over the
# RIGOROUSLY CERTIFIED Maass forms (LMFDB maass_rigor, Bober et al.).
#   EVENT: certified |a_p| > 2 + tol  (spiral strand signature; would be an
#          RP counterexample candidate -> certification ladder, never a claim
#          from this scan alone).
#   Telemetry: per form: max_p |a_p|, argmax p, near-misses (|a_p| > 1.95),
#   second-moment mean(a_p^2) (Sato-Tate sanity ~ 1).
# Polite client: UA identifies us, 2s pacing, 90s backoff on challenge/non-JSON,
# resumable via labels already present in the output JSONL.
import json, time, urllib.request, os, sys

BASE = "https://www.lmfdb.org/api"
UA = {"User-Agent": "helix-frobenius-research/0.1 (sam@sk-labs.com; falsifier-register scan)"}
OUT = "maass_spiral_round1.jsonl"
TOL = 1e-8
PACE = 2.0

def get_json(url, tries=8):
    delay = 90.0
    for _ in range(tries):
        try:
            req = urllib.request.Request(url, headers=UA)
            with urllib.request.urlopen(req, timeout=60) as r:
                body = r.read().decode()
            if body.lstrip().startswith("{"):
                return json.loads(body)
        except Exception:
            pass
        time.sleep(delay)
        delay = min(delay * 1.7, 900)
    return None

def real_of(v):
    if isinstance(v, dict) and "data" in v:
        return float(str(v["data"])[:30])
    try:
        return float(v)
    except Exception:
        return None

def is_prime(n):
    if n < 2: return False
    i = 2
    while i * i <= n:
        if n % i == 0: return False
        i += 1
    return True

done = set()
if os.path.exists(OUT):
    for line in open(OUT):
        try: done.add(json.loads(line)["label"])
        except Exception: pass

time.sleep(30)  # let any challenge window cool before first hit
forms = []
offset = 0
while True:
    d = get_json(f"{BASE}/maass_rigor/?_format=json&_fields=maass_label,level,spectral_parameter,spectral_error&_limit=100&_offset={offset}")
    if not d or not d.get("data"):
        break
    for r in d["data"]:
        forms.append((r["maass_label"], r.get("level"), real_of(r.get("spectral_parameter"))))
    offset += 100
    print(f"[list] {len(forms)} forms", flush=True)
    time.sleep(PACE)
    if len(d["data"]) < 100:
        break

print(f"form list: {len(forms)}", flush=True)
events = 0
with open(OUT, "a") as fh:
    for label, level, R in forms:
        if label in done:
            continue
        d = get_json(f"{BASE}/maass_rigor_coefficients/?_format=json&maass_label={label}&_fields=n,an&_limit=4000")
        time.sleep(PACE)
        if not d or not d.get("data"):
            fh.write(json.dumps({"label": label, "error": "no-coeffs"}) + "\n")
            continue
        aps = []
        for row in d["data"]:
            n = row.get("n")
            if n is not None and is_prime(int(n)):
                a = real_of(row.get("an"))
                if a is not None:
                    aps.append((int(n), a))
        if not aps:
            fh.write(json.dumps({"label": label, "error": "no-prime-coeffs"}) + "\n")
            continue
        mx_p, mx_a = max(aps, key=lambda t: abs(t[1]))
        near = [[p, a] for p, a in aps if abs(a) > 1.95]
        m2 = sum(a * a for _, a in aps) / len(aps)
        rec = {"label": label, "level": level, "R": R, "n_primes": len(aps),
               "max_abs_ap": abs(mx_a), "argmax_p": mx_p,
               "near_miss_count": len(near), "near": near[:10], "m2": m2}
        if abs(mx_a) > 2.0 + TOL:
            rec["EVENT"] = "ramanujan-exceedance"
            events += 1
            print(f"EVENT {label} p={mx_p} |ap|={abs(mx_a)}", flush=True)
        fh.write(json.dumps(rec) + "\n")
print(f"DONE forms={len(forms)} events={events}", flush=True)
