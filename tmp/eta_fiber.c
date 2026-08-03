/* eta_fiber.c — the eta fiber on a harmonized carrier, built phasor by phasor.
 *
 * Head height Z = e^y.  The bank holds one phasor per carrier site n <= Z:
 *
 *   carrier position   x_n = (pi/3) * n            (harmonized carrier)
 *   magnitude          w(n/Z) * x_n^{-1/2}         (growth window, w(0)=1, w(1)=0)
 *   phase              -y * log(x_n)               (head-coupled readout: every
 *                                                   phasor spins as the head
 *                                                   climbs, at rate log x_n)
 *   lane               n odd -> u=+1, n even -> u=-1   (the eta conductor)
 *
 *   R_odd = sum over odd sites, R_even = sum over even sites,
 *   F     = R_odd - R_even,
 *   c(Z)  = |F| / max(|R_odd|,|R_even|)            (projective closure measure)
 *
 * A focal closure — c(Z) collapsing while both lanes stay large — is a zero.
 * Nothing here knows about zeta: no L-function, no functional equation, no
 * continuation, no reference ordinate.  Only the fiber's construction laws.
 *
 * Every site is summed exactly, one libm log/sincos/exp per phasor.  No
 * approximation anywhere in the bank.  Accumulation is double-double: the
 * bank's L1 mass is 2*sqrt(Z) (2.8e7 at Z=2e14) while the resultant is O(10),
 * so ~7 digits cancel and plain double accumulation would floor the closure.
 *
 * Refinement is a complex secant on F (F is analytic in y and vanishes at the
 * event), not a minimisation of |F| — 3 or 4 evaluations instead of ~120.
 *
 * Build:  cc -O3 -ffp-contract=fast -mcpu=native -pthread -o eta_fiber eta_fiber.c -lm
 * Usage:  ./eta_fiber value  <y>
 *         ./eta_fiber scan   <y0> <y1> <per_unit>
 *         ./eta_fiber locate <y0> <y1> <per_unit>
 *         ./eta_fiber refine <y_a> <y_b>       (secant from a bracket)
 */

#include <math.h>
#include <pthread.h>
#include <stdatomic.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define PI3 (M_PI / 3.0)

/* ------------------------------------------------------------------ */
/* double-double accumulator                                           */
/* ------------------------------------------------------------------ */

typedef struct {
  double hi, lo;
} dd;

static inline dd dd_add(dd a, double b) {
  double s = a.hi + b;
  double bb = s - a.hi;
  double err = (a.hi - (s - bb)) + (b - bb);
  double lo = a.lo + err;
  double s2 = s + lo;
  return (dd){s2, lo - (s2 - s)};
}

static inline dd dd_sum(dd a, dd b) {
  dd r = dd_add(a, b.hi);
  return dd_add(r, b.lo);
}

static inline double dd_val(dd a) { return a.hi + a.lo; }

typedef struct {
  dd re, im;
} ddc;

static const ddc DDC_ZERO = {{0, 0}, {0, 0}};

/* growth window: C-infinity, w(0)=1, flat to all orders at u=1 */
static inline double window(double u) {
  double d = 1.0 - u * u;
  if (d <= 0.0) return 0.0;
  return exp(1.0 - 1.0 / d);
}

/* ------------------------------------------------------------------ */
/* the bank, summed site by site                                       */
/* ------------------------------------------------------------------ */

static void bank_range(long long lo, long long hi, double y, double Z, ddc *Rodd,
                       ddc *Reven) {
  const int BLK = 1024;
  double bo_re = 0, bo_im = 0, be_re = 0, be_im = 0;
  int cnt = 0;
  for (long long n = lo; n < hi; n++) {
    double dn = (double)n;
    double w = window(dn / Z);
    if (w == 0.0) continue;
    double x = PI3 * dn;
    double a = w / sqrt(x);
    double ph = -y * log(x);
    double c = cos(ph), s = sin(ph);
    if (n & 1) {
      bo_re += a * c;
      bo_im += a * s;
    } else {
      be_re += a * c;
      be_im += a * s;
    }
    if (++cnt == BLK) {
      Rodd->re = dd_add(Rodd->re, bo_re);
      Rodd->im = dd_add(Rodd->im, bo_im);
      Reven->re = dd_add(Reven->re, be_re);
      Reven->im = dd_add(Reven->im, be_im);
      bo_re = bo_im = be_re = be_im = 0;
      cnt = 0;
    }
  }
  Rodd->re = dd_add(Rodd->re, bo_re);
  Rodd->im = dd_add(Rodd->im, bo_im);
  Reven->re = dd_add(Reven->re, be_re);
  Reven->im = dd_add(Reven->im, be_im);
}

typedef struct {
  double y, Z;
  long long N;
  long long nchunk;
  _Atomic long long next;
  pthread_mutex_t mu;
  ddc Rodd, Reven;
} job_t;

static void *worker(void *arg) {
  job_t *J = (job_t *)arg;
  ddc lo_ = DDC_ZERO, le_ = DDC_ZERO;
  for (;;) {
    long long k = atomic_fetch_add(&J->next, 1);
    if (k >= J->nchunk) break;
    long long a = 1 + (long long)((__int128)J->N * k / J->nchunk);
    long long b = 1 + (long long)((__int128)J->N * (k + 1) / J->nchunk);
    if (b > J->N + 1) b = J->N + 1;
    if (a >= b) continue;
    bank_range(a, b, J->y, J->Z, &lo_, &le_);
  }
  pthread_mutex_lock(&J->mu);
  J->Rodd.re = dd_sum(J->Rodd.re, lo_.re);
  J->Rodd.im = dd_sum(J->Rodd.im, lo_.im);
  J->Reven.re = dd_sum(J->Reven.re, le_.re);
  J->Reven.im = dd_sum(J->Reven.im, le_.im);
  pthread_mutex_unlock(&J->mu);
  return NULL;
}

static int NTHREADS = 8;

typedef struct {
  double ore, oim, ere, eim;
  double fre, fim;
  double closure;
  long long N;
} bank_t;

static bank_t bank(double y) {
  job_t J;
  memset(&J, 0, sizeof J);
  J.y = y;
  J.Z = exp(y);
  J.N = (long long)J.Z;
  J.Rodd = DDC_ZERO;
  J.Reven = DDC_ZERO;
  atomic_init(&J.next, 0);
  pthread_mutex_init(&J.mu, NULL);
  long long per = 1 << 22;
  J.nchunk = J.N / per + 1;
  if (J.nchunk < (long long)NTHREADS * 4) J.nchunk = (long long)NTHREADS * 4;
  if (J.nchunk > (1 << 22)) J.nchunk = 1 << 22;

  pthread_t th[64];
  for (int i = 0; i < NTHREADS; i++) pthread_create(&th[i], NULL, worker, &J);
  for (int i = 0; i < NTHREADS; i++) pthread_join(th[i], NULL);

  bank_t B;
  B.ore = dd_val(J.Rodd.re);
  B.oim = dd_val(J.Rodd.im);
  B.ere = dd_val(J.Reven.re);
  B.eim = dd_val(J.Reven.im);
  B.N = J.N;
  B.fre = B.ore - B.ere;
  B.fim = B.oim - B.eim;
  double mo = hypot(B.ore, B.oim), me = hypot(B.ere, B.eim);
  double mx = mo > me ? mo : me;
  B.closure = mx > 0 ? hypot(B.fre, B.fim) / mx : 1.0;
  return B;
}

static void report(double y, bank_t B, const char *tag) {
  printf("%s y=%.15f  Z=%.6e  N=%lld\n", tag, y, exp(y), B.N);
  printf("   R_odd  % .17e  % .17e   |R|=%.10e\n", B.ore, B.oim, hypot(B.ore, B.oim));
  printf("   R_even % .17e  % .17e   |R|=%.10e\n", B.ere, B.eim, hypot(B.ere, B.eim));
  printf("   F      % .17e  % .17e\n", B.fre, B.fim);
  printf("   c(Z)   %.6e\n", B.closure);
  fflush(stdout);
}

/* complex secant on F(y): F is analytic in y and vanishes at the event */
static double secant(double ya, double yb, int steps) {
  bank_t A = bank(ya), Bv = bank(yb);
  double fa_r = A.fre, fa_i = A.fim, fb_r = Bv.fre, fb_i = Bv.fim;
  for (int i = 0; i < steps; i++) {
    double dr = fb_r - fa_r, di = fb_i - fa_i;
    double den = dr * dr + di * di;
    if (den == 0.0) break;
    /* (yb - ya) is real; step = -F(b) * (yb-ya) / (F(b)-F(a)), take Re */
    double h = yb - ya;
    double num_r = fb_r * dr + fb_i * di; /* Re[ F(b) * conj(dF) ] */
    double yn = yb - h * num_r / den;
    ya = yb; fa_r = fb_r; fa_i = fb_i;
    yb = yn;
    bank_t C = bank(yb);
    fb_r = C.fre; fb_i = C.fim;
    fprintf(stderr, "  secant %d: y=%.15f  c=%.4e\n", i + 1, yb, C.closure);
  }
  return yb;
}

int main(int argc, char **argv) {
  const char *nt = getenv("ETA_THREADS");
  if (nt) NTHREADS = atoi(nt);
  if (NTHREADS < 1) NTHREADS = 1;
  if (NTHREADS > 64) NTHREADS = 64;

  if (argc < 2) {
    fprintf(stderr, "usage: %s value|scan|locate|refine ...\n", argv[0]);
    return 2;
  }

  if (strcmp(argv[1], "value") == 0) {
    double y = atof(argv[2]);
    report(y, bank(y), "value");
    return 0;
  }

  if (strcmp(argv[1], "scan") == 0) {
    double y0 = atof(argv[2]), y1 = atof(argv[3]);
    int per = atoi(argv[4]);
    int npt = (int)((y1 - y0) * per);
    if (npt < 9) npt = 9;
    for (int i = 0; i < npt; i++) {
      double y = y0 + (y1 - y0) * i / (npt - 1);
      bank_t B = bank(y);
      printf("%.12f %.6e\n", y, B.closure);
      fflush(stdout);
    }
    return 0;
  }

  if (strcmp(argv[1], "locate") == 0) {
    double y0 = atof(argv[2]), y1 = atof(argv[3]);
    int per = atoi(argv[4]);
    int npt = (int)((y1 - y0) * per);
    if (npt < 9) npt = 9;
    double *ys = malloc(sizeof(double) * npt), *cs = malloc(sizeof(double) * npt);
    for (int i = 0; i < npt; i++) {
      ys[i] = y0 + (y1 - y0) * i / (npt - 1);
      cs[i] = bank(ys[i]).closure;
      fprintf(stderr, "  scan %.6f  %.3e\n", ys[i], cs[i]);
    }
    double *tmp = malloc(sizeof(double) * npt);
    memcpy(tmp, cs, sizeof(double) * npt);
    for (int i = 1; i < npt; i++) {
      double v = tmp[i];
      int j = i - 1;
      while (j >= 0 && tmp[j] > v) { tmp[j + 1] = tmp[j]; j--; }
      tmp[j + 1] = v;
    }
    double med = tmp[npt / 2];
    double step = ys[1] - ys[0];
    for (int i = 1; i < npt - 1; i++) {
      if (cs[i] < cs[i - 1] && cs[i] < cs[i + 1] && cs[i] < 0.25 * med) {
        double y = secant(ys[i] - 0.5 * step, ys[i] + 0.5 * step, 4);
        report(y, bank(y), "event");
      }
    }
    return 0;
  }

  if (strcmp(argv[1], "refine") == 0) {
    double ya = atof(argv[2]), yb = atof(argv[3]);
    int steps = argc > 4 ? atoi(argv[4]) : 4;
    double y = secant(ya, yb, steps);
    report(y, bank(y), "event");
    return 0;
  }

  fprintf(stderr, "unknown mode %s\n", argv[1]);
  return 2;
}
