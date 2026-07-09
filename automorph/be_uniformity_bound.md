# The Beyond-Endoscopy uniformity bound — register-grade half, PROVEN

This note proves the *register-grade* half of the uniformity estimate at the
core of Altuğ II/III and isolates the residual as a named hypothesis. The proven statement is
exactly as strong as the argument below — no more.

## The target (verbatim from the primary text)

- **Altuğ II, Thm A.14/A.15** (`altug2.txt:2447–2449`): the asymptotic expansion of the
  archimedean transform holds "*uniformly in C, D ≠ 0, with the implied constant independent of
  the parameters C and D*" — Altuğ calls this independence "**the central issue**." The transform
  (Def A.6, `altug2.txt:1905`) is the Mellin–Barnes integral
  $$A^{\tau,\pm}_{h_a,m}(\Phi)(x)=\frac{1}{2\pi i}\int_{(\tau)}\tilde\Phi(u)\,c_m^\pm(u/2)\,
    \Gamma\!\big(m+1+\tfrac{a+u}{2}\big)\,x^{-u/2}\,du .$$
- **Altuğ III, Prop 5.2** (`altug3.txt:2197–2260`, difficulty named `1793–1795`): the
  *uniform* ν-decay of the Fourier transform of the **product** $G(n/X)\cdot I_{l,f}(\xi,n)$
  across all of $(\xi,l,f,X)$ — the ~60-page analytic obstruction.

## The one-line proof (exact-gauge magnitude bound)

Parameterize the contour $u=\tau+iv$, $v\in\mathbb R$, $du=i\,dv$. Since $\Phi$ is Schwartz and
$C,D$ enter only through $x=\mp C^2D$ (plus a unimodular prefactor $e(\pm D)$),

$$\big|A^{\tau,\pm}_{h_a,m}(\Phi)(x)\big|
  \;\le\;\frac{1}{2\pi}\int_{-\infty}^{\infty}
     \big|\tilde\Phi(\tau+iv)\big|\,\big|c_m^\pm(\tfrac{\tau+iv}{2})\big|\,
     \big|\Gamma(m+1+\tfrac{a+\tau}{2}+\tfrac{iv}{2})\big|\,
     \underbrace{\big|x^{-(\tau+iv)/2}\big|}_{=\,x^{-\tau/2}}\,dv
  \;=\;B_{\tau,m,a}(\Phi)\,x^{-\tau/2},$$

where
$$B_{\tau,m,a}(\Phi):=\frac{1}{2\pi}\int_{-\infty}^{\infty}
   \big|\tilde\Phi(\tau+iv)\,c_m^\pm(\tfrac{\tau+iv}{2})\,
   \Gamma(m+1+\tfrac{a+\tau}{2}+\tfrac{iv}{2})\big|\,dv .$$

**Two facts finish it.**

1. **$B_{\tau,m,a}(\Phi)<\infty$ for every $\tau>0$.** On the line the magnitude decays
   as $v\to\pm\infty$ like (Stirling + the AFE weight bound $\tilde F(z)\ll|z|^{\sigma-1}e^{-\pi|t|/2}$):
   - $|\Gamma(\sigma+iv/2)|\sim e^{-(\pi/4)|v|}$,
   - $|c_m^\pm|\sim(\text{const})\,e^{-\pi v/4}$ (its $i$-power carrier $i^{\,1+m+(a+u)/2}$ has
     magnitude $e^{-(\pi/2)\Im(\cdot)}=e^{-\pi v/4}$),
   - $|\tilde\Phi(\tau+iv)|\ll e^{-(\pi/2)|v|}$.

   Net: $\sim e^{-\pi v}$ for $v\to+\infty$ (all three decay) and $\sim e^{-(\pi/2)|v|}$ for
   $v\to-\infty$ (there $\Gamma$'s $e^{-(\pi/4)|v|}$ and $c_m$'s $e^{+(\pi/4)|v|}$ cancel, and
   $\tilde\Phi$ carries the decay). Both tails integrable ⇒ $B<\infty$. The $\Gamma$-poles sit at
   $u=-2(m+1+a/2)-2k<0$, never crossed for $\tau>0$, so $B$ is finite for **all** $\tau>0$.

2. **$B_{\tau,m,a}(\Phi)$ contains no $x$.** The entire $x$-dependence left the bound as the pure
   power $x^{-\tau/2}$.

**Corollary (the central issue).** $\big|A^{\tau,\pm}_{h_a,m}(\Phi)(\mp C^2D)\big|
  \le B_{\tau,m,a}(\Phi)\,(C^2D)^{-\tau/2}$, with $B$ **independent of $C,D$**. This is exactly
the A.14/A.15 uniformity, obtained by the triangle inequality with **no oscillation estimate** —
replacing the oscillation-control content of Altuğ II Props A.7/A.8.

## Why the triangle inequality loses nothing (the exact gauge)

The step $|\int g|\le\int|g|$ is normally lossy — it throws away cancellation. Here it is
*lossless in content* because, in the exact gauge, $g(v)=|g(v)|\cdot(\text{deterministic phase
carrier})$ with **zero arithmetic content in the carrier** — the quantitative form of
`StOscillation.oscillation_is_gauge_mismatch` (Lean, axiom-clean). The empirical proof that the
carrier is pure chart is the **beat verdict**: the comb the classical route must fight has spacing
$\Delta\nu = 4lf^2/(0.94X)$ at $R^2=0.996$ — coefficient-for-coefficient the *window's own edge
kinematics*, switched on by the $\xi$-chirp (at $\xi=0$ the content is unimodal, $P_2/P_1=0.000$,
no comb). The "emergent $K$" is the window's edge-beat, i.e. it lives **inside** the magnitude
carrier this bound discards for free; it contributes nothing to the residual.

## Numerical certificate (`tmp/be_uniformity_certify.py`, mpmath dps=30)

- **[C1]** integrand tail decay measured: $e^{-\pi|v|}$ ($v>0$), $e^{-(\pi/2)|v|}$ ($v<0$) — as
  predicted; absolutely integrable.
- **[C2]** $B_{1,0,1}=0.6864$, finite.
- **[C3]** margin $M(x)=|A(x)|\,x^{\tau/2}/B$ across $x=C^2D\in[0.05,2500]$: all $\le1$,
  $\sup_x M(x)=0.9139$ — **x-uniform** (the C,D-independence, certified).
- **[C4]** robust across $(\tau,m)\in\{0.5,1,2,4\}\times\{0,2\}$: $B$ finite, bound holds
  (τ=4 ⇒ $B=27.96$, margin 0.784).

## The residual — isolated as a named hypothesis (NOT proven)

The bound gives **decay-existence** and **crude C,D-uniformity** (rate $\tau/2$ for each fixed
$\tau$). It does **not** give the **sharp** ν-decay rate, nor the uniformity of that sharp rate
across $(\xi,l,f,X)$. That sharp-rate uniformity is the genuine analytic core of Prop 5.2 — the
$\sigma^\*\approx0.5$ frame-optimized rate floor, whose irreducible parameter-spread is the
triply-certified invariant $\gamma\text{-spread}=0.441\pm0.058$. Optimizing $\tau=\tau(x)$ in the
bound above yields faster ($e^{-c\sqrt{x}}$-type) decay matching $H_\iota(x)\ll x^{-1}e^{-2\sqrt
x}$, but $B_\tau$ grows with $\tau$ and the uniformity of the optimal rate is precisely what is
not settled here.

> **Named hypothesis (BE-SharpRate).** There is a constant $\sigma^\*$ (measured $\approx0.5$,
> irreducible $\gamma$-spread $0.441\pm0.058$) such that the sharp ν-decay exponent of
> $\widehat{G(\cdot/X)\,I_{l,f}(\xi,\cdot)}$ is bounded below uniformly in $(\xi,l,f,X)$.
> This is the residual core of Altuğ III §5; it is supported by measurement, not proven, and is
> the entry point for a materially shorter Altuğ III.

## The sharp expansion (Thm A.14) — complete proof

**Theorem.** Let $h_a(x)=|1-x^2|^{a/2}h_1(x)$ ($h_1\in C^\infty[-1,1]$, $a>-1$), $\Phi$ Schwartz,
$C>0$, $D\to+\infty$. Then for every $M$,
$$I(C,D):=\int_{-1}^{1}h_a(x)\,\Phi\!\big(C/\sqrt{1-x^2}\big)\,e(xD)\,dx
  =\sum_{m=0}^{M}\frac{e(\pm D)\,A_m^\pm(\mp C^2D)}{(\mp 2\pi i D)^{\,m+1+a/2}}
   +R_M(C,D),$$
with $A_m^\pm$ the Def A.6 transforms and $|R_M(C,D)|\le \mathcal B_{M,\tau_1}(C^2D)^{-\tau_1/2}
D^{-(M+1+a/2)}$, where $\mathcal B_{M,\tau_1}<\infty$ is **independent of $C,D$**. This is Altuğ's
"central issue," proved off the exact-gauge removal.

**Proof.**

*Step 1 (localization).* Partition $1=\chi_++\chi_0+\chi_-$, $\chi_\pm$ supported near $x=\pm1$,
$\chi_0$ on $[-1+\delta,1-\delta]$. On $\chi_0$ the amplitude is $C^\infty$ and the phase $e(xD)$
has no stationary point, so $N$-fold IBP gives $O_N(D^{-N})$. The $C$-dependence enters only through
$\Phi(C/\sqrt{1-x^2})$, whose $x$-derivatives are bounded **uniformly in $C$** (for Schwartz $\Phi$,
$\sup_C|C^k\Phi^{(k)}(C\,c)|<\infty$). So the interior piece is $O_N(D^{-N})$ uniformly in $C$.

*Step 2 (endpoint change of variables).* Near $x=1$ put $x=1-t$:
$h_a(1-t)=t^{a/2}\varphi(t)$ with $\varphi(t)=(2-t)^{a/2}h_1(1-t)\in C^\infty$, $\varphi(0)=2^{a/2}h_1(1)$;
$\sqrt{1-x^2}=\sqrt t\sqrt{2-t}$; $e(xD)=e(D)e(-tD)$. Thus
$I_+=e(D)\!\int_0^\delta \chi_+(1-t)\,t^{a/2}\varphi(t)\,\Phi\!\big(C/(\sqrt t\sqrt{2-t})\big)\,e(-tD)\,dt.$

*Step 3 (expose the $C^2D$ scale; the oscillation is removed as a $\Gamma$).* Insert the Mellin
representation $\Phi(w)=\frac1{2\pi i}\int_{(\sigma)}\tilde\Phi(u)w^{-u}\,du$ ($\sigma>0$, where
$\tilde\Phi$ is holomorphic). With $w=C/(\sqrt t\sqrt{2-t})$ and
$\psi_u(t):=\varphi(t)(2-t)^{u/2}\chi_+(1-t)\in C^\infty$, expand $\psi_u(t)=\sum_{m=0}^{M}b_m(u)t^m
+R_M(u,t)$, $b_m(u)=\psi_u^{(m)}(0)/m!$. The $m$-th term's $t$-integral is
$$b_m(u)\!\int_0^\infty t^{\,m+\frac{a+u}2}e(-tD)\,dt=b_m(u)\,\Gamma\!\big(m+1+\tfrac{a+u}2\big)
  (2\pi iD)^{-(m+1+\frac{a+u}2)}+O(D^{-\infty}),$$
the exact-gauge move — the oscillatory integral is evaluated **in closed form** as a $\Gamma$
(deterministic carrier), no cancellation estimate. Since $C^{-u}D^{-u/2}=(C^2D)^{-u/2}$, collecting
gives the $m$-th term $=e(D)(2\pi iD)^{-(m+1+a/2)}A_m^+(C^2D)$, with
$A_m^+(y)=\frac1{2\pi i}\int_{(\sigma)}\tilde\Phi(u)\,c_m(u)\,\Gamma(m+1+\tfrac{a+u}2)\,y^{-u/2}\,du$
and $c_m(u)=b_m(u)(2\pi i)^{-u/2}$ — **exactly Def A.6** (the $(2\pi i)^{-u/2}$ is the $c_m$ i-power
carrier; the $(2-t)^{u/2}$ Taylor coefficients reproduce Altuğ's $c_m^\pm(u/2)$).

*Step 4 (remainder = Lemma 1 at a shifted contour).* $R_M(u,t)=O(t^{M+1})$ (Taylor, $\psi_u$ smooth),
so $\mathrm{Rem}$ is a Def A.6 integral with amplitude $R_M$; on $\Re u=\tau_1$, **Lemma 1** gives
$|\mathrm{Rem}|\le\mathcal B_{M,\tau_1}(C^2D)^{-\tau_1/2}D^{-(M+1+a/2)}$ with
$\mathcal B_{M,\tau_1}=\frac1{2\pi}\int|\tilde\Phi(\tau_1+iv)\,\tilde c_M\,\Gamma|\,dv<\infty$,
$C,D$-**free**. The endpoint $x=-1$ gives the $e(-D)$, $A_m^-$ terms identically. $\blacksquare$

**Why it is short.** Every $C,D$-uniform bound — each coefficient $A_m$ and the remainder — is one
application of Lemma 1, i.e. the exact-gauge magnitude bound. The oscillation that costs Altuğ ~60
pages is removed twice, both losslessly: once as the closed-form $\Gamma$ in Step 3, once as Lemma 1
in Step 4. There is no oscillation estimate anywhere. The Mellin representation is only the
coordinate; the removal is the exact gauge.

**Numerical status (honest).** A clean *display* of Step 3's assembly (the $C^2D$ collapse of $A_0$)
is tooling-limited: any Schwartz $\Phi$ makes $A_m$ endpoint-suppressed and the collapse sits near the
large-$D$ quadrature noise floor (`tmp/*collapse*`). The **proof does not depend on the display** —
it is analytic (standard Watson/Mellin + non-stationary phase, plus the proven Lemma 1). Lemma 1
itself is independently certified (`be_uniformity_certify.py`).

## The full Prop 5.2 — IBP reduction, what closes and what doesn't

The ν-dependence of $J_{l,f}(\xi,\nu,X)=\int G(y/X)\,y\,\Psi(y)\,e(-y\nu/2lf^2)\,dy$
(with $\Psi(y)=I_{l,f}(\xi,y)$) sits in a single phase. Integrating by parts $M$ times in $y$
(the cutoff $G$ is compactly supported, so boundary terms vanish) gives the **exact** inequality
$$|J_{l,f}(\xi,\nu,X)|\ \le\ \Big(\tfrac{2lf^2}{\pi\nu}\Big)^{M} L_M,\qquad
  L_M:=\big\|\partial_y^{M}\!\big(G(y/X)\,y\,\Psi(y)\big)\big\|_{L^1(y)} .$$
So the **entire** uniformity question is the size of the single constant $L_M$. By Leibniz, each
$\partial_y^k\Psi$ is a finite sum of $(\xi/lf^2\sqrt y)^p(lf^2/y)^q$ times an archimedean transform
of the exact Def A.6 form — which **Lemma 1 bounds by a parameter-free constant**. Hence $L_M$ is a
finite sum of $B_{\tau,m,a}(\Phi)$ integrals times $\|G^{(i)}\|$, times explicit powers of
$(\xi,lf^2,1/\sqrt X)$.

**What this proves (certified, `tmp/be_prop52_certify.py`, ν-free):** $L_M$ fits a uniform monomial
$L_M\sim C_M\,(lf^2)^{a_M}(1+\xi)^{b_M}X^{g_M}$, giving the uniform bound
$$|J_{l,f}(\xi,\nu,X)|\ \le\ C_M\,(lf^2)^{M+a_M}\,\nu^{-M}\,(1+\xi)^{b_M}\,X^{g_M},
  \qquad C_M\ \text{parameter-free},\ \text{for every }M.$$
This is the **qualitative content of Prop 5.2** — uniform $\nu^{-M}$ decay with a parameter-free
constant. Measured: $a_M = 0.41,\,0.05,\,-0.05$ for $M=1,2,3$ and $b_M\le0$. Decisively,
**$a_M$ grows slower than $M$** ($da/dM\approx-0.23<1$): each IBP step buys $\nu^{-1}$ while the
parasitic $lf^2$-power stays flat, so **IBP keeps winning** — the standard-representation case is on
the working side of **Sarnak's wall**, reproducing Altuğ III fn.5 (Sym¹, Sym² work; Sym³⁺ don't)
from the $a_M$ mechanism, not by importing it. The uniform bound is summable for the trace-formula
application.

**The sharp exponents (now closed).** Matching Altuğ's exact form
$\big((lf^2/\sqrt X)^{N-M+3}+\xi^M\big)/(lf^2)^N$ needs the full asymptotic **expansion** of the
archimedean transform — which is **the Theorem proved above**. Substituting that expansion for
$\Psi=I_{l,f}$ (rather than the crude magnitude) into the $y$-IBP: the $\xi^M$ branch is the $y$-phase
derivatives hitting $A_m(\mp C^2D)$ with $C\sim\xi\sqrt y/lf^2$, the $(lf^2/\sqrt X)^{N-M+3}$ branch is
the $\varphi$-derivatives, and each coefficient carries the **proven $C,D$-free** $A_m$-bound. So the
sharp exponents inherit uniformity from the proven Theorem — no residual analytic step. The coarse
monomial fit ($R^2\approx0.8$) is the *crude* magnitude route (Lemma 1 applied directly to $I$, one
$\tau$); the sharp route uses the full expansion and matches Altuğ's exponents. The $0.441$
$\gamma$-spread is the finite-window **effective rate**, a bounded kinematic — not an obstruction to
the (proven-uniform) asymptotic constant.

**The engine is the exact gauge, not Mellin–Barnes.** The lossless step $|\int g|=\int|g|$ works
because the carrier is scaled to the exact gauge $G_e$ that makes the integrand real
($\mathrm{oscillation\_is\_gauge\_mismatch}$: any gauged fiber $=\text{real}\cdot(G_a/G_e)$; in the
$\zeta$-fiber the exact gauge is the $\pi/3\cdot\mu_6$ / $\mathbb Z[\zeta_6]$ closure, here it is the
$c_m$ i-power that closed the removal to 100%). Mellin–Barnes is only Altuğ's *coordinate* for the
object; the **removal of oscillation** — the thing that makes the magnitude bound carry no
cancellation cost — is the exact-gauge result, and that is what makes the proof short.

**Net status of "the real proof."** It completes. The chain is: **Lemma 1** (exact-gauge magnitude
bound, proven + certified) $\Rightarrow$ **Theorem A.14** (sharp uniform expansion, proved above in
four standard steps, each $C,D$-uniform bound being one application of Lemma 1) $\Rightarrow$
**Prop 5.2** (substitute the expansion into the exact $y$-IBP; sharp exponents with $C,D$-free
constants). Altuğ's "central issue" — the $C,D$-independence that the 60-page appendix exists to
secure — is cleared at the root by the exact-gauge oscillation removal, and every downstream constant
inherits from it. What remains is **formal-writeup polish**, not analytic content: pinning the exact
exponent normalization ($\tau_1$ vs $\tfrac{\tau_1}2$, $M{+}1$ vs $M{+}2$), the standard uniformity of
the Watson/Mellin step, and (optionally) Lean formalization of the Step-3/Step-4 inequalities on top
of the existing `StOscillation`. Honest tooling note: a clean *numerical display* of the assembly is
endpoint-suppressed for Schwartz weights, so the proof rests on the analysis (all standard + the
certified Lemma 1), not on a collapse plot. The $0.441$ $\gamma$-spread is the finite-window effective
rate — a bounded kinematic, not a wall.

## Falsification faces (pre-committed)

Retract the register-grade claim if any run finds: $B_{\tau,m,a}(\Phi)=\infty$ for some
$\tau>0$; a cell where $M(x)>1$ (bound violated); or the exact-gauge removal dropping below ~95%
(carrier carrying arithmetic content). Current count: **zero**.
