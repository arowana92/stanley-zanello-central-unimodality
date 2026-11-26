# A local comparison at the mode of an exponential tilt

Let $s=m^{3/2}$ for word length $m=2n$ or $2n+1$, let $P_m(k)$ be the probability of corank $k$, and let $f$ be the limiting density of half the Brownian meander area. For a real parameter $h$ write $P_{m,h}(k)$ and $f_h(x)$ for the probability laws obtained by multiplying by $e^{-hk/s}$ and $e^{-hx}$ respectively and normalizing. Put $\delta^2 p(k)=p(k-1)-2p(k)+p(k+1)$.

**Tilted comparison.** If $R=10^{-4}m^{1/28}\ge10^6$ and $-R\le h\le R^3$, then
$$\sup_{k\in\mathbb Z}|s^3\delta^2P_{m,h}(k)-f_h''(k/s)|<1. \tag{1}$$
In particular, whenever $x=k/s>0$ and $-R\le(\log f)'(x)\le R^3$, the original coefficients satisfy $b_k^2>b_{k-1}b_{k+1}$.

For the implication choose $h=(\log f)'(x)$. The smooth positive density $f_h$ has logarithmic second derivative at most $-12$ by the [Gaussian projection proof](peak-window.md#curvature-of-the-limiting-density). It has its maximum at $x$. Integrating $f_h(y)\le f_h(x)e^{-6(y-x)^2}$ gives $f_h(x)\ge\sqrt{6/\pi}$. Thus $f_h''(x)\le-12f_h(x)<-1$, and (1) makes the tilted lattice mass at $k$ strictly exceed the average of its neighbors. Undoing a geometric tilt preserves the sign of the log-concavity determinant.

## The random clock and two deterministic times

Use the [Brownian embedding](peak-rate.md#coupling-the-area-while-retaining-the-wall) with Brownian motion $B$, unit crossing times $T_i$, durations $D_i=T_i-T_{i-1}$ and walk heights $H_i=B(T_i)$. The durations are independent of all walk signs. Use $K=\sum_{i=1}^m\lfloor H_i/2\rfloor$ also on nonsurviving walks. Let $A$ be discrete survival, and $C_t$ continuous survival above $-1$ through time $t$. For estimates (2)–(5) allow any $R\ge10^6$ and $\epsilon=m^{-1/2}$ such that $10^{-56}R^{-14}\le\epsilon\le10^{-35}R^{-7}$. Both the tilt range $-R\le h\le R^3$ and the upper end $T$ of the Fourier interval refer to this $R$. Write
$$
V=10^5R\sqrt m,\quad t_\pm=m\pm V,\quad
Y_t=\frac{1}{2t^{3/2}}\int_0^t(1+B_u)\,du,\quad T=10^9R^3.
$$
There is an event $G$ with $\Pr(G^c)\le e^{-1000R^2}$ such that on $G$
$$
C_{t_+}\ \subseteq\ A\ \subseteq\ C_{t_-},\qquad
|K/s-Y_{t_\pm}|\le 2\cdot10^{11}\epsilon R^2=:\eta. \tag{2}
$$
The inclusions mean that the corresponding indicators are ordered on $G$.

To prove (2) impose $|T_m-m|\le V$, $\sup_{u\le m+V}|B_u|\le V$ and $|\sum_{i=1}^m H_i(D_i-1)|\le V^2$. Reflection bounds the failure of the Brownian supremum by $4e^{-V^2/(4m)}$. For the clock use $\mathbb E e^{v(D_i-1)}\le e^{10^6v^2}$ for $|v|\le.001$. Indeed $\mathbb E D_i=1$ and $\Pr(D_i>j)\le .96^j$ at integer $j$, since from any point inside $[-1,1]$ an absolute displacement greater than two in the next unit of time forces exit. Taylor's inequality gives the claimed bound using $\sum_{j\ge0}(j+2)^2e^{.001(j+2)}.96^j<10^6$. For deterministic weights bounded by $M$ in absolute value and threshold $b$, exponential Markov gives $2\exp(-b^2/(4\cdot10^6 mM^2))$ for the two-sided sum of the weighted centered durations, provided $b/(2\cdot10^6 m M)\le.001$. Use $(M,b)=(1,V)$ first. On the two preceding good events all $|H_i|\le V$. To bound failure of the third condition with $|H_i|\le V$, condition only on the walk signs and use $(M,b)=(V,V^2)$. The two exponents are both $-V^2/(4\cdot10^6 m)=-2500R^2$, proving the probability estimate.

The walk first reaches $-1$ at precisely the Brownian crossing time of that vertex, giving the inclusions. Replacing $2K$ by $\sum H_i$, then by $\sum H_iD_i$, then by $\int_0^{T_m}(1+B_u)\,du$ costs at most $m+V^2+3T_m$ on $G$. Changing the time to $t_\pm$ costs at most $2V(1+V)$. Division by $2s$ gives an error below $3\cdot10^{10}\epsilon R^2$. Finally $|(m/t_\pm)^{3/2}-1|\le4V/m$ and the absolute integral up to $t_\pm$ divided by $2s$ is below $2\cdot10^5R$. These give (2).

## Relative normalization at the boundary

Let $W$ be standard three-dimensional Brownian motion, $g=1/|W_1|$ and $Y^0=\frac12\int_0^1|W_u|\,du$. Define
$$I_h(\xi)=\mathbb E[g e^{(-h+i\xi)Y^0}],\qquad Z_*=m^{-1/2} I_h(0).$$
By Imhof's relation $I_h(\xi)/I_h(0)$ is the characteristic function of $f_h$. We have $I_h(0)\ge e^{-16R^2}$ by restricting all three coordinates to $[-1/(2R),1/(2R)]$ for unit time. Each stays there with probability at least $e^{-\pi^2R^2/2}$ by the positive killed cosine eigenfunction. On this event $g\ge R$, $Y^0\le1/(2R)$ and $hY^0\le R^2/2$. [Meander and radial laws](peak-rate.md#starting-height-and-meander-law)

For $t=t_\pm$ let $Q_t(\xi)=\mathbb E[{\bf1}_{C_t}e^{(-h+i\xi)Y_t}]$ and $a=1/\sqrt t$. We claim
$$
\left|Q_t(\xi)/Z_*-I_h(\xi)/I_h(0)\right|
   \le10\epsilon(R^3+|\xi|)\qquad(|\xi|\le T). \tag{3}
$$
The killed Brownian kernel and the three-dimensional radial kernel differ by the telescoping endpoint factor as in the cited radial argument. Including the survival probability gives $Q_t(\xi)=a\,\mathbb E[e^{(-h+i\xi)Y^a}/|W_1+a e_1|]$, where $Y^a=\frac12\int |W_u+a e_1|\,du$. To keep the reciprocal endpoint identical in the two laws, put $L_a=\frac12\int_0^1 |W_u+a(1-u)e_1|\,du$. Then exactly
$$
Q_t(\xi)=a\,\mathbb E[g\,e^{aW_1^{(1)}-a^2/2}e^{(-h+i\xi)L_a}].
$$
Indeed $W_u-uW_1$ is independent of $W_1$. Shifting the Gaussian endpoint by $a e_1$ gives the displayed factor and restores the original path $W_u+a e_1$ in the integrand.

We have $|L_a-Y^0|\le a/2$. On $\sup |W_u|\le R^2$ use $a\le2\epsilon$ and $|\log(a/\epsilon)|\le 2V/m$. The logarithm of the real weight ratio to the integrand of $Z_*$ has modulus at most $2V/m+2\epsilon R^2+2\epsilon^2+\epsilon R^3<4\epsilon R^3$. The phases differ by at most $\epsilon|\xi|$. For the tails write $M=\sup|W_u|$. Reflection gives $\Pr(M>z)\le12e^{-z^2/6}$, and $\mathbb E g^2=1$ by Gaussian integration. Thus $\mathbb E[g e^{(R+1)M}{\bf1}_{M>R^2}]\le e^{-R^4/100}$ by Cauchy–Schwarz and integration of the Gaussian tail, using $2(R+1)z\le z^2/12$ above $R^2$. This bounds both discarded terms after division by $\epsilon$ up to a factor of four, since $h\ge-R$ and $Ra\le1$. Division by $I_h(0)\ge e^{-16R^2}$ gives (3).

Put $D(\xi)=\mathbb E[{\bf1}_A\exp((-h+i\xi)K/s)]$. Removing $G^c$ from $D$ or either $Q_t$ costs at most $\epsilon Z_*$ at every frequency. For $h\ge0$ the survival indicators make both real weights at most one. For $-R\le h<0$ use the unconstrained identity $K=D_0-S$ with $D_0=\lfloor m^2/4\rfloor$ and $S$ the sum of independent fair down-step labels. Its mean in units of $s$ has modulus at most one, and Hoeffding gives $\mathbb E e^{uK/s}\le e^{|u|+u^2/8}$. The unconstrained Brownian $Y_t$ is Gaussian with mean $a/2$ and variance $1/12$. Cauchy–Schwarz with $u=-2h\le2R$ and $\Pr(G^c)\le e^{-1000R^2}$ gives the claim, using $\epsilon\ge10^{-56}R^{-14}$ and $Z_*\ge\epsilon e^{-16R^2}$.

On $G$, (2) sandwiches $D(0)$ between the masses of $C_{t_+}$ and $C_{t_-}$ up to factors $e^{\pm R^3\eta}$ and discarded masses at most $3\epsilon Z_*$. By (3), $|D(0)/Z_*-1|\le 3R^3\eta$. The discrete mass of $A\setminus(C_{t_+}\cap G)$ divided by $Z_*$ is at most $6R^3\eta$, by subtracting the lower comparison on $C_{t_+}\cap G$. On that common event the real weight ratio differs from one by at most $2R^3\eta$ and the phases differ by at most $|\xi|\eta$. Compare the complex integrals there, apply (3) and normalize by $D(0)$. These inequalities give
$$
\left|\frac{D(\xi)}{D(0)}-\frac{I_h(\xi)}{I_h(0)}\right|
 \le 10^{13}\epsilon R^2(R^3+|\xi|)\qquad (|\xi|\le T). \tag{4}
$$
For example the common-event error divided by $Z_*$ is at most $2(2R^3+|\xi|)\eta$, and the normalization costs at most $4R^3\eta$ in the characteristic function since $|D(\xi)|\le D(0)$.

## High frequencies under either sign of tilt

For any word length $M\ge\max(4,h^2)$ let $\Phi_{M,h}$ be the characteristic function of the scaled tilted lattice area. We use
$$|\Phi_{M,h}(\xi)|\le \exp(100(1+h^2)-|\xi|^{2/3}/4000)
\qquad(|\xi|\le\pi M^{3/2}). \tag{5}$$
Relative to the unconstrained fair law, exponential tilting makes the down indicators independent with log odds $hr/M^{3/2}$ at label $r$. The probabilities of both signs are in $[1/4,3/4]$. Put $l=\lfloor M/2\rfloor$ and let $E_j$ denote survival through the first $j$ steps. For the oscillatory suffix use the [paired-label bound](effective-middle.md#restoring-the-wall-without-losing-a-lattice-difference). In a pair each mixed configuration has probability at least $1/16$, so the unrestricted deficit is at least $\sin^2(d\theta/2)/18$ for spacing $d$ and $\theta=\xi/M^{3/2}$. Averaging the mixed phases and imposing the wall as in that argument bounds the suffix absolute row sum by $3e^{-|\xi|^{2/3}/4000}$. Dividing by the tilted survival probability introduces the prefactor $\Pr_h(E_l)/\Pr_h(E_M)$, where $\Pr_h$ here denotes the independent tilted steps before conditioning.

For completeness this ratio is bounded uniformly in $M$. On $E_l$, the prefix likelihood relative to the fair law is at most $\exp(|h|\max_{j\le l}H_j/(2\sqrt M))$. Indeed the centered weighted label sum is $-\frac12\sum_{i\le l}(M+1-i)(H_i-H_{i-1})$. Summing by parts gives the bound since all prefix heights are nonnegative, and the likelihood normalizer is a product of hyperbolic cosines at least one. The fair conditional maximum in units of $\sqrt l$ has tail at most $4e^{-x^2/8}/x$ by the [height estimate](peak-rate.md#coupling-the-area-while-retaining-the-wall). Its positive exponential moment at parameter $v$ is at most $e^{10(1+v^2)}$, by integrating that tail from one and completing the square. For the denominator, the fair conditional mean of $K/M^{3/2}$ is at most $3$ by the same maximum bound on the second moment. Jensen gives $\mathbb E[e^{-hK/M^{3/2}}{\bf1}_{E_M}]\ge e^{-3|h|}\Pr(E_M)$. The independent tilt normalizer is at most $e^{|h|+h^2/8}$ by Hoeffding. Combining with $\Pr(E_l)/\Pr(E_M)\le4$ proves (5).

For an exact check of the tilt identity, the verifier weights each up step of label $r$ by $a^r$ and each down step by $b^r$. It compares the surviving mass at every corank with the rank counts from direct partition enumeration for both $(a,b)=(2,3)$ and $(3,2)$ and every word length from two through twelve. It also checks $K=D_0-S$ on the discarded words. [Verification code](verify_blocks.py)

~~~sh
python3 -B -c 'from verify_blocks import check_area_tilts; check_area_tilts()'
~~~

For each fixed $h$ the tilted laws converge weakly to the law of density $f_h$ by the [meander limit](peak-window.md#differentiable-local-limits) and uniform integrability of their untilted exponential weights, using the fair conditional maximum bound. Passing $M\to\infty$ in (5) therefore gives the same envelope for $I_h(\xi)/I_h(0)$ on the whole real line. This establishes the continuum bound at any real $h$ including the one chosen for the current $m$.

For $0\le h\le R^3$ we also need (5) with prefactor $e^{100(1+R^2)}$ in place of $e^{100(1+h^2)}$, both at $M=m$ and in the continuum. Use fair steps in the block argument, attaching the real factor $\exp(-h\lfloor H_j/2\rfloor/M^{3/2})$ at each surviving step. Every path's retained weight lies in $[0,1]$. For an unrestricted row bound $\rho$, a weighted killed row of total real mass $p$ has absolute row sum at most both $p$ and $\rho+1-p$, just as for a wall alone. For fixed block endpoints the area phase differs from the label-sum phase only by a constant, by summing prefix down counts. Thus the same oscillatory suffix bound holds and the unnormalized prefix costs at most the fair $\Pr(E_l)$. At $M=m$ divide by $D(0)\ge\epsilon e^{-16R^2}/2$ and use $\Pr(E_l)\le2/\sqrt m$. For the continuum take $M\to\infty$ with $h,R$ fixed. The fair survival ratio is bounded by four, and the conditional tilt normalizer tends to $I_h(0)/I_0(0)\ge e^{-16R^2}/2$ since $I_0(0)=\sqrt{2/\pi}$. These bounds give the required prefactor.

## Inversion at lattice spacing $1/s$

For $|\xi|\ge T$, the envelopes just proved are at most $e^{-|\xi|^{2/3}/8000}$ because $T^{2/3}/8000=125R^2>100(1+R^2)$. The tail in the inversion integrals for the second difference and the density's second derivative has absolute value below $.01$ in total. For instance extract $e^{-T^{2/3}/16000}$ and integrate $\xi^2e^{-|\xi|^{2/3}/16000}$ over the real line. Outside the lattice Fourier interval only the limiting transform is needed.

On $[-T,T]$ the scaled lattice multiplier is $-4s^2\sin^2(\xi/(2s))$. Its difference from $-\xi^2$ is at most $\xi^4/(12s^2)$ and its modulus is at most $\xi^2$. Equation (4) bounds the characteristic-function error after integration by $2\cdot10^{22}\epsilon R^5 T^3=2\cdot10^{-7}$. The multiplier costs at most $T^5/s^2<.01$ at the tilt scale of (1), where $\epsilon=10^{-56}R^{-14}$ and $s=\epsilon^{-3}$. This proves (1).

## A range of coranks with strict log-concavity

For either central family at every $m\ge10^{280}$ the coefficients are strictly log-concave at all integer coranks
$$4\cdot10^4 m^{41/28}\le k\le D_0/2.$$

We first bound the limiting density below on $[u,5]$ for $0<u\le1/20$. The bound is $\exp(-3/u^2)$ everywhere on this interval. To see this, put all three Brownian coordinates inside $[-2u/\sqrt3,2u/\sqrt3]$ up to time one. The killed cosine eigenfunction gives event probability at least $\exp(-9\pi^2/(32u^2))$. Here $Y^0\le u$ and the Imhof weight $\sqrt{\pi/2}\,g$ exceeds one. Hence there is a point below $u$ with density at least $\exp(-3/u^2)$. For a point above five, take the tube of Euclidean radius $1/2$ about the straight path $24t e_1$. The centered tube contains the paths confined in each coordinate to $[-1/4,1/4]$ with joint survival probability at least $e^{-6\pi^2}$. Changing measure to drift $24e_1$ gives the shifted tube at least $e^{-288-12}$ times the centered mass, by its endpoint displacement. The half-area is within $1/4$ of six and the Imhof weight exceeds $1/25$. This gives a point above five with density at least $e^{-365}$. Log-concavity between the two points proves the asserted bound.

Now put $u=2/R$ and $g_0=\log f$. The [fair Fourier estimate](peak-rate.md#fourier-inversion-for-lattice-differences) gives $f\le 10^{11}$. For $2u\le x\le4$, use the secant from $x-u$ to $x$ to get $g_0'(x)\le(\log(10^{11})+3/u^2)/u<R^3$. For the lower bound use the secant to five and apply the density bound at $u=1/20$. As $5-x\ge1$, this gives $g_0'(x)\ge-1200-\log(10^{11})>-R$. The mode comparison therefore proves strict log-concavity from $4s/R=4\cdot10^4m^{41/28}$ through $4s$. The [increasing-side curvature theorem](first-passage.md) covers $4s\le k\le D_0/2$. The [small-corank estimate](harmonic-small-area.md) meets the lower endpoint for $n\ge10^{550}$. [Interval overlap](finite-reduction.md#joining-the-three-intervals)

## Strict increase in corank under a larger positive tilt

Let $R_0=10^{-4}m^{1/28}\ge10^6$ and $R_1=10^{-5}m^{1/14}$. At any corank with $x=k/s>0$ and
$$R_0^3<h=(\log f)'(x)\le R_1^3,$$
we have $b_{k+1}>b_k$. This holds for each parity. We compare the first forward difference at the mode of the tilted density; undoing the tilt then gives the sign.

Put $R=h^{1/3}$. Since $R_0<R\le R_1$, we have $10^{-56}R^{-14}\le\epsilon=m^{-1/2}\le10^{-35}R^{-7}$. These are the hypotheses for (2)–(5). In the clock estimate $V/m=10^5\epsilon R$ and in the relative mass estimate the real exponent error is $R^3\eta=2\cdot10^{11}\epsilon R^5$. Both are below $10^{-20}$. The lower bound on $\epsilon$ ensures $e^{-R^4/100+16R^2}<\epsilon$ and $e^{-400R^2}<\epsilon^2e^{-16R^2}$ for the discarded terms.

Here a lower cutoff $T_1=10^6R^3$ in Fourier inversion suffices. On an even suffix of $2\lceil m/4\rceil$ fair steps, the [paired-step row bound](harmonic-small-area.md#comparing-two-frequencies) gives $2e^{-|\xi|^{2/3}/150}$ after retaining positive tilt weights in $[0,1]$. The prefix costs at most $2/\sqrt m$ by the ballot survival probability. Dividing by $D(0)\ge\epsilon e^{-16R^2}/2$ gives a normalized bound $8e^{16R^2-|\xi|^{2/3}/150}$ on the lattice Fourier interval. The same bound with prefactor 16 holds on the real line for the limiting tilted transform. Indeed take a word length $M\to\infty$ with $h,R$ fixed, using the prefix/full fair survival ratio at most four and the limiting conditional normalizer $I_h(0)/I_0(0)\ge e^{-16R^2}/2$. For $|\xi|\ge T_1$ both envelopes are below $e^{-|\xi|^{2/3}/300}$ since $T_1^{2/3}=10^4R^2$. Their combined inversion tails weighted by $1+|\xi|$ cost less than $.01$, by extracting $e^{-T_1^{2/3}/600}$ and integrating the other factor.

On $[-T_1,T_1]$, (4) bounds the transform error by $2\cdot10^{19}\epsilon R^5$. For the density the integrated error is at most $2\cdot10^{25}\epsilon R^8$. For the first difference the multiplier $s(e^{-i\xi/s}-1)$ has modulus at most $|\xi|$ and differs from $-i\xi$ by at most $\xi^2/(2s)$. Thus the integrated error for this comparison is at most $2\cdot10^{31}\epsilon R^{11}+T_1^3/s$, including the factor $1/(2\pi)$ in inversion. Since $s=\epsilon^{-3}$ and $\epsilon R^7\le10^{-35}$, we have
$$
|sP_{m,h}(k)-f_h(x)|<R/1000,\qquad
|s^2\Delta P_{m,h}(k)-f_h'(x)|<R^4/1000.
$$

At least $1-e^{-4R^2}$ of the limiting tilted mass lies in $[0,20/R]$. Indeed $I_h(0)\ge e^{-16R^2}$, and on the complement $e^{-hY^0}\le e^{-20R^2}$ with $\mathbb E g=I_0(0)<1$. The density is maximized at $x$ by the choice of $h$, so $f_h(x)>R/21$ and $f_h'(x)=0$. Consequently $sP_{m,h}(k)>R/22$ and $|\Delta P_{m,h}(k)|/P_{m,h}(k)<22h/(1000s)$. As $0<h/s=R^3\epsilon^3<1$, multiplying the adjacent ratio by $e^{h/s}$ upon undoing the tilt proves strict increase.

On $4/R_1\le x\le4$ the density secants in the preceding section, with $u=2/R_1$, give $-R_0\le(\log f)'(x)\le R_1^3$. This slope decreases with $x$. Thus this interval has strict growth in corank for all lattice points with slope above $R_0^3$, followed by strict log-concavity wherever the slope is at most $R_0^3$, using (1) at $R_0$. Either portion may be empty. The [overlap proof](finite-reduction.md#unimodality-from-the-first-difference) joins these signs to the rest of the rank sequence.
