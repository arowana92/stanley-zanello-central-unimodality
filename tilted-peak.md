# A local comparison at the mode of an exponential tilt

Let $s=m^{3/2}$ for word length $m=2n$ or $2n+1$, let $P_m(k)$ be the probability of corank $k$, and let $f$ be the limiting density of half the Brownian meander area. For a real parameter $h$ write $P_{m,h}(k)$ and $f_h(x)$ for the probability laws obtained by multiplying by $e^{-hk/s}$ and $e^{-hx}$ respectively and normalizing. Put $\delta^2 p(k)=p(k-1)-2p(k)+p(k+1)$.

**Tilted comparison.** If $R=m^{1/40}\ge10^{24}$ and $-R\le h\le R^3$, then
$$\sup_{k\in\mathbb Z}|s^3\delta^2P_{m,h}(k)-f_h''(k/s)|<1. \tag{1}$$
In particular, whenever $x=k/s>0$ and $-R\le(\log f)'(x)\le R^3$, the original coefficients satisfy $b_k^2>b_{k-1}b_{k+1}$.

For the implication choose $h=(\log f)'(x)$. The smooth positive density $f_h$ has logarithmic second derivative at most $-12$ by the [Gaussian projection proof](peak-window.md#curvature-of-the-limiting-density). It has its maximum at $x$. Integrating $f_h(y)\le f_h(x)e^{-6(y-x)^2}$ gives $f_h(x)\ge\sqrt{6/\pi}$. Thus $f_h''(x)\le-12f_h(x)<-1$, and (1) makes the tilted lattice mass at $k$ strictly exceed the average of its neighbors. Undoing a geometric tilt preserves the sign of the log-concavity determinant.

## The random clock and two deterministic times

Use the [Brownian embedding](peak-rate.md#coupling-the-area-while-retaining-the-wall) with Brownian motion $B$, unit crossing times $T_i$, durations $D_i=T_i-T_{i-1}$ and walk heights $H_i=B(T_i)$. The durations are independent of all walk signs. Use $K=\sum_{i=1}^m\lfloor H_i/2\rfloor$ also on nonsurviving walks. Let $A$ be discrete survival, and $C_t$ continuous survival above $-1$ through time $t$. Write
$$
V=\sqrt m\,R^2,\quad t_\pm=m\pm V,\quad
Y_t=\frac{1}{2t^{3/2}}\int_0^t(1+B_u)\,du,\quad T=R^{7/2}.
$$
There is an event $G$ with $\Pr(G^c)\le e^{-R^3}$ such that on $G$
$$
C_{t_+}\ \subseteq\ A\ \subseteq\ C_{t_-},\qquad
|K/s-Y_{t_\pm}|\le 30R^{-16}. \tag{2}
$$
The inclusions mean that the corresponding indicators are ordered on $G$.

To prove (2) impose $|T_m-m|\le V$, $\sup_{u\le m+V}|B_u|\le V$ and $|\sum_{i=1}^m H_i(D_i-1)|\le mR^4$. Reflection bounds the failure of the Brownian supremum by $4e^{-R^4/4}$. For the clock use $\mathbb E e^{v(D_i-1)}\le e^{10^6v^2}$ for $|v|\le.001$. Indeed $\mathbb E D_i=1$ and $\Pr(D_i>j)\le .96^j$ at integer $j$, since from any point inside $[-1,1]$ an absolute displacement greater than two in the next unit of time forces exit. Taylor's inequality gives the claimed bound using $\sum_{j\ge0}(j+2)^2e^{.001(j+2)}.96^j<10^6$. For deterministic weights bounded by $M$ in absolute value and threshold $b$, exponential Markov gives $2\exp(-b^2/(4\cdot10^6 mM^2))$ for the two-sided sum of the weighted centered durations, provided $b/(2\cdot10^6 m M)\le.001$. Use $(M,b)=(1,V)$ first. On the two preceding good events all $|H_i|\le V$. To bound failure of the third condition with $|H_i|\le V$, condition only on the walk signs and use $(M,b)=(V,mR^4)$. The two exponents are both $-R^4/(4\cdot10^6)$, proving the probability estimate.

The walk first reaches $-1$ at precisely the Brownian crossing time of that vertex, giving the inclusions. Replacing $2K$ by $\sum H_i$, then by $\sum H_iD_i$, then by $\int_0^{T_m}(1+B_u)\,du$ costs at most $m+mR^4+3T_m$ on $G$. Changing the time to $t_\pm$ costs at most $2V(1+V)$. Dividing by $2s$ gives an error below $5R^{-16}$, since $m=R^{40}$. Finally $|(m/t_\pm)^{3/2}-1|\le4V/m$, and the absolute integral up to $t_\pm$ divided by $2s$ is below $2R^2$. This proves (2).

## Relative normalization at the boundary

Let $W$ be standard three-dimensional Brownian motion, $g=1/|W_1|$ and $Y^0=\frac12\int_0^1|W_u|\,du$. Define
$$I_h(\xi)=\mathbb E[g e^{(-h+i\xi)Y^0}],\qquad Z_*=m^{-1/2} I_h(0).$$
By Imhof's relation $I_h(\xi)/I_h(0)$ is the characteristic function of $f_h$. We have $I_h(0)\ge e^{-16R^2}$ by restricting all three coordinates to $[-1/(2R),1/(2R)]$ for unit time. Each stays there with probability at least $e^{-\pi^2R^2/2}$ by the positive killed cosine eigenfunction. On this event $g\ge R$, $Y^0\le1/(2R)$ and $hY^0\le R^2/2$. [Meander and radial laws](peak-rate.md#starting-height-and-meander-law)

For $t=t_\pm$ let $Q_t(\xi)=\mathbb E[{\bf1}_{C_t}e^{(-h+i\xi)Y_t}]$ and $a=1/\sqrt t$. We claim
$$
|Q_t(0)/Z_*-1|\le R^{-16},\qquad
\left|Q_t(\xi)/Z_*-I_h(\xi)/I_h(0)\right|\le R^{-16}\quad(|\xi|\le T). \tag{3}
$$
The killed Brownian kernel and the three-dimensional radial kernel differ by the telescoping endpoint factor as in the cited radial argument. Including the survival probability gives $Q_t(\xi)=a\,\mathbb E[e^{(-h+i\xi)Y^a}/|W_1+a e_1|]$, where $Y^a=\frac12\int |W_u+a e_1|\,du$. To keep the reciprocal endpoint identical in the two laws, put $L_a=\frac12\int_0^1 |W_u+a(1-u)e_1|\,du$. Then exactly
$$
Q_t(\xi)=a\,\mathbb E[g\,e^{aW_1^{(1)}-a^2/2}e^{(-h+i\xi)L_a}].
$$
Indeed $W_u-uW_1$ is independent of $W_1$. Shifting the Gaussian endpoint by $a e_1$ gives the displayed factor and restores the original path $W_u+a e_1$ in the integrand.

We have $|L_a-Y^0|\le a/2$. On $\sup|W_u|\le R^2$, use $a\le2R^{-20}$, $|a\sqrt m-1|\le2R^{-18}$. The real weight in $Q_t$ relative to the corresponding integrand of $Z_*$ lies between $e^{-8R^{-17}}$ and $e^{8R^{-17}}$. The phases differ by at most $TR^{-20}$. To bound the discarded tails, write $M=\sup|W_u|$. Reflection gives $\Pr(M>z)\le12e^{-z^2/6}$. Also $\mathbb E g^2=1$ by integration of the three-dimensional Gaussian. Thus $\mathbb E[g e^{(R+1)M}{\bf1}_{M>R^2}]\le e^{-R^4/100}$. For example apply Cauchy–Schwarz, then integrate the Gaussian tail against the derivative of $e^{2(R+1)z}$ above $R^2$, using $2(R+1)z\le z^2/12$ there. This bounds the discarded terms for both integrands up to a factor of two since $h\ge-R$, both areas are nonnegative and $Ra\le1$. Dividing by the lower bound on $I_h(0)$ proves (3).

Put $D(\xi)=\mathbb E[{\bf1}_A\exp((-h+i\xi)K/s)]$. Removing $G^c$ from $D$ or either $Q_t$ costs at most $R^{-100}Z_*$ at every frequency. For $h\ge0$ the survival indicators make both real weights at most one. For $-R\le h<0$ use the unconstrained identity $K=D_0-S$ with $D_0=\lfloor m^2/4\rfloor$ and $S$ the sum of independent fair down-step labels. Its mean in units of $s$ has modulus at most one, and Hoeffding gives $\mathbb E e^{uK/s}\le e^{|u|+u^2/8}$. The unconstrained Brownian $Y_t$ is Gaussian with mean $a/2$ and variance $1/12$. Cauchy–Schwarz with $u=-2h\le2R$ and $\Pr(G^c)\le e^{-R^3}$ gives the claim.

On $G$, (2) sandwiches the real mass $D(0)$ between the masses for $C_{t_+}$ and $C_{t_-}$ up to relative factors $e^{\pm30R^{-13}}$ and the just bounded discarded terms. Hence $|D(0)/Z_*-1|\le 100R^{-13}$ by (3). In particular the discrete tilted mass of $A\setminus(C_{t_+}\cap G)$ divided by $Z_*$ is at most $200R^{-13}$, by subtracting the lower comparison for $C_{t_+}\cap G$. On that common event the real weight ratio differs from one by at most $40R^{-13}$ and the phases differ by at most $30|\xi|R^{-16}$. Comparing the complex integrals there, then applying (3) and normalizing, gives
$$
\left|\frac{D(\xi)}{D(0)}-\frac{I_h(\xi)}{I_h(0)}\right|\le R^{-12}\qquad(|\xi|\le T). \tag{4}
$$
For example the common-event difference divided by $Z_*$ is at most $2(40R^{-13}+30TR^{-16})$. All errors above fit in (4) because $T=R^{7/2}$ and $R\ge10^{24}$. The small absolute survival or area probability has canceled.

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

For $0\le h\le R^3$ we also need (5) with prefactor $e^{100(1+R^2)}$ in place of $e^{100(1+h^2)}$, both at $M=m$ and in the continuum. Use fair steps in the block argument, attaching the real factor $\exp(-h\lfloor H_j/2\rfloor/M^{3/2})$ at each surviving step. Every path's retained weight lies in $[0,1]$. For an unrestricted row bound $\rho$, a weighted killed row of total real mass $p$ has absolute row sum at most both $p$ and $\rho+1-p$, just as for a wall alone. For fixed block endpoints the area phase differs from the label-sum phase only by a constant, by summing prefix down counts. Thus the same oscillatory suffix bound holds and the unnormalized prefix costs at most the fair $\Pr(E_l)$. At $M=m$ divide by $D(0)\ge R^{-20}e^{-16R^2}/2$ and use $\Pr(E_l)\le2/\sqrt m$. For the continuum take $M\to\infty$ with $h,R$ fixed. The fair survival ratio is bounded by four, and the conditional tilt normalizer tends to $I_h(0)/I_0(0)\ge e^{-16R^2}/2$ since $I_0(0)=\sqrt{2/\pi}$. These bounds give the required prefactor.

## Inversion at lattice spacing $1/s$

For $|\xi|\ge T$, the envelopes just proved are at most $e^{-|\xi|^{2/3}/8000}$ because $R^{7/3}/8000>100(1+R^2)$. The tail in the inversion integrals for the second difference and the density's second derivative has absolute value below $.01$ in total. For instance extract $e^{-T^{2/3}/16000}$ and integrate $\xi^2e^{-|\xi|^{2/3}/16000}$ over the real line. Outside the lattice Fourier interval only the limiting transform is needed.

On $[-T,T]$ the scaled lattice multiplier is $-4s^2\sin^2(\xi/(2s))$. Its difference from $-\xi^2$ is at most $\xi^4/(12s^2)$ and its modulus is at most $\xi^2$. Equation (4) bounds the error from the characteristic functions here by $T^3R^{-12}$ and the multiplier costs at most $T^5/s^2$. Their sum is less than $.01$ since $s=R^{60}$. This proves (1).

## A range of coranks with strict log-concavity

For either central family, at every $m\ge10^{960}$ the coefficients are strictly log-concave at all integer coranks
$$2000\,m^{59/40}\ \le\ k\ \le\ D_0/2.$$
To see this take $u=10^3/R\le10^{-5}$. The [Brownian tube bound](finite-reduction.md#density-lower-bound-and-inversion) gives $f\ge 2^{-\lceil10^8/u^2\rceil}$ on $[u,201]$, and the [fair Fourier bound](peak-rate.md#fourier-inversion-for-lattice-differences) gives $f\le10^{11}$. With $g=\log f$, concavity bounds $g'(x)$ above by the secant slope from $x-u$. For $2u\le x\le200.5$ this gives
$$g'(x)\le \frac{\log(10^{11})+\lceil10^8/u^2\rceil\log2}{u}\le10^9/u^3=R^3.$$
For the lower bound take the secant from $x$ to $201$. Applying the tube bound with the fixed parameter $10^{-5}$ gives $g(201)\ge-10^{18}\log2$. Since $201-x\ge1/2$, the slope exceeds $-10^{19}\ge-R$.

Take $x=k/s$ in (1). The lower endpoint $2us$ equals $2000m^{59/40}$. The [increasing-side curvature theorem](effective-middle.md) covers all larger coranks from $200s$ to $D_0/2$. This proves the assertion, and the [small-area bridge estimate](effective-small-area.md#a-wider-window-at-large-sizes) connects its lower end to the high-rank tail for $n\ge10^{1700}$.
