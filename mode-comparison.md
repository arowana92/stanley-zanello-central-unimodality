# Joining the saddle estimate to the peak

For both central staircases the rank sequence is unimodal at every $n\ge10^{100}$. At every $n\ge10^{164}$ it is strictly log-concave at all interior ranks $j\ge D/2$. Here $m=2n$ or $2n+1$, $s=m^{3/2}$, $D=\lfloor m^2/4\rfloor$, and $b_k=a_{D-k}$. The estimates below control coranks $k/s$ down to $4/(1.2\cdot10^6)$, where the [linear-potential estimate](linear-potential.md) already gives strict increase and strict log-concavity.

## The tilt at the point of comparison

Use the [tilted meander notation](tilted-peak.md). The fair surviving walk has scaled corank $K/s$ with probabilities $P_m(k)$. Exponential weighting by $e^{-hK/s}$ and normalization give $P_{m,h}$. The corresponding continuous densities are $f$ and $f_h$ for half the Brownian meander area. Put $g=\log f$, $r_*=1.2\cdot10^6$, $x=k/s$. The [density secants](tilted-peak.md#a-range-of-coranks-with-strict-log-concavity) at $u=2/r_*$ and at $1/20$ give
$$-1250<h=g'(x)<r_*^3\qquad(4/r_*\le x\le4).$$
Indeed $g'(x)\le(\log(10^{11})+3/u^2)/u$ and $g'(x)\ge-1200-\log(10^{11})$. At this $h$, $f_h$ is maximized at $x$, and $f_h'(x)=0$. The [curvature bound](peak-window.md#curvature-of-the-limiting-density) $g''\le-12$ implies $f_h(x)\ge\sqrt{6/\pi}$ and $f_h''(x)\le-12f_h(x)$. When $h=r^3$ with $r\ge10$, also $f_h(x)>r/21$. Indeed the [radial normalization bound](tilted-peak.md#relative-normalization-at-the-boundary) $I_h(0)\ge e^{-16r^2}$ puts at least $1-e^{-4r^2}$ of the tilted mass in $[0,20/r]$.

## Smaller clock error

Let $\epsilon=m^{-1/2}$, $r=(\max(h,0))^{1/3}$ and $R=\max(2000,r,\sqrt{\log m})$. For $m\ge10^{100}$, write $\Phi_{m,h}$ and $\phi_h$ for the characteristic functions of the discrete and continuous scaled tilted laws. Then
$$|\Phi_{m,h}(\xi)-\phi_h(\xi)|\le 10^7\epsilon R^2(R^3+|\xi|)\qquad (|\xi|\le10^9 R^3). \tag{1}$$

Here are the changes to the [clock and wall comparison](tilted-peak.md#the-random-clock-and-two-deterministic-times). For the Brownian exit duration $D_1$ from $(-1,1)$, the moment generating function is $1/\cos(\sqrt{2v})$, interpreted by its real power series for $v<0$. Stop $e^{vt}\cos(\sqrt{2v}\,B_t)$ at the exit or a deterministic time and let that time tend to infinity. The exit tail $\Pr(D_1>j)\le .96^j$ justifies the limit at $|v|\le.001$. For either sign $\cos(\sqrt{2v})\ge1-v$. Thus $\log\mathbb E e^{v(D_1-1)}\le-v-\log(1-v)\le v^2$. Choose $V=100R\sqrt m$ and $t_\pm=m\pm V$. Exponential Markov for the independent centered durations at threshold $V$, and for the durations weighted by walk heights bounded by $V$ at threshold $V^2$, gives $2e^{-V^2/(4m)}$ each. For the weighted bound condition on the walk signs, independent of the durations. The largest argument of the moment generating function is $V/(2m)<.001$. Brownian reflection bounds failure of the supremum condition by $4e^{-V^2/(4m)}$. The union of failures has probability at most $e^{-1000R^2}$.

On the common good event the same survival inclusions hold. With $Y_t=(2t^{3/2})^{-1}\int_0^t(1+B_v)\,dv$ the area error satisfies
$$|K/s-Y_{t_\pm}|\le\eta=2\cdot10^5\epsilon R^2.$$
Indeed before scaling the error in the doubled area is at most $m+V^2+3t_++2V(1+V)$. Changing the denominator costs at most $(4V/m)(2\cdot100R)$ after scaling. Uniformly in $m$, $R^3\eta<10^{-13}$. To see this and to evaluate the bounds below, for $0\le a\le5$ and $m\ge m_0\ge10^{100}$ the function $\epsilon R^a$ is nonincreasing at fixed $r$. Both $m^{-1/2}$ and $m^{-1/2}(\log m)^{a/2}$ decrease on this range.

In the [comparison of boundary masses](tilted-peak.md#relative-normalization-at-the-boundary), use this $V$ and $\eta$. In its equation (3) the change-of-time term $2V/m$ is at most $\epsilon R^3$, and the relative error is at most $10\epsilon(R^3+|\xi|)$. The discarded endpoint tail is bounded by $4e^{-R^4/100+16R^2}<\epsilon$. Discarding the bad clock event costs less than $\epsilon^2 I_h(0)$ by the same Cauchy–Schwarz and exponential moment bounds, since $e^{-400R^2}<\epsilon^2 e^{-16R^2}$. These inequalities hold even as $m$ tends to infinity because $R^2\ge\log m$. Thus for $D(0)=\mathbb E[{\bf1}_{\rm survival}e^{-hK/s}]$,
$$|D(0)/(\epsilon I_h(0))-1|\le3R^3\eta.$$
In units of $\epsilon I_h(0)$ the mass off the common survival event is at most $6R^3\eta$, the error on that event is at most $2(2R^3+|\xi|)\eta$, and renormalization costs at most $4R^3\eta$. Adding the boundary comparison gives (1).

## Fourier tails for the two signs of tilt

Use the following upper integration limits for the comparison (1).

| Tilt | $T$ |
| --- | --- |
| $-1250\le h<0$ | $10^9$ |
| $0\le r<100$, $h=r^3$ | $10^6\max(10,r)^3$ |
| $100\le r\le r_*$, $h=r^3$ | $10^4 r^2$ |

In each case, the integral over $|\xi|>T$ of $(1+\xi^2)(|\Phi_{m,h}(\xi)|+|\phi_h(\xi)|)$ is less than $.01$, with the discrete characteristic function set to zero outside $[-\pi s,\pi s]$.

* At $h<0$ use the independent-step tilt of [the paired-label estimate](tilted-peak.md#high-frequencies-under-either-sign-of-tilt). The drift at every step is nonnegative, so the full survival probability is at least the fair one, $1/(2\sqrt m)$. On the first $\lfloor m/2\rfloor$ steps the drift is at most $|h|/(2\sqrt m)$, and the [homogeneous survival bound](first-passage.md#tilt-and-prefix-variance) gives prefix survival at most $(|h|+2)/\sqrt m$. Multiplying the resulting survival ratio by the oscillatory suffix bound gives $6(|h|+2)e^{-|\xi|^{2/3}/4000}$. The same bound holds in the continuum by taking the walk length to infinity at fixed $h$, using the tilted weak convergence. In the tail extract $e^{-125}$ and integrate the remaining $(1+\xi^2)e^{-|\xi|^{2/3}/8000}$.
* For $0\le r<100$, $D(0)\ge\epsilon I_h(0)/2$ and $I_h(0)\ge\exp(-16\max(1,r)^2)$. The [fair oscillatory suffix bound with positive weights](tilted-peak.md#strict-increase-in-corank-under-a-larger-positive-tilt) bounds both characteristic functions by $16\exp(16\max(1,r)^2-|\xi|^{2/3}/150)$. Above $T$ this is at most $\exp(-|\xi|^{2/3}/300)$. Integrate as in the first case.
* For $r\ge100$ set $\beta=h/s$, $H=\sqrt m/r$, $N=n/H^2\ge.49r^2$ and $y=\xi/r^3$. Here $H>10^{20}$ and $N\ge4900$. The [shorter-block estimates](linear-potential.md#a-shorter-block-for-intermediate-frequencies) give the following three envelopes for each transform, with the lattice normalizer bounded below by (5) there at zero and the continuum obtained by taking word length to infinity at fixed $h$.
$$2e^{20}\begin{cases}
e^{-3.9\cdot10^{-6}\xi^2/r^4},& |y|\le200,\\
e^{-.7r^2}, &200\le|y|\le10^4,\\
e^{-|\xi|^{2/3}/170},& |y|\ge10^4 .
\end{cases}$$
In the first range $T\le200r^3$ and half the exponent at $T$ has magnitude $195$. Extract $e^{-195}$ and integrate the remaining Gaussian with weight $1+\xi^2$, whose integral is below $10^{10}r^6$. The middle range costs at most $16\cdot10^{12}r^9 e^{20-.7r^2}$ for the two tails of both transforms. In the last range use $|\xi|\ge10^{10}$ and extract half the exponent. These bounds give the claimed errors at $100\le r\le r_*$. All stretched-exponential integrals here use $\int_0^\infty t^j e^{-t^{2/3}/c}dt=(3/2)c^{3(j+1)/2}\Gamma(3(j+1)/2)$.

## Lattice differences at the tilted mode

Let $\Delta$ be the forward difference and $\delta^2$ the centered second difference. Inverting on $[-T,T]$ bounds the characteristic-function part of the error by
$$A_j=10^7\epsilon R^2(R^3+T)T^{j+1},\qquad j=0,1,2. \tag{2}$$
This compares $sP_{m,h}$, $s^2\Delta P_{m,h}$ and $s^3\delta^2P_{m,h}$ with $f_h,f_h',f_h''$, respectively, at $x=k/s$. For $j=1,2$ the lattice multipliers differ from $-i\xi,-\xi^2$ by at most $\xi^2/(2s),\xi^4/(12s^2)$. Thus the total error in each comparison is less than $A_j+.011$ since $T\le1.44\cdot10^{16}$ and $s\ge10^{150}$. The same Fourier convention is used for both transforms.

For $m\ge10^{100}$ use the following bounds.

* For $-1250\le h\le-1$, $A_0,A_1<10^{-7}$. For $1\le h=r^3$ with $r\le100$ in the second row of the table, $A_0<10^{-10}$ and $A_1/h<10^{-6}$. Here $T^2/h\le10^{18}$. In both cases $sP_{m,h}(k)>1$ and $|s^2\Delta P_{m,h}(k)|<.02|h|$.
* For $100\le r\le2000$, (2) gives $A_0,A_1<10^{-4}$ using $T\le4\cdot10^{10}$. Thus $sP_{m,h}(k)>r/30$ and $|s^2\Delta P_{m,h}(k)|<r^4/1000$.
* For $2000\le r\le r_*$ use monotonicity of $\epsilon R^a$ at fixed $r$ to evaluate (2) at $m=10^{100}$, where $R=r$. Then $A_0/r\le10^{-39}(r^6+10^4r^5)<.0031$ and $A_1/r^4\le10^{-35}(r^5+10^4r^4)<.000026$. Including the tails again gives $sP_{m,h}(k)>r/30$ and $|s^2\Delta P_{m,h}(k)|<r^4/1000$.

For all these tilts the absolute relative change in tilted probability is less than $|h|/(4s)$. Since $|h|/s<1$, undoing the tilt gives $b_{k+1}>b_k$ for $h\ge1$ and $b_{k+1}<b_k$ for $h\le-1$. If $|h|<1$, strong log-concavity gives $|x-x_*|\le1/12$ for the untilted mode $x_*$ and $g(x)\ge g(x_*)-1/12$ by integrating the monotone slope. Thus $f(x)\ge e^{-1/12}\sqrt{6/\pi}>1$. The [untilted local comparison](peak-rate.md#a-bound-for-the-largest-coefficients-before-global-unimodality-is-known) gives $sP_m(k)>1/8$ and proves strict log-concavity at that site.

For $m\ge10^{164}$ the same inversion works directly with $j=2$. For $r\le2000$ (including negative $h$) use $R=2000$ at $m=10^{164}$ and the uniform bound $T\le10^{12}$ to get $A_2<.001$. For $r\ge2000$ use $R=r$ at that threshold to get $A_2/r\le10^{-63}(r^{10}+10^4 r^9)<.0063$. The resulting errors lie strictly below $12 f_h(x)$ by the lower bounds on the mode height. Since $f_h''(x)\le-12 f_h(x)$, the tilted second difference is strictly negative. The arithmetic-geometric mean inequality yields strict log-concavity, which survives undoing the tilt.

## Joining the signs

At $n\ge10^{100}$ we have
$$\frac{4s}{r_* n^{3/2}}\le\frac{4(2.001)^{3/2}}{1.2\cdot10^6}<9.44\cdot10^{-6}.$$
Consequently the [small-corank theorem](linear-potential.md) extends more than two lattice spacings past the beginning of the mode comparison. Below that theorem's starting corank $n/105$, the [tail theorem](finite-tail.md) gives strict growth and the [paired-step result](paired-steps.md) gives strict log-concavity.

From $4s/r_*$ to $4s$, $h=g'(k/s)$ decreases with $k$. The steps with $h\ge1$ increase, followed by a region of strictly decreasing adjacent ratios where $|h|<1$, then decreasing steps with $h\le-1$. In the middle region strict log-concavity at $k$ compares the steps beginning at $k-1$ and $k$, so no increase can follow a decrease there. At $x$ within $1/s$ of four, $g'(x)<-1$ since $g''\le-12$ and the [untilted mode bound](peak-rate.md#a-bound-for-the-largest-coefficients-before-global-unimodality-is-known) gives $x_*<.75$. The [first-passage theorem](first-passage.md) gives $b_{k-1}>b_k$ and strict log-concavity at $4s\le k\le D/2$. The [lower-half rank inequality](monotonicity.md#1-lower-half-for-all-sizes) gives weak decrease in corank beyond the midpoint, including the central step for odd $D$. This proves unimodality. At $n\ge10^{164}$ the second-difference comparison applies to every intermediate corank, so the same intervals cover every interior upper-half rank with strict log-concavity.

The [endpoint verifier](verify_comparison.py) uses fractions to check the numerical margins in the derivative estimates, block norm, saddle inversion, bounds (2) and interval overlap. The [rank verifier](verify.py) checks actual coefficients independently at small sizes.

~~~sh
python3 -B verify_comparison.py
python3 -B verify.py --max-n 32 --direct-n 12 --upper-curvature
~~~
