# Controlling the maximum height in the area comparison

**Both central staircases have unimodal rank polynomials at every $n\ge10^{30}$.** With the [finite verification](certified-window.md), a counterexample would have to satisfy $2049\le n<10^{30}$. The additional estimate bounds the maximum height under the positive area weight. It reduces the cost of comparing a walk on the crossing-time clock with Brownian motion at a fixed time.

Use the notation of the [two-tilt proof](holder-blocks.md): $m=2n+\delta$, $s=m^{3/2}$, $k=D-j$, $\epsilon=m^{-1/2}$, $h=(\log f)'(k/s)$ in the peak comparison, $r=\max(h,0)^{1/3}$, and $Z_*=\epsilon I_h(0)$. In the positive tilt comparison $H=\sqrt m/r$, $\beta=H^{-3}$ and $N=n/H^2$. In the small-area saddle argument $H$ is instead selected by $k=-np'(\beta)$. We use the two scales in their respective intervals.

## A height estimate for each weighted law

Hryniv and Velenik established a $3/2$ height-tail exponent for area-weighted aperiodic walks above a wall, with height scale proportional to $\beta^{-1/3}$ for a linear potential. Here the simple walk has period two and a free endpoint. We derive explicit bounds for its entire running maximum and for the Brownian comparison on the same normalization. [Hryniv and Velenik, *Universality of critical behaviour in a class of recurrent random walks*](https://arxiv.org/abs/math/0310217)

Suppose $m\ge2\cdot10^{30}$ and $15\le r\le1900$. Put
$$ U=(60\log m)^{2/3},\qquad M=\lceil H U\rceil .$$
The surviving lattice paths that reach $M$ have total weight less than $\epsilon^8 Z_*$ under the fair law weighted by $e^{-hK/s}$. The same bound holds for a Brownian motion started at one, killed at zero and weighted by $e^{-hY_t}$, reaching $M$ by time $t$, whenever $|t/m-1|\le.001$. Here $Y_t=(2t^{3/2})^{-1}\int_0^t(1+B_v)\,dv$.

We first record the common normalization
$$ I_h(0)\ge .09r e^{-a r^2/2} . \tag{1}$$
Take an auxiliary length tending to infinity at fixed $r$, so $H\to\infty$ and $N\to r^2/2$. At real tilt the [spectral gap](two-harmonics.md#analytic-control-on-a-wider-disk) gives $\lambda_2/\lambda\le e^{-1.48/H^2}$. Peeling two boundary blocks gives relative remainder at most $e^{20-1.4N}$ in the real transform when $N\ge100$: use boundary norm product $10/H$, $c>.1/H$, and $-pH^2<2.61$. In particular $F_n(\beta)>.99c e^{np(\beta)}$. Now $|H^2p+a|\le10/H$ and $\sqrt m F_n(\beta)\to I_h(0)$ by the [tilted meander convergence](localized-mode.md#positive-tests-under-the-random-clock). Passing to the limit gives (1). At the actual finite $m$, $\exp(mp/2+ar^2/2)\le e^{5r^2/H}<2$.

For the lattice bound let $d=\lfloor M/2\rfloor$. Separate the last visit to $d$ before the first visit to $M$. For fixed times at the two ends of this segment, of length $L$, the middle kernel is bounded by
$$ e^{-\beta dL/2-(M-d)^2/(2L)}.$$
The first factor bounds the real weights on its edges. The second bounds the probability of an unrestricted walk having at least the required displacement by the fair-sign exponential inequality. The remaining transfer powers have operator norm product at most $e^{(m-L)p/2}$. The terminal vector has norm at most $2H^{3/2}$ by its geometric series. Since $-pH^2<2.61$, $\beta d/2+p/2\ge .22M/H^3$. Minimizing $cu+d'/u$ over positive $u$ shows that the cost of the middle segment relative to $e^{Lp/2}$ is at most $e^{-.30U^{3/2}}$. There are at most $m^2$ time pairs. By (1) the resulting weight in units of $Z_*$ is at most $50m^2 H^{5/2}e^{-.30U^{3/2}}<\epsilon^8$.

For the Brownian bound let $H_t=\sqrt t/r$. The half-line killed kernel with weight $e^{-\int X_v\,dv/(2H_t^3)}$, $X_v=1+B_v$, has norm $e^{-EL}$ over length $L$, where $E=a/(2H_t^2)$. This follows from the [Dirichlet Feynman–Kac operator](small-area.md) by rescaling space by $H_t$. The linear-potential representation also appears in [the Brownian area propagator, §3](https://arxiv.org/abs/1507.03203). Discard paths with $X_t>2m$ and paths with a displacement of magnitude above $M/64$ from the beginning of any unit time interval with integer left endpoint before $t$. Gaussian tails and reflection give unnormalized cost at most $2e^{-m/2}+4(t+1)e^{-M^2/8192}$. Here $M^2/8192>m/10^7$ and $Z_*\ge .09H^{-1}e^{-1.30r^2}$. This cost is below $\epsilon^8Z_*/2$, uniformly in the stated range.

On a remaining path that reaches $M$, take the integer parts $u,v$ of its last time at $M/2$ before the first hit of $M$, and of that first hitting time. The unit displacement bound gives $v>u\ge1$, $X_u\in[.47M,.53M]$, $X_v\ge.96M$, and $X_w\ge.45M$ on $[u,v]$. The middle operator has norm at most
$$ \exp\{- .45 M(v-u)/(2H_t^3)-(.4M)^2/(2(v-u))\}.$$
Indeed restrict its two endpoint coordinates to the displayed separated ranges, dominate it by the Gaussian transition kernel times the weight bound, and use the one-sided Gaussian tail for both row and column integrals. Since $H_t\le1.001H$, the excess potential over $E$ is at least $.21 M/H_t^3$. The last display divided by $e^{-E(v-u)}$ is at most $e^{-.25 U^{3/2}}$. The first unit of time sends the starting point to a density of $L^2$ norm below one. The terminal indicator of $[0,2m]$ has norm $\sqrt{2m}$. Apply the semigroup bound on $[1,u]$ and $[v,t]$, and sum over at most $4m^2$ time pairs. Since $Et=ar^2/2$, (1) gives total relative cost below $200m^3 e^{-.25U^{3/2}}<\epsilon^8/2$. This proves the Brownian assertion.

## The clock error for the retained paths

Keep $X=1.31\max(15,r)^2+5\log m+4$ and $V=2\sqrt{mX}$ at nonnegative tilt, with $t_\pm=m\pm V$. At $r\ge15$ one may use
$$ \eta=3\epsilon+2.4V(M+3)/s
 \le \epsilon\left(3+4.81\,U\sqrt X/r\right) \tag{2}$$
in the [unnormalized positive-test inequality](holder-blocks.md#positive-tests-before-normalization), increasing its additive constant from 3 to 10. For negative tilts or $r<15$ retain the previous $X,V,\eta$.

For the upper comparison discard paths reaching $M$ under the surviving discrete law; for the lower comparison discard paths reaching $M$ under the deterministic Brownian law through $t_+$. The preceding lemma bounds these two weighted errors separately. Write $\tau_m=\sum_i D_i$ for the $m$th crossing time. Outside a set of probability at most $2e^{-X}$, $|\tau_m-m|\le V$. For the upper comparison all Brownian heights needed up to $\tau_m$ then have absolute value at most $M+2$, as they stay within one of the preceding walk height between crossings. For the lower one $\tau_m\le t_+$, so Brownian survival and the continuous height cap give this same bound. The [duration estimate conditional on the walk signs](mode-comparison.md#smaller-clock-error) bounds the probability of $|\sum_i H_i(D_i-1)|>V(M+2)$ together with $\max_i|H_i|\le M+2$ by $2e^{-X}$. Its moment generating function is used at arguments of magnitude at most $V/(2m)<.001$. These exceptional probabilities cost less than $\epsilon^8 Z_*$ each for the surviving positive weights, since $I_h(0)\ge e^{-1.31r^2}$.

On the comparison events, replacing $2K$ by the integrated height through $\tau_m$ costs at most $m+V(M+2)+3\tau_m$. Changing the terminal time costs at most $2V(M+3)$. Changing the area scaling denominator adds at most $(1.51V/m)t_+(M+3)/(2s)$. These three terms, with the first two divided by $2s$, give (2). The original survival inclusions and deterministic endpoint comparison apply. Thus the test exponent is still $u_L=(|h|+L)(\eta+\epsilon)+3\epsilon R^2$, $R=\max(50,-h,r,\sqrt{\log m})$. The sharper height cutoff affects only the clock comparison.

## Comparing the adjacent signs near the peak

Use the [signed kernel inequality](holder-blocks.md#a-kernel-for-the-adjacent-coefficient-sign) with the following cutoffs.

| Tilt range | $T$ |
| --- | --- |
| $h<0$ | $80000$ |
| $h\ge0,\ r\le4$ | $120000$ |
| $4<r<7$ | $600000$ |
| $7\le r<15$ | $10^6$ |
| $15\le r<50$ | $45r^3$ |
| $50\le r<500$ | $500r^2$ |
| $500\le r<1900$ | $170r^2$ |

For the first four rows the $.035|\xi|^{2/3}$ tail estimate there applies. The exponent at the cutoff exceeds $64,85,248,350$ respectively (with equality allowed for 350). At $r\le4$ and $4<r<7$ subtract at most $32$ and $343/2$ respectively using $I_h(0)\ge.7e^{-h/2}$. At $7\le r<15$ subtract at most $1.31\cdot225$. The same explicit gamma integral bounds the tails. In the fifth row use the [two-harmonic block](two-harmonics.md#a-bound-for-arbitrary-retained-paths) at $45\le |y|=|\xi|/r^3\le10^4$. Its relative norm is below $.815$, and at least $3.9N$ blocks fit after peeling boundaries because $N\ge.49r^2\ge110$. It gives a normalized envelope $2e^{20-.7N}$, using the real normalization in the proof of (1). The combined cost is at most $12\cdot10^4r^3(1+1.001\cdot10^4)e^{20-.7\cdot.49r^2}$, decreasing for $r\ge15$. Beyond $10^4$ use the full-block bound: $2n-4\lceil H^2\rceil\ge1.96n$ here, and $(1.96/75-1/80)(10^4)^{2/3}>2.61$. The last two cutoff rows use exactly the two-tilt tails. In the fifth row the same continuum envelopes follow by sending length to infinity at fixed $r$. These costs, including the low-frequency multiplier error, are below $.01 f_h(x)$ for each inversion as before.

For $|h|\ge1$ the kernel loss now satisfies
$$\sinh(u_{3T})\big(2.81+4.06\cdot1.001T/|h|\big)<.76. \tag{3}$$
Here are details on the uniformity in size. At fixed $r$, each product of $\epsilon$ with the logarithmic factors in (2) decreases for $m\ge2\cdot10^{30}$, since the total power of $\log m$ is at most $7/6$. Evaluate $\log(2\cdot10^{30})<70$ in the resulting endpoint bounds. At that endpoint (2) is below $2150\epsilon$ for $r\ge15$ and $1530\epsilon$ for $r\ge50$. In the last cutoff row its upper bound for $u_{3T}$ and that bound divided by $r$ are increasing after using $1530\epsilon$. In the other positive rows take the upper endpoint for $u_{3T}$ and the maximum of $T/h$ in the row. At negative tilt use $X/|h|\le2(1+1250/4+354)$ and $R^2/|h|\le2500$. In all cases $u_{3T}<.02$ at $|h|\ge1$ and $u_0<.02$ also through $|h|<1$. The mass of the unnormalized measure lies between $.7$ and $1.4$, as needed for the tails. The increased additive test error costs at most $60\epsilon^8T(1+1.001T)$ after scaling, which is below $.001$. Thus (3) gives the required strict signs at $|h|\ge1$. The [untilted estimate](peak-rate.md#unimodality-between-large-coefficients) applies at $|h|<1$ because $m\ge10^{30}$.

## The small-area estimates at the new size

Keep $x_0=(a/3+.004)/1900$. We verify growth at $9n\le k\le x_0s+2$ for $n\ge10^{30}$. At the saddle $H>4$. In the following table each row includes its lower endpoint. The last line uses the saddle slope and the common ground energy as in the [join at $x_0$](holder-blocks.md#the-join-in-corank). The other lower bounds on $N$ follow from $n\ge10^{30}$ alone.

| Range of $H$ | Lower bound on $N$ | Estimate |
| --- | ---: | --- |
| $4\le H<2\cdot10^4$ | $2.5\cdot10^{21}$ | [Flat-pair inversion](flat-pairs.md#inversion-with-a-uniform-number-of-blocks) |
| $2\cdot10^4\le H<2\cdot10^6$ | $2.5\cdot10^{17}$ | Cubic bound $4600H^7$ |
| $2\cdot10^6\le H<2\cdot10^7$ | $2.5\cdot10^{15}$ | Cubic bound $210H^7$ |
| $2\cdot10^7\le H<3\cdot10^9$ | $10^{11}$ | [Second saddle range](holder-blocks.md#signed-inversion-at-the-small-area-saddle) |
| $3\cdot10^9\le H<2\cdot10^{11}$ | $2.5\cdot10^7$ | Energy comparison through $\lvert y\rvert=.04$ |
| $H\ge2\cdot10^{11}$ | $1.7\cdot10^6$ | Energy comparison through $\lvert y\rvert=.08$ |

Here are the changes in the second and third rows. Both use $.0084<p''/H^4<116$ from the flat-pair proof. For $H\ge2\cdot10^4$ the two-tilt block estimate holds with relative norm $.926$ at $4.5\le|y|\le45$, because $20/H\le.001$ in its real energy comparison. The twelfth harmonic satisfies the spacing condition on this interval. The multiplier argument gives Fourier loss at least $.003 N y^2$ for $|y|\le.2$ and at least $.00008N$ for $.2\le|y|\le45$. From 45 to $10^4$ the earlier two-harmonic block gives loss $.7N$, since its spacing condition is $2\lfloor H^2/4\rfloor|\theta|\le\pi$. Above $10^4$ the full-block estimate applies. These estimates have the same $e^{20}$ prefactor.

Use the [flat contour](flat-pairs.md#estimates-down-to-height-scale-four) for the first cubic bound. For the second use the wider contour and semidisk argument from [the two-tilt proof](holder-blocks.md#signed-inversion-at-the-small-area-saddle): at $H\ge10^6$ its energy error on $|w|\le.04$ is at most $2(12/H)^{.68}$. On $|w|\le.01$ this gives $|p'''|/H^7<210$. The nodal cut after $1.5H$ and all contour and gap inequalities used for this conclusion hold already at $H=10^6$ and above.

In the two rows let $(C,y_0)$ be $(4600,1.5\cdot10^{-6})$ and $(210,2\cdot10^{-5})$ respectively. The flat contour also bounds the complementary term of a normalized $j$-pair transform at $|y|\le2\cdot10^{-5}$ by $e^{20-.39j/H^2}$ for $j\ge100H^2$. In its form comparison $K_\beta^2+3|y|(I-K_\beta)$, the polynomial on the lower spectrum is below $\lambda^2-.95/H^2$, using the gap $.60/H^2$, and the top overlap of a unit vector in the complementary space is below $.0003$ by the contour displacement. Thus peeling the boundary blocks gives this bound. For the shorter centered transform $S$ of $b_0=\lceil400H^2\rceil$ pairs, $|S(\pm.04)|<e^{54}$: the shifted real curvature is below $123H^4$, and the boundary prefactor is below $204e^{5.5}$ by the same two blocks, using $c>.05/H$. The centered quadratic exponent costs at most $123\cdot401(.04)^2/2$. Hence $|S(iy)-1|<.001+1600|y|$ by the two-sided real exponential moments, and $|S(iy)|\le1.001$.

In equation (2) of the [signed inversion](holder-blocks.md#signed-inversion-at-the-small-area-saddle) take the core $|x|\le3$, where $x=\sigma\theta$, $d=\beta\sigma\ge\sqrt{.0084N}$. Its cubic error is at most $27C/(6\cdot.0084d)$. The real principal integrand exceeds $.92e^{-x^2/2}$. For $3<|x|$ and $|y|\le y_0$ the modulus is at most $1.002e^{-.35x^2}$, costing less than $.50$ with weight $1+x^2$. From $y_0$ through $10^4$ the weighted integral is at most $2(1+10^4\sqrt{116N})^3 e^{20-.003Ny_0^2}<.001$. The complementary and far tails cost less than $.01$ by their exponential bounds. As in the earlier inversion the two signed integrals exceed $.5$ and the absolute first moment integral is below ten. This proves growth and strict log-concavity at the saddle.

For the last two rows use the wider contour. At $H\ge10^9$ the energy error on the disk of radius $.04$ is less than $.0000083$. Hence $.35<p''/H^4<.60$, and the third derivative is bounded by $4H^7$ through $|w|\le.015$. For $|y|\le.015$, Taylor's inequality gives $H^2\Re P(iy)\le-.12y^2$ for the centered log eigenvalue $P$. Through $.04$ use the complex energy comparison and $\Re(1+iy)^{2/3}\ge1+.109y^2$: at $|y|\ge.015$ the loss from the energy error plus $12/H$ is less than $(1.65\cdot.109-.12)y^2$. Use the short-transform estimate $|S(iy)-1|<.001+160|y|$, valid since the shifted height stays above $10^9$ and $p''<.60H^4$ there. On $|x|\le3$ the cubic error is at most $4\cdot27/(6\cdot.35d)$, and the real principal integrand exceeds $.8e^{-x^2/2}$. Beyond three use $1.002e^{-.48x^2}$ through $|y|=.01$, then $1.002e^{-.199x^2}$ until $.04$. The block loss above $.04$ through $.2$ is at least $.0034 N y^2$, so its weighted Gaussian tail and the higher frequencies cost less than $.01$ by the same integration as before. This proves the fifth row.

At $H\ge10^{11}$ the energy errors on radii $.04,.065,.08$ are bounded by $2(12/H)^\gamma$ with $\gamma=.68,.50,.40$ respectively. The middle exponent follows from $.065/.16<\tan(\pi/8)$. The inner error gives $|p'''|<H^7$ through $.01\beta$ from the real tilt. For $.01\le |y|\le.04$, $.04\le |y|\le.065$, and $.065\le |y|\le.08$ respectively, each error plus $12/H$ costs less than $(1.65\cdot.109-.12)y^2$. Thus all local slope, curvature and damping bounds used in the [first saddle range](holder-blocks.md#signed-inversion-at-the-small-area-saddle) hold at $H\ge2\cdot10^{11}$, including the slightly shifted real tilts. This gives the last row, since $-p'(\beta)/H>2a/3-.001$ implies $N>1700000$ at $k\le x_0s+2$.

The [linear tail estimate](finite-tail.md) covers $k<9n$. On $x_0s\le k\le4s$ the limiting mode estimate gives $r<1900$, so the signed comparison above applies. As $k$ increases, the limiting slope moves from positive to negative, with negative centered second differences in the intervening $|h|<1$ interval. The first-passage estimate and lower-half rank inequalities finish the other end of the row, exactly as in the [two-tilt join](holder-blocks.md#the-size-threshold). This proves the stated size bound.

Run the rational checks for both arguments from the checkout.

~~~sh
python3 -B verify_holder.py
python3 -B verify_tilted_height.py
~~~
