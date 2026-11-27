# Unimodality for both staircases from $10^{24}$ rows

For the odd-part and even-part central staircases the rank sequence is unimodal at **every $n\ge10^{24}$**. Together with the [finite result](certified-window.md), the unresolved sizes are $2049\le n<10^{24}$. The [Airy grid estimate](airy-grid.md) extends the small-corank sign far enough to limit the positive tilt to $h\le500^3$. On the opposite side of the peak a Gaussian translation gives a lower bound for the Brownian density. It allows the unweighted coefficient estimate to reach the first-passage range.

Use $m=2n$ or $2n+1$, $s=m^{3/2}$, $D=\lfloor m^2/4\rfloor$, and $b_k=a_{D-k}$. Put $f$ for the density of half the area under a standard Brownian meander, $g=\log f$, $x_*$ for its mode, $x=k/s$, $h=g'(x)$ and $r=\max(h,0)^{1/3}$ in the comparison with this density.

## The decreasing side in corank

For every $y>0$ and $v\ge0$,
$$ f(y+v)\ge e^{-12vy-6v^2}f(y). \tag{1}$$
Indeed, start Brownian motion at $d>0$ and let $Y$ be half its unconditioned unit-time area, Gaussian of mean $d/2$ and variance $1/12$. Regressing its height at time $u$ on $Y$ gives coefficient $6(u-u^2/2)\ge0$. The residual path is independent of $Y$. Thus the probability of staying positive conditional on $Y=y$ is nondecreasing in $y$. For the area conditional on survival the density is proportional to this probability times the Gaussian density at $y$. Comparing it at $y+v$ and $y$ gives the bound with $y-d/2$ in the linear term. Integrate over bounded intervals and take $d\downarrow0$ using the [radial construction](peak-rate.md#starting-height-and-meander-law). The limiting density is continuous, so shrinking the intervals yields (1). In particular $g'(y)\ge-12y$ and $f(z)\ge f(x_*)e^{-6(z^2-x_*^2)}$ for $z\ge x_*$.

For **every $m\ge10^{23}$**, if $k/s\le1.5$, $h\le-1$, then $b_{k+1}<b_k$. Use [centered-clock inversion](centered-clock.md#fourier-inversion-and-the-peak) with cutoff 4800. Its uniform error for the scaled first difference at $z=(k+c_m)/s$, $c_m=(m+\lceil m/2\rceil)/2$, is less than $.000005$. Since $z\ge x$, $g'(z)\le-1$. For $z\le1.4$, (1) gives $f(z)\ge\sqrt{6/\pi}e^{-6(1.4)^2}>.000005$. For $1.4<z<1.501$ use $-g'(z)\ge12(1.4-.75)$, since $x_*<.75$ and $g''\le-12$. Multiplying this slope bound by $\sqrt{6/\pi}e^{-6(1.501)^2}$ again exceeds $.000005$. Both bounds use the [limiting mode and curvature estimates](peak-rate.md#a-bound-for-the-largest-coefficients-before-global-unimodality-is-known). The [all-size first-passage inequality](rising-window.md) takes over at $1.5s$ up to the midpoint in rank.

At $m\ge2\cdot10^{24}$ the same first-difference error is below $.0000003$. If $1\le h\le20$, the tilted density $f_h$ at its mode $x$ is at least $\sqrt{6/\pi}$. Thus
$$ f(x)=f_h(x)e^{hx}\mathbb E e^{-hY_0}\ge\sqrt{6/\pi}\, e^{-h/2},$$
where $Y_0$ is half the meander area and has mean below $1/2$. The limiting Fourier envelope bounds $\sup|f''|<3300000$, so $f'(z)\ge f(x)-3300000/\sqrt m>.0000003$. This gives strict corank growth. If $|h|<1$, then $f''(x)\le-11e^{-1/12}\sqrt{6/\pi}<-12.3$. The shift to $z$ costs less than $.001$ by $\sup|f'''|<10^9$, and the centered second-difference error is below $2.3$. Hence the centered second difference is strictly negative.

## Positive tilts between the peak and the saddle

Use the [positive tests for the signed adjacent functional](holder-blocks.md#a-kernel-for-the-adjacent-coefficient-sign), at $20\le h\le500^3$. The Fourier cutoffs are

| Range | $T$ |
| --- | ---: |
| $20\le h<125$ | $((55+h/2)/.115)^{3/2}$ |
| $5\le r<15$ | $((55+1.31r^2)/.115)^{3/2}$ |
| $15\le r<30$ | $45r^3$ |
| $30\le r<50$ | $4.5r^3$ |
| $50\le r<250$ | $250r^2$ |
| $250\le r\le500$ | $150r^2$ |

For the second row we need $I_h(0)\ge.09 r e^{-a r^2/2}$ already at $r\ge5$. In the auxiliary-length limit used in the [real normalization](tilted-height.md#a-height-estimate-for-each-weighted-law), $H=\sqrt m/r\to\infty$ and $N=n/H^2\to r^2/2\ge12.5$. The [real boundary-factor estimate](airy-grid.md#boundary-factors-in-fourier-inversion) gives limiting relative error at most $20000e^{-1.48(12.5-2.01)}<.01$. Taking the limit of $c>.1/H$ and of $H^2p\to-a$ gives the claim. In the first row Jensen gives $I_h(0)\ge.7e^{-h/2}$. The [moderate-tilt Fourier bound](peak-overlap.md#the-signed-comparison-on-the-peak-scale) in both rows has rate $.115|\xi|^{2/3}$ and prefactor at most $100e^b$, with $b=h/2$ or $1.31r^2$. Thus $.115 T^{2/3}-b=55$. The combined tail cost is below $.001$ by the same gamma integral as there. The additional lattice frequencies above $s/1024$ are negligible by the full-period bound. The third row uses the [existing estimate above $45r^3$](tilted-height.md#comparing-the-adjacent-signs-near-the-peak), whose conditions $N\ge.49r^2$ and $H\ge10^7$ hold. In these estimates one can allow a factor $1.4$ in the unnormalized lattice mass, justified below independently of inversion.

For the last three rows write $y=\xi/r^3$, $N=nr^2/m\ge.49r^2$, $H=\sqrt m/r$. Peel the [two longer real boundary factors](airy-grid.md#boundary-factors-in-fourier-inversion). The normalized transform has modulus at most $1.01 e^{-(N-42)B(y)}$ through $|y|=45$ using the bounds there, now with $B=.075$ on the whole interval $4.5\le|y|\le45$. Indeed $12\cdot45/H<\pi$ at the present heights, so the Hölder block applies throughout. There are at least $N-42$ integer blocks of $\lfloor H^2\rfloor$ pairs after the cut, also for $30\le r<50$. Beyond 45 the fair row estimate applies over at least $1.80n$ single steps here. It gives $3e^{-N|y|^{2/3}/80}$ since $(.124\cdot1.80-1/80)45^{2/3}>2.61$ up to $|\theta|=1/64$, $\theta=\xi/s$. Above that frequency $|y|>10^4$ and $(1.80/75-1/80)(10^4)^{2/3}>2.61$. The continuum inherits the envelopes by sending the length to infinity at each fixed $r$.

In the fourth row the remaining cost up to $|y|=45$ is bounded by $12\cdot45 r^3(1+1.001\cdot45)e^{-.075(.49r^2-42)}<.001$. This decreases from $r=30$. The full tail beyond 45 also costs less than $.001$ by substituting $\xi=r^3y$ and extracting $e^{-.49r^2 45^{2/3}/160}$. The same estimates cover these bands in the last two rows. For frequencies below $4.5r^3$ use $v=|\xi|/r^2$ and weight $1+1.001v/r$. In the fifth row integrate $e^{-.00093(.49-42/50^2)v^2}$ from 250. In the last row use $.00249$ in place of $.00093$ from 150 up to $v=r$, and $.00093$ from $v=r\ge250$ to $4.5r$, with $.49-42/250^2$ as the second factor. Tails that start above the upper endpoint are empty. Each integral costs less than $.001$, including the frequency scale $r^2$, the two signs and both laws. These bounds put both inversion errors below $.01f_h(x)$ as in the [signed comparison](peak-overlap.md#the-signed-comparison-on-the-peak-scale).

For the comparison of clocks use $\epsilon=m^{-1/2}$ and $U=(60\log m)^{2/3}>220$. In the [maximum-height proof](tilted-height.md#a-height-estimate-for-each-weighted-law) the two excess-potential bounds $.22$ and $.21$ hold with $U=220$ as lower bound and $H>10^9$. Also $H^2U^2/8192>m/10^7$, $5r^2/H<.01$, and $m/10^7>1.30(500)^2+10\log m$, sufficient for the discarded Gaussian cost. Thus both maximum-height tails are below $\epsilon^8Z_*$ with the original choice of cut. As before the products of $\epsilon$ with the logarithmic factors decrease at these sizes. At $m=2\cdot10^{24}$, $\log m<56$, $U<225$. In the test exponent $u_L=(h+L)(\eta+\epsilon)+3\epsilon\max(50,r,\sqrt{\log m})^2$ use the endpoint bounds $\eta/\epsilon\le5500$ for $r<15$, $1740$ for $15\le r<50$, $1300$ for $50\le r<250$, and $1250$ thereafter. These follow by substituting in [the height and clock bounds](tilted-height.md#the-clock-error-for-the-retained-paths).

The [rational checks](verify_airy_overlap.py) give $u_{3T}<.22$ and
$$ \sinh(u_{3T})(2.81+4.06\cdot1.001 T/h)<.88.$$
For the variable small-tilt cutoffs $T$ increases within each row, and $T^2/h$ is largest at an endpoint. This follows by differentiating $(55+h/2)^3/h$ in the first row, and by writing the corresponding expression in the second as a constant times $(55/r+1.31r)^3$. Expand $(h+3T)(2.81+4.06\cdot1.001T/h)$ before using these bounds. For $T$ proportional to $r^2$ both $u$ and its endpoint bound divided by $r$ increase with $r$ after substituting the constant bound for $\eta/\epsilon$, since $r\ge50$. The mass test at $L=0$ gives lattice mass between $.7$ and $1.4$. The additive test and lattice multiplier errors cost less than $.001$ each because $T<4\cdot10^7$. Therefore the [signed integral lower bound](holder-blocks.md#a-kernel-for-the-adjacent-coefficient-sign) is positive and $b_{k+1}>b_k$ throughout these positive-tilt ranges.

## Joining the integer coranks

Take $x_0=(a/3+.014)/500$. For $x\ge x_0$ the [continuous concentration lemma](tilt-concentration.md#width-of-the-continuous-tilted-law) forces $r<500$ whenever $h>0$. Otherwise the tilted mode would have $x<a/(3r)+7/r^2\le x_0$. Thus the preceding signs cover $x_0s\le k\le 1.5s$.

On the other side, growth through $9n$ follows from the [linear tail](finite-tail.md). For $9n\le k\le x_0s+2$, select the saddle $k=-np'(\beta)$, which has $H>4$. For $4<H<20$ one has $N=n/H^2\ge2.5\cdot10^{21}$ so the [flat-pair proof](flat-pairs.md#inversion-with-a-uniform-number-of-blocks) gives growth. For $20\le H<110$ one has $N>2.5\cdot10^{19}$. Use the [shorter-walk inversion with cubic bound 4600](peak-overlap.md#the-small-corank-saddle). Its low-frequency loss $.00004Ny^2$ through $.2$ and $.0000017 N$ through 200 follows from the $\lfloor H^2/10\rfloor$ block and multiples in $[200,400]$ since $H\ge20$. From 200 to $10^4$ the [flat-pair norm](flat-pairs.md#inversion-with-a-uniform-number-of-blocks) loses at least $.023 Ny^2/H^4>.0000017 N$. The boundary costs used for $S(\pm.04)$ in that inversion still hold here. Indeed $\lceil(H')^2\rceil/(H')^2\le1+1/19^2$ at the shifted height, so the relative prefactor is below $204 e^{5.5}$ using $c>.05/H$ and $-p(\beta')(H')^2<2.72$. The flat contour and its complementary bound hold for $H\ge4$. The rest of that inversion uses only $N$.

At $H\ge110$, (1) of [the Airy grid proof](airy-grid.md) gives $k/n>(2a/3-.016)H$. As $x_0s+2\le (a/3+.015)s/500$ and $m/n<2.001$, this yields
$$ N\ge\frac{500^2(2a/3-.016)^2}{(2.001)^3(a/3+.015)^2}>100000.$$
The minimum of the right side occurs at the smallest allowed $a=1.65$. The growth theorem in that proof now gives the last overlap.

As $k$ increases, $h=g'(k/s)$ decreases. There is strict growth for the positive-slope part with $h\ge1$, negative centered second differences for $|h|<1$, and strict decrease at $h\le-1$ through the first-passage range. Thus the forward differences can change from positive to negative only once. The [lower-half inequality](monotonicity.md#1-lower-half-for-all-sizes) finishes the row. This proves the stated global result for both parities.

~~~sh
python3 -B verify_airy_grid.py
python3 -B verify_airy_overlap.py
python3 -B verify_centered_clock.py
python3 -B verify_peak_overlap.py
~~~
