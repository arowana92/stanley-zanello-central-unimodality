# Unimodality of both staircases for $n\ge5\cdot10^{18}$

For the odd- and even-part staircases in Conjecture 3.4, **every rank sequence with $n\ge 5\cdot10^{18}$ is unimodal**. Write $m=2n$ or $2n+1$, $s=m^{3/2}$ and $b_k=a_{D-k}$. The proof controls changes in individual integer coefficients. Together with the [finite certificate](certified-window.md), it leaves $2049\le n<5\cdot10^{18}$ open.

The comparison distribution has density $f$ for half the unit Brownian meander area, with $g=\log f$ and $g''\le-12$. At $x=k/s$ put $h=g'(x)$, so the tilted density $f_h\propto e^{-hx}f$ has its maximum there. The lattice measure $\mu$ is the unconditioned surviving walk measure, weighted by $e^{-hK/s}$ and divided by $Z_*=m^{-1/2} I_h(0)$, the Brownian boundary normalization. We use $\epsilon=m^{-1/2}$. The [rational verifier](verify_variation.py) checks the constants below.

## Testing displacements by total variation

For a bounded nonnegative function $v$ on the line let $v^{+d}(y)$ and $v^{-d}(y)$ denote its supremum and infimum on $[y-d,y+d]$. The [clock and survival comparison](localized-mode.md#positive-tests-under-the-random-clock) gives
$$
 e^{-u}\int v^{-d} f_h-E\|v\|_\infty\le\int v\,d\mu
 \le e^u\int v^{+d} f_h+E\|v\|_\infty. \tag{1}
$$
Here $d=\eta+\epsilon$ bounds the random-clock and starting-height displacements together, $u=|h|d+3\epsilon R^2$, $R=\max(50,|\min(h,0)|,(\max(h,0))^{1/3},\sqrt{\log m})$. The choices below give $E\le100e^{-38}$. To obtain (1), use discrete survival inside continuous survival at the earlier deterministic time for the upper bound, and continuous survival at the later time inside discrete survival for the lower bound. On the retained events the arguments of $v$ differ by at most $\eta$, and the radial endpoint comparison adds at most $\epsilon$. Taking the two extrema of $v$ makes these inequalities pointwise. Only the change of the positive weights contributes to $u$.

If $v$ is absolutely continuous with integrable derivative, then
$$ \int (v^{+d}-v)\le d\|v'\|_1,\qquad \int(v-v^{-d})\le d\|v'\|_1. \tag{2}$$
Indeed the increase from $y$ to any point on its right is at most the integral of $(v')_+$ over $[y,y+d]$. For a point on its left use $(v')_-$ on $[y-d,y]$. Add both bounds and integrate in $y$. Applying the same reasoning to $-v$ proves the other inequality.

Take the even Fourier multiplier $w$ equal to one through $|t|=1$, equal to $3-2|t|$ from there to $1.5$, and zero afterwards. Let $K$ be its inverse Fourier transform with the $1/(2\pi)$ convention. For $j=0,1,2$ we have respectively
$$ \|K^{(j)}\|_1 < 1.76,\ 1.63,\ 1.69. $$
For $G=K^{(j)}$ use Cauchy–Schwarz with $(a^2+z^2)^{-1/2}$ and minimize over $a>0$. The squared bound is $2\pi\|G\|_2\|zG\|_2=\|t^jw\|_2\|(t^jw)'\|_2$ by Plancherel. The two squared norms on the right are integrals of piecewise polynomials. Also $\|K\|_\infty,\|K'\|_\infty<1$ by the Fourier integral.

For $h\ne0$ define $A=1/[s(1-e^{-h/s})]$, $J=K+ATK'$, where $T$ is the bandwidth. The [signed adjacent functional](holder-blocks.md#a-kernel-for-the-adjacent-coefficient-sign) is positive precisely when $b_{k+1}-b_k$ has the sign of $h$. Its continuum counterpart at $x$ equals $f_h(x)$ since $f_h'(x)=0$. Write $B=T\int J(T(x-y)) f_h(y)\,dy$. Applying (1) to the positive and negative parts separately, using (2) for each part and $f_h\le f_h(x)$, gives
$$
 T\int J(T(x-y))\,d\mu(y)
 \ge \cosh(u) B- f_h(x)\left[
 \sinh(u)(1.76+1.63|A|T)+ e^u dT(1.63+1.69|A|T)
 \right]-2ET(1+|A|T). \tag{3}
$$
The variation norms of the two parts add to the variation norm of the signed function. In particular the bracket uses one displacement $d$ and no derivative of the weights. The bounds on the bracket and on the truncated Fourier integrals are given below.

## Normalization at all positive tilts and location of the tilted mode

Write $h=r^3>0$ and let $a$ be the lowest Dirichlet eigenvalue of $-\partial_x^2+x$ on the half-line, $1.65\le a<2.60$. For every $r>0$,
$$ I_h(0)\ge\frac{r}{2} e^{-a r^2/2}. \tag{4}$$
Indeed let $F$ be the positive $L^2$-unit ground state. Integration of $((x-a)F^2-(F')^2)'=F^2$ shows $F'(0)=1$. Its energy gives $\|F\|_\infty^2\le2\|F'\|_2\le 2\sqrt a<4$. For Brownian motion started at $z>0$, killed at zero, the positive area-weighted semigroup has generator $\tfrac12(\partial_z^2-hz)$. It maps the terminal function $F(rz)$ to $e^{-a r^2/2} F(rz)$ in one unit of time. Dominate $F(rz)/2$ by the constant terminal function one, divide the resulting lower bound by $z$, and let $z\downarrow0$. The left side converges to $I_h(0)$ by the [radial boundary normalization](tilted-peak.md#relative-normalization-at-the-boundary). This proves (4).

For $r\ge7$ we also have
$$ f_h(x)>.21r^2,\qquad |x-a/(3r)|<2.7/r^2 \quad\text{at its mode}. \tag{5}$$
Use the [real amplitude comparison](airy-powers.md#real-boundary-amplitude) in the auxiliary-length limit at fixed $r$. As in the [tilted concentration proof](power-overlap.md#positive-tilts-needed-after-the-transfer-power-interval), the lattice saddle center $-np'(\beta)/s$ tends to $a/(3r)$ for $\beta=r^3/s$. At the real shifts $\beta(1\pm1/r)$ the principal amplitude ratio is at most $(1.01/.99)(8/7)^{1/3}$. The ratio of actual to principal mass is within $.001$ of one at all three tilts, since $N=nr^2/m\ge.49r^2$ eventually and the shifted $N'\ge N(6/7)^{2/3}$. Use the real error $20000e^{-1.48(N'-2.01)}$ in those units. On the shifted segment the [grid variance estimate](airy-grid.md) gives $p''<.60(6/7)^{-4/3} H^4<.76H^4$ for $H=\beta^{-1/3}$. Centering the exponent therefore costs at most $.38N/r^2\le .19$. Each exponential moment at $\pm r^2$ about the indicated center in the auxiliary-length limit is below $1.4$. Truncation and weak convergence give $\mathbb E\cosh Z\le1.4$ for $Z=r^2(Y-a/(3r))$ under $f_h$. Consequently $\Pr(|Z|\ge2)\le.4/(\cosh 2-1)<.146$. The interval of radius $2/r^2$ has average density above $.21r^2$. If the mode were at distance at least $2.7/r^2$, the next $.7/r^2$ on that side would have at least this average density by monotonicity, contradicting the tail bound. This gives (5).

## A uniform interval in corank

For **every $n\ge10^{17}$**, both families satisfy $b_{k+1}>b_k$ for every integer $0\le k\le s/70$. We give the parameter details since this interval covers some coefficients in the remaining size gap.

First the [finite Jacobi brackets](airy-grid.md#independent-finite-matrix-check-of-the-correction) at $H=100$ give $2.337<a<2.339$ when combined with the analytic grid error. In detail write $v=1-\rho/2$, where $\rho$ is the infinite single-step norm. For the bracket, restrict to the first 1600 vertices for the lower bound and add the cut edge to its two incident diagonal entries for the upper bound. The decoupled tail is bounded by twice the cut-edge weight. The verifier encloses the finite positive matrices by dyadic matrices and bisects using leading principal minors. With the resulting rational bounds for $v$, use
$$ v\le-\log(1-v)\le v/(1-v),\qquad
 \left|2H^2[-\log(1-v)]+3/(2H)-a-a^2/(30H^2)\right|\le2000/H^4.$$
This certifies the stated energy interval using only rational operations and the prior bound $a<2.60$.

For $k<9n$ use the [linear tail theorem](finite-tail.md). From $k\ge9n$ take the saddle $k=-np'(\beta)$, with $H=\beta^{-1/3}>4$, $N=n/H^2$, as in the [transfer-power proof](airy-powers.md#smaller-heights-and-the-uniform-interval). For $4\le H<110$ use its shorter walk of $b=\lceil400H^2\rceil$ pairs, scaled variance $v_2=p''/H^4$, and $d_0^2=(n-b)v_2/H^2$. The following table gives a lower bound $v_*$ for $v_2$, the arc $|y|\le y_0$ on which the principal modulus is at most $e^{-c(d_0y)^2}$ for the remaining $n-b$ pairs, and the rate $C$ giving at least $CNy_0^2$ loss from $y_0$ up to $10^4$.

| Height | $v_*$ | $y_0$ | $c$ | $C$ |
| --- | ---: | ---: | ---: | ---: |
| $[4,8]$ | .0084 | .0003 | .40 | $.023/8^4$ |
| $[8,20]$ | .015 | .0005 | .34 | .000009 |
| $[20,110]$ | .017 | .0005 | .36 | .00004 |

Indeed $v_2\ge 2(1/(4\cdot2.60)-1/(2H^2))^2$ by the [edge variance bound](flat-pairs.md#estimates-down-to-height-scale-four). The even Taylor remainder costs at most $.37 y^4/[.08^4(1-(y/.08)^2)]$ in the scaled log, giving the indicated $c$. The complementary error $e^{20-.4j/H^2}$ still holds through $.0005$. On that arc the projection displacement is below $.006$ and the polynomial norm bound on the lower real spectrum is at most $\lambda^2-.95/H^2$, as in the transfer-power proof. Including the squared top overlap below $.006^2$ leaves a loss of at least $.80/H^2$ in squared norm.

The first row uses flat-pair damping directly. In the second take $l=\lfloor H^2/6\rfloor$ and $80\le |y|\le81$. The unrestricted paired-label bound and the retained-mass inequality give a relative block norm at most
$$ \frac{1+\exp[-(1/6-1/64)^3\,80^2/16]}{2}\,e^{2.72/6}<.99.$$
Indeed $l/H^2\ge1/6-1/64$, $81l/H^3<\pi$. For $0<|y|\le1$ take the integer multiple $\lceil80/|y|\rceil$ in the [multiple-frequency comparison](harmonic-small-area.md#comparing-two-frequencies). At least $5.99N$ blocks remain after the two short end blocks, giving the stated rate. For $1\le|y|\le10^4$ flat pairs give rate $.023 y^2/H^4\ge.023/20^4>C y_0^2$. In the third row the previous block at multiples near 200 gives $.00004 y^2$ up to $.2$ and at least $.0000017$ from there through $10^4$, using flat pairs beyond 200.

In each row apply the shorter-walk integral proof with $d_0^2>v_*(N-401)$. The cubic error now costs less than $.95$ by $1.001\cdot4600/(6v_*d_0c^2)$, and the replacement of the shorter-walk factor by its real mass costs less than $.018$ by $2300/(cd_0)$. The omitted Gaussian tail starts at $y_0d_0>10$. The complementary terms and local adjacent multiplier together cost less than $.01$ as there, using $1.01/(cd_0)$ for the local $|y|$ integral up to the short mass factor $1.001$. The outer cost up to $10^4$ is bounded in every row by $2(1+1.01\cdot10^4)10^4\sqrt{116N}\,e^{20-CNy_0^2}<.001$. Beyond $10^4$ the previous stretched-exponential estimate applies. Subtracting these costs from $\sqrt{2\pi}\cdot.999$ proves the adjacent sign.

For $110\le H<10000$ the [grid saddle theorem](airy-grid.md) applies since $N>100000$. For $H\ge10000$, $k/n>(2a/3-.016)H$. Thus $k\le s/70$ implies $N\ge70^2(2\cdot2.337/3-.016)^2/(2.001)^3>1450$ and the [large-height power theorem](airy-powers.md) applies. This finishes the uniform interval. Put $x_0=1/70$. At $x\ge x_0$ and $h>0$, (5) forces $r<60$ since $2.339/(3\cdot60)+2.7/60^2<1/70$.

## The central interval and bounded negative tilts

For $x_0\le x\le1.5$ put $z=x+c_m/s$, $c_m=(m+\lceil m/2\rceil)/2$. The [centered-clock estimates](centered-clock.md#fourier-inversion-and-the-peak) compare the scaled first and second differences with $f'(z), f''(z)$ to errors $.0054,12.3$ at every $m\ge10^{19}$.

* For $1\le h\le16$, $f'(x)\ge h\sqrt{6/\pi}\,e^{-h/2}$ by the tilted mode bound and Jensen. The minimum on this interval is at 16. Subtracting $3300000/\sqrt m$ for the shift, by the [derivative envelope](airy-overlap.md#the-decreasing-side-in-corank), leaves more than $.0054$.
* For $|h|<1$, $f''(x)\le-11 e^{-1/12}\sqrt{6/\pi}$. The shift changes it by at most $10^9/\sqrt m$, leaving $f''(z)<-12.3$.
* For $1\le q=-h\le8$, $x-x_*\le q/12$, where $x_*\le.65$ and $f(x_*)\ge1.78$. The [Gaussian regression bound](airy-overlap.md#the-decreasing-side-in-corank) and $-g'(z)\ge q$ give
$$ -f'(z)\ge1.78q\exp[-.65q-q^2/24-12(1.501)\epsilon-6\epsilon^2]>.0054.$$
The last expression attains its minimum at an endpoint by log-concavity in $q$. Regression also gives $h\ge-12x\ge-18$ on this entire interval.

Thus strict corank growth, strict centered concavity, and strict corank decrease hold in the respective cases. It remains to test $-18\le h\le-8$ and $16\le h<60^3$.

## Bandwidth and error bounds outside the central interval

For $h\ge16$ put $B=\min(h/2,1.31r^2)$, $X=B+\tfrac12\log m+38$. Jensen and (4) give $I_h(0)>.7e^{-B}$. For $h=-q\le-8$ take $X=2(1+.084 q^2+\tfrac12\log m+38)$. Use $V=2\sqrt{mX}$ and $\eta=9.36\epsilon X$ up to $r=15$, with $r=0$ for negative $h$. From $r=15$ use $\eta=\epsilon(3+4.81U\sqrt X/r)$ with $U=(60\log m)^{2/3}$. These are the [displacement estimates for the two clocks](tilted-height.md#the-clock-error-for-the-retained-paths).

For negative $h$ the square root of the unconditional second weight moment at each deterministic Brownian time is at most $e^{1+.084q^2}$. The area there is Gaussian with variance $1/12$ and mean $1/(2\sqrt{t_\pm})$. On the lattice use $K=D-\sum i X_i$ with independent fair down indicators, and $\mathbb E K\le0$. The product of centered cosh factors gives the same upper bound since $\sum i^2/(4s^2)<.084$. Thus Cauchy–Schwarz costs at most $\sqrt8 e^{1+.084q^2-X/2}/Z_*$ on each exceptional event of probability at most $8e^{-X}$. For positive $h$ its cost is at most $8e^{-X}/Z_*$. Also $I_h(0)>.7$ at negative tilt. At $15\le r\le60$ the inputs to the [height-tail proof](tilted-height.md#a-height-estimate-for-each-weighted-law) hold with $H=\sqrt m/r>10^7$, $U>185$. In particular its excess potentials exceed $.22,.21$, $5r^2/H<.01$ and $H^2U^2/8192>m/10^7>1.3\cdot60^2+10\log m$. Each discarded height error is below $\epsilon^8$ in units $Z_*$. The discarded radial-endpoint error is also below $\epsilon^8$ as in (1)'s clock proof. These estimates, allowing $e^u<1.16$ on retained weights, give the stated $E$.

Use $T=(25/.115)^{3/2}$ for $h\le-8$ and $T=((27+B)/.115)^{3/2}$ for $h\ge16$, $r<7$. The [moderate-tilt envelope](peak-overlap.md#the-signed-comparison-on-the-peak-scale) below $|\xi|=s/1024$ has modulus at most $P e^{B_0-.115|\xi|^{2/3}}$ for either normalized law, with $(P,B_0)=(208,0)$ or $(100,B)$ respectively. Indeed the independent negative-tilt label probabilities are within $[.499,.501]$ and $8(q+8)\le208$. In the positive case use $32/I_h(0)$. The positive-test mass bound obtained below is independent of Fourier inversion. If $w_0=.115T^{2/3}$, the integral above $T$ with weight $1+1.001|\xi/h|$ costs less than $.003$ for both laws together, using $\Gamma(3/2,w_0)\le e^{-w_0}(w_0+1)/\sqrt{w_0}$ and $\Gamma(3,w_0)=e^{-w_0}(w_0^2+2w_0+2)$. The remaining lattice frequencies cost below $.001$ by the full-period rates of the cited proof.

For larger $r$ use the following cutoffs. Here $y=|\xi|/r^3$, $N=nr^2/m\ge.49r^2$ and $H=\sqrt m/r$.

| Range of $r$ | $T/r^3$ |
| --- | ---: |
| $[7,9)$ | 35 |
| $[9,12)$ | 20 |
| $[12,14)$ | 12 |
| $[14,15)$ | 10 |
| $[15,21)$ | 8 |
| $[21,30)$ | 4.5 |
| $[30,42)$ | 3 |
| $[42,54)$ | 2 |
| $[54,60]$ | 1.5 |

To verify their tails use the [binomial Hölder moment](power-overlap.md#tilted-fourier-blocks-at-intermediate-frequencies) for $\lfloor cH^2\rfloor$ pairs. The table gives a relative norm $\le e^{-cC}$ from the indicated $y$ through 150. Every harmonic has the required spacing because $100\cdot150/H<\pi$. The real energy error allowance $.00001$ applies at all the shifted heights.

| $y$ | $c$ | Hölder exponent | $C$ |
| ---: | ---: | ---: | ---: |
| 1.5 | 1 | 50 | .0095 |
| 2 | 1 | 25 | .016 |
| 2.5 | 1 | 16 | .025 |
| 3 | 1 | 12 | .036 |
| 4.5 | 1 | 6 | .075 |
| 6 | .8 | 6 | .12 |
| 8 | .7 | 4 | .20 |
| 10 | .7 | 3 | .28 |
| 12 | .6 | 3 | .37 |
| 15 | .5 | 2 | .50 |
| 20 | .45 | 2 | .72 |
| 25 | .35 | 2 | .92 |
| 30 | .35 | 2 | 1.10 |
| 35 | .3 | 2 | 1.30 |
| 45 | .25 | 2 | 1.60 |

In ground-state units the end blocks of $\lceil H^2\rceil$ pairs cost at most 20000. End blocks of $\lceil9H^2\rceil$ cost less than $1.03$. In fact if the original two boundary norms divided by their respective ground components are $a_1,a_2$, then $a_i\ge1$ and $a_1 a_2\le20000$. Each squared excess $a_i^2-1$ decreases by the factor $e^{-2\cdot1.48\cdot7.999}$, by the real spectral gap. The new squared product is therefore at most $1+(20000 e^{-1.48\cdot7.999})^2$. Real boundary norms dominate the complex ones entrywise. Rounding the lengths and the number of complete blocks gives the envelope
$$ L_C=\min(20000e^{-C(N-4)},\ 1.03e^{-C(N-20)}).$$
For each successive band $[l,v]$ above the cutoff, up to 150, the cost relative to $f_h(x)$ is at most $12r(v-l)(1+1.001v)L_C/.21$ by (5). This accounts for both frequency signs, both laws, the lattice mass and the real ratio to the principal mass. The continuum bound follows by taking the auxiliary-length limit. Summing the bands costs less than $.022$ relative to $f_h(x)$. Each bound decreases from the corresponding row's lower endpoint since $C\cdot.49r^2>1/2$ in each band used.

For $y\ge150$ the two shorter end blocks leave at least $1.82n$ single steps. Up to $|\theta|=|\xi|/s=1/64$ the [retained fair row estimate](airy-grid.md#boundary-factors-in-fourier-inversion) then gives $3\cdot20000 e^{-.10N y^{2/3}}$ in ground units since $(.124\cdot1.82-.10)150^{2/3}>2.61$. Beyond that frequency $y>10^4$, and the full-period estimate gives $2\cdot20000 e^{-N y^{2/3}/80}$. For each tail extract $e^{-28N/20}$ or $e^{-460N/160}$, and integrate the remaining $1+1.001y$ against $e^{-y^{2/3}}$ or $e^{-.14 y^{2/3}}$, respectively. Each integral costs below $.001 f_h(x)$ already at the smallest $N=.49\cdot49$.

At all the listed cutoffs $|A|<1.001/|h|$, $T<500000$ and $T/|h|<500$. The verifier bounds $u<.14$ and the bracket in (3) by $.96$. It checks extrema on rational intervals in the tilt parameter, using the largest bandwidth, displacement and $T/|h|$ in each interval as separate upper bounds. For fixed tilt the terms $\epsilon$ times the logarithmic factors decrease from $m=10^{19}$, since their total logarithmic degree is at most $7/6$. At that endpoint $\log m<44$, $U<192$. The mass test $v=1$ in (1) puts the lattice mass in $(.7,1.4)$. The combined additive test error is below $.001$. Replacing the lattice difference multiplier by the continuum one under the cutoff costs below $.001$ using $4(2T)^3/s$. All tails, including their factor $\cosh(u)<1.01$ on the continuum side, leave a positive signed functional since $f_h(x)>1$. This proves strict growth for the positive tilts and strict decrease for the negative ones.

As $k$ increases, $g'(k/s)$ decreases. The signed intervals and the negative centered differences at $|h|<1$ allow only one change from growth to decline. They meet the small-corank interval at $x_0$ and the [first-passage inequality](rising-window.md) at $x=1.5$. The [lower-half inequality](monotonicity.md#1-lower-half-for-all-sizes) covers the rest of each row. This proves the theorem for both families.

~~~sh
python3 -B verify_variation.py
python3 -B verify_airy_powers.py
python3 -B verify_centered_clock.py
python3 -B verify.py --max-n 64 --direct-n 12 --upper-curvature
~~~
