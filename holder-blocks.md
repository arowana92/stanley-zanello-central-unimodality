# Comparing two real tilts in a Fourier block

For the odd-part and even-part central staircases, **the rank sequence is unimodal for every $n\ge10^{36}$**. Write $m=2n+\delta$, $s=m^{3/2}$, $D=\lfloor m^2/4\rfloor$ and $k=D-j$. The proof joins a small-area saddle estimate to a comparison at the mode of a tilted Brownian meander area law. Both estimates concern individual adjacent integer coefficients.

## A block inequality

Use the [symmetric two-step transfer](effective-small-area.md#real-transfer-operator) $K_z$, $\beta=H^{-3}$, $p(\beta)=\log\|K_\beta\|$ and $N=n/H^2$. In a block of $2l$ fair steps let $\rho_d$ bound the norm of the matrix of entrywise moduli of the unrestricted endpoint transforms at frequency $d\theta$. Take $\rho_0=1$. Writing $M$ for the matrix of entrywise moduli of $K_{\beta+i\theta}^{\,l}$, we have, for $b=6/5$,
$$
 \|M\|\le \exp\{lp(b\beta)/b\}
 \left(2^{-24}\sum_{d=-12}^{12}\binom{24}{12+d}\rho_{|d|}\right)^{1/6}. \tag{1}
$$
Test the nonnegative symmetric matrix on a nonnegative unit vector $v$. Give each unrestricted path from $i$ to $j$ mass $4^{-l}v_i v_j$, extending $v$ by zero to negative heights. This has total mass at most one. Subtract the phase of the corresponding retained endpoint transform from the path phase to obtain $u$. If $W$ is the surviving real weight, zero on killed paths, the quadratic form is $\int W\cos u$. Hölder bounds it above by $(\int W^b)^{1/b}(\int(\cos u)_+^6)^{1/6}$. The first integral is the real quadratic form at $b\beta$. For the second, $(\cos u)_+^6\le\cos^{24}(u/2)$ since $(1+t)^2/4\ge t$ for $0\le t\le1$. Expanding the even power gives (1), as each endpoint rotation preserves the modulus of its harmonic. This uses the real weight of each retained path.

Put $y=\theta/\beta$, $H\ge10^7$, $l=\lfloor H^2\rfloor$. The [unrestricted pair bound](linear-potential.md#a-shorter-block-for-intermediate-frequencies) gives $\rho_d\le e^{-d^2 l^3\theta^2/16}$ through $|y|\le10^4$, since $12l|\theta|\le\pi$. Symmetry and the uniform row estimate give the required operator bound. The [real energy error](linear-potential.md#approximation-of-the-real-ground-energy) gives
$$ H^2\big(p(b\beta)/b-p(\beta)\big)\le a(1-b^{-1/3})+20/H,$$
where $1.65\le a<2.60$ is the Dirichlet ground energy of $-\partial_x^2+x$. In (1) take $z=.999^3(4.5)^2/16$ and $\rho_d\le e^{-d^2z}$ for $4.5\le|y|\le10^4$. The right side divided by $e^{lp(\beta)}$ is less than $.924$. Below $4.5$ the [integer-multiple inequality](harmonic-small-area.md#comparing-two-frequencies) with multiplier $\lceil4.5/|y|\rceil$ gives a relative norm at most $1-.076 y^2/(4.5+|y|)^2$.

For $F_n(z)=2^{-m}\sum_k a_{D-k}e^{-zk}$ use the principal amplitude $c=c(\beta)>.1/H$ and $\Psi=F_n(\beta+i\theta)/(ce^{np(\beta)})$. After peeling the two boundary blocks of $\lceil H^2\rceil$ pairs there are at least $.996N$ whole blocks for $N\ge1000$. The [boundary norm product](harmonic-small-area.md#real-and-complex-estimates-near-the-saddle) is at most $10/H$. Consequently $|\Psi|\le e^{20-N B(y)}$ on the lattice period with the following choices:

| Range of $\lvert y\rvert$ | $B(y)$ |
| --- | --- |
| $0\le \lvert y\rvert\le.2$ | $.0034 y^2$ |
| $.2\le \lvert y\rvert\le1$ | $.00249 y^2$ |
| $1\le \lvert y\rvert\le4.5$ | $.00093 y^2$ |
| $4.5\le \lvert y\rvert\le10^4$ | $.075$ |
| $10^4\le \lvert y\rvert$ | $\lvert y\rvert^{2/3}/80$ |

The last line is the [full-block estimate](flat-pairs.md#inversion-with-a-uniform-number-of-blocks) using $2n-4\lceil H^2\rceil\ge1.99n$ at these heights and sizes.

## Signed inversion at the small-area saddle

At any integer $k=-np'(\beta)$ the coefficients grow strictly in corank from $k$ to $k+1$, and are strictly log-concave at $k$, in either of these ranges:

| $H$ | Sufficient $N$ |
| --- | ---: |
| $H\ge2\cdot10^{12}$ | $1{,}700{,}000$ |
| $H\ge2\cdot10^7$ | $10^{11}$ |

Put $d=\beta\sqrt{np''(\beta)}$, $\sigma=d/\beta$ and $x=\sigma\theta=dy$. In the first range the [spectral estimates](two-harmonics.md#analytic-control-on-a-wider-disk) give $.35N<d^2<.60N$, $|p'''|<H^7$ on $|z/\beta-1|\le.01$, and $H^2\Re(p(z)-p(\beta))\le-.12 y^2$ through $|y|\le.08$ on $z=\beta(1+iy)$.

Use $b_0=\lceil400H^2\rceil$ pairs and the same terminal parity. The centered shorter transform $S(w)=F_{b_0}(\beta(1+w))e^{-b_0\beta p'(\beta)w}/(ce^{b_0p(\beta)})$ satisfies $|S(0)-1|<.001$, $|S(iy)|\le1.001$ and $|S(iy)-1|<.001+160|y|$ by the [short-walk moment estimate](two-harmonics.md#signed-inversion-after-twenty-million-blocks-on-the-height-scale). Write $J=e^{ik\theta}\Psi$ and $P(w)=p(\beta(1+w))-p(\beta)-\beta p'(\beta)w$. On $|y|\le.08$ its principal term is exactly
$$ (S(iy)-E_{b_0}(iy))\exp((n-b_0)P(iy)), \tag{2} $$
where the complementary term satisfies $|E_j|\le e^{20-.16j/H^2}$ for $j=b_0,n$. This keeps the short-walk factor inside the inversion integral.

For $|x|\le3$, the exponent in (2) differs from $-(1-b_0/n)x^2/2$ by at most $27/(6\cdot.35d)<.017$. Its real contribution is greater than $.35e^{-x^2/2}$, using $d>\sqrt{.35\cdot1700000}$, the bound on $|S(iy)-1|$ and $|E_{b_0}|<.001$. Beyond $3$ through $|y|=.01$ its modulus is at most $1.002e^{-.49x^2}$ by the same cubic bound relative to $x^2$. From $.01$ to $.08$ use $1.002e^{-.199x^2}$ and $|x|>.01\sqrt{.35N}>7.7$. With weight $1+x^2$ these last two integrals together cost less than $.12$.

For $.08\le|y|\le.2$ use the first line of the block table. At $C=.0034N$, $v=.08$, the weighted integral is at most
$$2e^{20-Cv^2}\left[\frac{d}{2Cv}+d^3\left(\frac{v}{2C}+\frac{1}{4C^2v}\right)\right]<.001.$$
This is Gaussian integration by parts with $d\le\sqrt{.60N}$. Between $.2$ and $10^4$ use loss at least $.00249(.2)^2N$ and volume $2(1+10^4d)^3$. The low-frequency complementary term has the same volume bound and loss $.16N$. Above $10^4$ extract $e^{-N(10^4)^{2/3}/160}$ and integrate the remaining bound against $2e^{20}d(1+d^2)(1+y^2)e^{-y^{2/3}}$. The last three costs together are below $.01$.

In the second range the wider-disk proof still gives the gap $1.48/H^2$, the same contour and the complementary bound $e^{20-.16j/H^2}$ on $|w|\le.08$. Indeed the nodal cut at $1.5H$, its sine and exponential bounds, and the real-complement polynomial comparison there hold already at $H\ge10^7$. On the disk $|w|\le.04$ the energy error $H^2p(\beta(1+w))+a(1+w)^{2/3}$ is bounded by $2(12/H)^{.68}<.000189$ by the same semidisk estimate. Cauchy's bounds give $.13<p''/H^4<.82$ and $|p'''|/H^7<44$ on the smaller disk $|w|\le.01$ for the third derivative (the variance bounds are at zero). Thus $H^2\Re P(iy)\le-.04y^2$ through $|y|\le.003$. The shorter-walk estimate uses $|S(\pm.08)|<e^{12}$: at the intervening real tilts $p''<.82(.92)^{-4/3}H^4$ since their height exceeds $10^7$. Integrating the two exponential moment tails gives $|S(iy)-1|<.001+180|y|$. For $|x|\le6$ equation (2) now exceeds $.85e^{-x^2/2}$ in real part, with cubic error at most $44\cdot216/(6\cdot.13d)$. For $6<|x|$ through $|y|=.003$ the Taylor bound relative to $x^2$ gives modulus at most $1.002e^{-.32x^2}$. For $.003\le|y|\le10^4$ take loss $.0034(.003)^2N$, which exceeds 3000 at the threshold. The same complement and far-tail integrals apply.

In both ranges the integral of $\Re J$ over the scaled period exceeds $.5$. So does the integral with multiplier $4\sigma^2\sin^2(x/(2\sigma))$, which lies between $.99x^2$ and $x^2$ for $|x|\le3$ and is at most $x^2$ elsewhere. Both Gaussian integrals on $[-3,3]$, with weights one and $x^2$, exceed $2.3$. The integrated $|xJ|$ is below ten by the same absolute majorants. Fourier inversion gives a negative centered second difference at the tilted saddle and a relative adjacent difference below $20/\sigma<\beta/4$. Removing the geometric tilt proves the two assertions.

## The join in corank

Set $x_0=(a/3+.004)/1900$. For $n\ge10^{36}$ there is strict growth through $x_0s+1$. Below $9n$ use the [linear tail theorem](finite-tail.md). At $k\ge9n$ the saddle has $H>4$. For $H<2\cdot10^7$, $N>10^{21}$ and the [uniform inversion](flat-pairs.md#inversion-with-a-uniform-number-of-blocks) applies. From $2\cdot10^7$ to $2\cdot10^{12}$ we have $N\ge2.5\cdot10^{11}$. Above this height the [slope estimate](two-harmonics.md#analytic-control-on-a-wider-disk) gives $k/n>(2a/3-.001)H$. At $k\le x_0s+2$ it follows that
$$N\ge 1900^2(2a/3-.001)^2/\big((2.001)^3(a/3+.005)^2\big)>1700000.$$
For $x_0\le k/s\le4$ let $h=(\log f)'(k/s)$ where $f$ is the density of half the Brownian meander area. Its tilt $f_h\propto e^{-hx}f(x)$ has mode at $x=k/s$. The [limiting mode bound](tilt-concentration.md#width-of-the-continuous-tilted-law) at $r=h^{1/3}\ge250$ places the mode below $(a/3+7/r)/r$. Hence $r<1900$ for positive $h$, and the [negative slope bound](mode-comparison.md#the-tilt-at-the-point-of-comparison) gives $h>-1250$.

## Positive tests before normalization

Let $\epsilon=m^{-1/2}$, $r=\max(0,h)^{1/3}$ and $R=\max(50,-h,r,\sqrt{\log m})$. Define a positive measure $\mu$ on the scaled lattice by weighting the unconditioned surviving walk by $e^{-hK/s}/Z_*$, where $Z_*=\epsilon I_h(0)$ is the [Brownian boundary normalization](tilted-peak.md#relative-normalization-at-the-boundary). Its mass need not equal one. For a nonnegative bounded test $v$ with log Lipschitz constant $L$ write $B_v=\int vf_h$. We use
$$ e^{-u_L}B_v-3\epsilon^8\|v\|_\infty\ \le\ \int v\,d\mu\
 \le e^{u_L}B_v+3\epsilon^8\|v\|_\infty,\qquad
 u_L=(|h|+L)(\eta+\epsilon)+3\epsilon R^2 . \tag{3}$$
The zero test is allowed. In the [random-clock comparison](localized-mode.md#positive-tests-under-the-random-clock) take $V=2\sqrt{mX}$ and $\eta=9.36\epsilon X$, where
$$
 X=\begin{cases}
 1.31\max(15,r)^2+5\log m+4,&h\ge0,\\
 2(|h|+h^2/4+5\log m+4),&h<0 .
 \end{cases}
$$
Indeed $V/m<.001$, the area error on the common good event is bounded by $2.34V^2/s$, and the failure probability by $8e^{-X}$. For $h\ge0$ surviving weights are at most one and $I_h(0)\ge e^{-1.31\max(15,r)^2}$ by the [ground-energy normalization](two-harmonics.md#matching-the-two-area-scales). For $h<0$, $I_h(0)\ge I_0(0)>.7$, and the square root of the second exponential moment before the wall is at most $e^{|h|+h^2/4}$, for both the Gaussian area and the independent walk labels. Each discarded integral in units of $Z_*$ is therefore at most $\epsilon^8\|v\|_\infty$. For the Brownian endpoint shift use the same cutoff $\sup |W_u|\le R^2$ as in the localized proof. Its discarded cost is at most $4e^{-R^4/100+16R^2}\|v\|_\infty<\epsilon^8\|v\|_\infty$. The time and radial weight error is at most $2V/m+2\epsilon R^2+2\epsilon^2\le3\epsilon R^2$, and the endpoint displacement costs $\epsilon(|h|+L)$. The survival inclusions then give (3) before division by the test with $v=1$.

## A kernel for the adjacent-coefficient sign

Consider $|h|\ge1$. Write $\mu_k=\mu(\{k/s\})$ and
$$ A=\frac1{s(1-e^{-h/s})},\qquad |A|\le 1.001/|h|.$$
Positivity of $s\mu_k+A s^2(\mu_{k+1}-\mu_k)$ implies that $b_{k+1}-b_k$ has the sign of $h$, by multiplying out the tilt. The corresponding continuous quantity at the mode is $f_h(x)+Af_h'(x)=f_h(x)$.

Use the [trapezoidal Fourier cutoff](localized-mode.md#localized-fourier-inversion) with inverse kernel $K(z)=(\cos z-\cos 2z)/(\pi z^2)$. At bandwidth $T$ set $J=K+ATK'$. To test this signed kernel in (3) let $G(z)=3e^{-3|z|}/2$, and define $v_\pm=G*(J-J''/9)_\pm$ where the minus subscript denotes the magnitude of the negative part. Then $J=v_+-v_-$ because $(1-\partial_z^2/9)G$ is the unit point mass. Each nonzero test $v_\pm(T(x-y))$ has log Lipschitz constant at most $3T$ by the triangle inequality in the exponent of $G$. Their total integral before scaling satisfies
$$
 \|v_++v_-\|_1\le \|K\|_1+\|K''\|_1/9+
 |A|T(\|K'\|_1+\|K'''\|_1/9)<2.81+4.06 |A|T. \tag{4}
$$
For $i=0,1,2,3$, bound $|K^{(i)}(z)|$ by $\min(a_i,b_i/z^2)$ with $a_i=(2^{i+2}-1)/(\pi(i+1)(i+2))$ from the Fourier integral and $b_i=(4,10,28,60)_i/(2\pi)$ from the second distributional derivative of its multiplier. Integration gives $\|K^{(i)}\|_1\le4\sqrt{a_i b_i}$. These bounds prove (4). The two sup norms are each at most $3(1+|A|T)$ directly from the $a_i$.

Write $B=T\int J(T(x-y))f_h(y)\,dy$. Applying (3) to the two tests and subtracting gives the lower bound
$$
 T\int J(T(x-y))\,d\mu(y)\ \ge\
 \cosh(u)B-\sinh(u)(2.81+4.06|A|T) f_h(x)
 -18\epsilon^8T(1+|A|T),\qquad u=u_{3T}. \tag{5}
$$
Here $f_h(x)$ is the maximum of the density. Both signs use the same unknown normalizing mass of $\mu$.

## Fourier tails at the chosen cutoffs

| Tilt range | $T$ |
| --- | --- |
| $h<0$ | $10^5$ |
| $h\ge0,\ r\le4$ | $250000$ |
| $4<r<50$ | $1000\max(10,r)^3$ |
| $50\le r<500$ | $500r^2$ |
| $500\le r<1900$ | $170r^2$ |

For these cutoffs, $|B-f_h(x)|$ and the difference between the left side of (5) and the discrete adjacent functional are each below $.01 f_h(x)$. Here and below the lattice transform is integrated on its own period. The estimates proving this are as follows.

* For $h<0$ the [drifted suffix bound](two-harmonics.md#matching-the-two-area-scales) for the normalized transform is $4(|h|+2)e^{-.035|\xi|^{2/3}}$ up to $|\xi|\le s/8$. For $0\le r<50$ the same suffix argument with fair steps gives $16e^{-.035|\xi|^{2/3}}/I_h(0)$. In detail, use $2\lceil m/4\rceil$ suffix steps. At $|\theta|=|\xi|/s\le1/8$ pair labels a distance $l=\lceil4|\theta|^{-2/3}\rceil$ apart. In a block the unrestricted modulus is at most $e^{-.24l\sin^2(l\theta/2)}$. The retained positive weights lie in $[0,1]$, giving relative to fair unconditioned mass at most $(1+e^{-.24l\sin^2(l\theta/2)})/2<e^{-.61}$ since $\sin^2(l\theta/2)\ge.65(l\theta/2)^2$. At least $|\xi|^{2/3}/17-1$ blocks fit. The prefix has survival probability at most $2\epsilon$; the normalizer is at least $.7 Z_*$ by (3) at $v=1$ and the numerical bounds below. Both limiting envelopes follow by taking the length to infinity at fixed tilt. Above $s/8$ use the earlier normalized lattice envelopes with rates $1/4000$ and $1/150$, respectively. For $r\le4$ Jensen gives $I_h(0)\ge.7e^{-h/2}$. For $4<r<50$ put $z=.035 T^{2/3}=3.5\max(10,r)^2$; then $z-1.31\max(15,r)^2\ge55$. The integral of $\xi e^{-.035\xi^{2/3}}$ from $T$ to infinity is $(3/2)(.035)^{-3}(z^2+2z+2)e^{-z}$. This controls the tails with weight $1+|A\xi|\le2|\xi|$ there.
* At $r\ge50$, $H=\sqrt m/r\ge10^7$, $N=n/H^2\ge.49 r^2$ and $y=\xi/r^3$. The normalized lattice transform and its continuum limit satisfy $2e^{20-NB(y)}$ using the block table (use $.49r^2$ for $N$ in the limit). The factor two follows from the real principal term and complementary estimate at zero. Set $v=|\xi|/r^2$. For $|y|\le4.5$ use the common envelope $2e^{20-.000455 v^2}$. With $v\ge500$ this costs less than $.001$ at $r\le500$, integrating with $d|\xi|=r^2 dv$ and weight at most $1+1.001v/r$. At $r\ge500$ this same estimate handles $1\le|y|\le4.5$, where $v\ge r$. For $|y|\le1$, $v\ge170$, use $2e^{20-.00122v^2}$ and weight at most $1+.0021v$. The combined costs in these last two intervals, including both tails and both laws, are less than $.0001 r^2$. The [concentration lemma](tilt-concentration.md#width-of-the-continuous-tilted-law) gives $f_h(x)>.089r^2$ there.
* On $4.5\le |y|\le10^4$ the combined cost is below $12\cdot10^4 r^3(1+1.001\cdot10^4)e^{20-.075\cdot.49r^2}$, decreasing already at $r=50$. Above $10^4$ the bound is $2e^{20-|\xi|^{2/3}/170}$ since $N\ge.49r^2$. These tail estimates allow the mass factor $\mu(\mathbb R)<1.4$ for the unnormalized lattice transform. It follows from (3) at $L=0$. On $|\xi|\le2T$ the forward difference multiplier costs an additional $|A|\xi^2/(2s)$ in the integrand. Its integrated cost is below $.001$ because $T<7\cdot10^8$ and $s\ge(2\cdot10^{36})^{3/2}$. Throughout, $f_h(x)\ge\sqrt{6/\pi}>1$ by strong log-concavity.

## The size threshold

At $m\ge2\cdot10^{36}$ the clock and bandwidth choices give $u<.28$ and
$$ \sinh(u)\big(2.81+4.06\cdot1.001T/|h|\big)<.88. \tag{6}$$
For fixed tilt, $\epsilon$, $\epsilon R^2$ and $\epsilon X$ decrease with $m$, so it suffices to use $\log(2\cdot10^{36})<84$ in evaluating the endpoint. For negative $h$, bound $X/|h|$ by $2(1+1250/4+424)$ and $R^2/|h|$ by $2500$. For positive tilts split at $r=4,10,50,500$. On $10\le r<50$ the ratio $T/h=1000$. On $50\le r<500$ the ratio is at most ten. On the final interval both $u$ and $u/r$ increase with $r$ at this size endpoint, by their explicit positive-power formulas, and $\sinh(u)/u$ increases too. The largest bound in (6) is attained in this last comparison. Also $e^{u_0}+3\epsilon^8<1.4$ and $e^{-u_0}-3\epsilon^8>.7$ as used above.

The last error in (5) is less than $.001$. With the two inversion errors, (5) and (6) give strict positivity of the adjacent functional at $|h|\ge1$. For $|h|<1$ the [untilted peak estimate](peak-rate.md#unimodality-between-large-coefficients) already gives negative centered second differences at $m\ge10^{30}$. Since $h=(\log f)'(k/s)$ decreases with $k$, these steps give one interval of increase followed by one interval of decrease, allowing equality at the transition. They join the small-area growth below $x_0s+1$. Above $4s$ the [first-passage sign](first-passage.md) and then the [lower-half inequality](monotonicity.md#1-lower-half-for-all-sizes) continue the decrease in corank. This proves unimodality for both parities at the asserted sizes. The [maximum-height refinement](tilted-height.md) lowers this sufficient threshold to $10^{30}$. The [finite verification](certified-window.md) covers both families through 2048 rows.

The [rational checker](verify_holder.py) verifies the numerical bounds and tests the weighted block inequality by explicit endpoint enumeration. Run it with Python 3 from the checkout.

~~~sh
python3 -B verify_holder.py
~~~
