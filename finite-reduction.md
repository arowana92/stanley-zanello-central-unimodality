# Reduction to an explicit finite range

Put $N=10^{61}$. For both central staircases the rank sequence is unimodal whenever $n\ge N$. Consequently any counterexample to Conjecture 3.4 must have $1001\le n<N$, using the [finite verification through 1000 rows](certified-window.md) for the lower bound. This upper bound on possible exceptional sizes is far beyond feasible exhaustive computation.

The [odd-height flat pairs](flat-pairs.md) and [linear-potential estimate](linear-potential.md) give growth through $10^{-5}n^{3/2}$ at $n\ge10^{61}$. The [localized mode comparison](localized-mode.md) overlaps this interval and joins the [increasing-side estimate](first-passage.md) at $4m^{3/2}$. It also gives strict log-concavity on the upper half for $n\ge10^{118}$. Earlier thresholds follow from the [tilted concentration argument](tilt-concentration.md) and the estimates below. All arguments apply to both word parities.

## Unimodality from the first difference

Let $m=2n$ or $2n+1$, $s=m^{3/2}$, $D=\lfloor m^2/4\rfloor$ and $b_k=a_{D-k}$. Assume $n\ge10^{290}$. The [tail theorem](finite-tail.md) gives strict growth in corank through $2n$. The [small-corank estimate](harmonic-small-area.md) continues it through $3\cdot10^{-15}n^{3/2}$. Take $R_0=10^{-4}m^{1/28}$ and $R_1=10^{-5}m^{1/14}$. We have $R_0>10^6$ and
$$\frac{4s/R_1}{n^{3/2}}\le 4\cdot10^5(2.001)^{3/2}m^{-1/14}<2.2\cdot10^{-15}.$$
Thus the proved interval of growth extends more than two ranks past $4s/R_1$.

From $4s/R_1$ to $4s$ the [positive-tilt first-difference argument](tilted-peak.md#strict-increase-in-corank-under-a-larger-positive-tilt) gives strict growth followed by strict log-concavity, in that order. The slope $(\log f)'(k/s)$ is decreasing, and at $x=4$ it is already below $R_0^3$ by the upper secant estimate with $u=2/R_0$. The [first-passage theorem](first-passage.md) continues strict log-concavity from $4s$ to $D/2$. Every corank step before the log-concave interval is therefore increasing, and within that interval the adjacent ratios can cross one only downwards. Beyond the midpoint the [lower-half rank inequality](monotonicity.md#1-lower-half-for-all-sizes) gives weak decrease in corank, including the central step when $D$ is odd. This proves unimodality for both parities.

## Joining the three intervals

Write $m=2n$ for the odd-part staircase and $m=2n+1$ for the even-part staircase. The degree of the rank polynomial is $D=\lfloor m^2/4\rfloor$, and rank $j$ corresponds to corank $k=D-j$. At $n\ge10^{550}$ the following results give $a_j^2>a_{j-1}a_{j+1}$ on their respective corank intervals.

| Integer corank $k$ | Estimate |
| --- | --- |
| $1\le k\le 2n$ | [Sparse and bounded tilts](upper-curvature.md#joining-the-tilts-between-the-sparse-and-peak-regimes) |
| $2n\le k\le 3\cdot10^{-15}n^{3/2}$ | [Small-corank transfer estimate](harmonic-small-area.md) |
| $4\cdot10^4m^{41/28}\le k\le D/2$ | [Tilted Brownian comparison and increasing-side estimate](tilted-peak.md#a-range-of-coranks-with-strict-log-concavity) |

For the last two rows, $m/n\le2.001$ at these sizes and
$$\frac{4\cdot10^4 m^{41/28}}{n^{3/2}}\le4\cdot10^4(2.001)^{3/2}m^{-1/28}<2.6\cdot10^{-15}$$
at $m\ge10^{550}$. Thus the second interval extends more than two whole ranks beyond the start of the third. Every interior rank $j\ge D/2$ lies in the union. On this interval the adjacent coefficient ratios decrease and hence cross one at most once. The [lower-half inequality](monotonicity.md#1-lower-half-for-all-sizes) gives weak growth up to $\lceil D/2\rceil$. This proves unimodality of both rank sequences throughout the stated size range.

## Exact area moments

Write $m=2n+\delta$, $s=m^{3/2}$, $Y_m=K/s$ for the scaled area of a uniform surviving word, and $Y$ for half the area of the standard Brownian meander. The [peak-window argument](peak-window.md) gives $Y_m\Rightarrow Y$, a smooth density $f$ and $(\log f)''\le-12$ on $(0,\infty)$. Takács derived limit distributions and moments for Bernoulli meander area. We use the two last-return recurrences to control the errors at finite $m$. [Takács](https://doi.org/10.2307/3215294)

For $x\ge1$ there is the uniform bound $\Pr(Y_m\ge x)\le2e^{-x^2/2}/x$. Indeed $K\le m\max H_t/2$. To reach $h=\lceil2x\sqrt m\rceil$ before hitting $-1$ the walk must first hit $\lfloor h/2\rfloor$ before $-1$, of probability at most $2/h$ by fair ruin probabilities. From there it must climb at least $h/2$ in at most $m$ steps, of probability at most $e^{-h^2/(8m)}$ by the exponential maximal inequality. Divide by $\Pr(E_m)=2^{-m}\binom{m}{n}\ge1/(2\sqrt m)$. Thus all fixed moments converge by uniform integrability. For $d\ge1$ the even moments of both $Y_m$ and $Y$ are bounded by $1+2^{d+1}d!$, by integration of this tail.

Use the [Catalan series](README.md#catalan-recurrences-for-the-two-families) $C,B,O$ with length variable $z$ and area variable $q=e^x$. Put $v=\sqrt{1-4z}$. At $x=0$ we have $C_0=2/(1+v)$, $B_0=1/v$ and $O_0=C_0B_0$. Factor these three respective bases out of the series and expand in ordinary powers $x^r$, with constant coefficient one in each factored series. The coefficients are Laurent polynomials in $v$ over the rationals, computed as follows.

* Write $D=z\partial_z=(v-v^{-1})\partial_v/2$. On coefficients multiplying $C_0$ and $B_0$ the respective operators are $D_C=D+(v^{-1}-1)/2$ and $D_B=D+(v^{-2}-1)/2$. The substitution $z\mapsto e^{a x}z$ in a based series with coefficients $P_i$ gives at order $r$ the sum $\sum_{i+j=r}a^j D_{\rm base}^j P_i/j!$.
* For $C=1+zC(z,q)C(qz,q)$ the multiplier on the product after factoring is $(1-v)/2$. Omit the two unknown order-$r$ terms, multiply the known product coefficient by $(1-v)/(2v)$, and obtain the normalized $C$ coefficient at $r\ge1$.
* For $B=C+e^x(C-1)B(e^{2x}z,q)$, divide the equation at order $r$ by $B_0(2-C_0)$. The normalized $B$ coefficient is the normalized $C$ coefficient plus $v^{-1}$ times the known order-$r$ coefficient of $e^x ((C-1)/C_0)(B(e^{2x}z,q)/B_0)$. Here the constant of $(C-1)/C_0$ is $(1-v)/2$, and only the as-yet unknown $B$ coefficient is omitted. Finally multiply the normalized $C$ series by the normalized shifted $B(e^xz,q)$ series to obtain the normalized $O$ series.

Multiply the resulting even and odd coefficient polynomials at order $r$ by $r!v^{-1}$ and $r!(1-v)v^{-1}$ respectively. Write $P_{\delta,r}(v)=\sum_h c_hv^h$ for the result. With $\ell=n+\delta$, set
$$R_h(\ell)=\frac{[z^\ell](1-4z)^{h/2}}{\binom{2\ell}{\ell}}
 =\prod_{i=0}^{\ell-1}\frac{2i-h}{2i+1}.$$
Then the exact scaled moment is
$$\mathbb E Y_m^r=(2\ell-\delta)^{-3r/2}\sum_h c_h R_h(\ell).\tag{1}$$
For the odd case this uses $C_0=(1-v)/(2z)$ and $\binom{2n+2}{n+1}=2\binom{2n+1}{n}$. For example the coefficient of $v^{-4}$ in both first-moment polynomials is $3/4$, and that of $v^{-7}$ in both second-moment polynomials is $59/16$. Formula (1) gives the limiting moments $3\sqrt{2\pi}/16$ and $59/240$.

The following checks (1) in exact arithmetic against the rank polynomials for both parities and against direct partition enumeration for small shapes.

~~~sh
python3 -B verify_moments.py --order 10 --max-n 64 --direct-n 12
~~~

## A uniform error estimate for finitely many moments

For any positive integer $Q$, take
$$J=1000(Q+4)^6,\qquad V=2^{2^J},\qquad E=(10V)^{10V}.$$
For $0\le r\le Q$ and $n\ge(10V)^4$ we claim
$$|\mathbb E Y_m^r-\mathbb E Y^r|\le E/\sqrt n.\tag{2}$$

Here are bounds on the algebra in (1). The maximum absolute exponent and the sum of absolute coefficients of every $P_{\delta,r}$ are at most $V$. For clarity, one may count Laurent polynomial operations following the three recurrences above. For a series shifted by $e^{a x}$ through order $r$, form each sequence of divided derivatives by repeatedly applying $a D_{\rm base}/j$ to its preceding entry, then add by total order. Its triangular array has at most $(r+1)^2$ entries. At each order form three such arrays and the products, including the convolution with $\sum x^j/j!$. Fewer than $50(Q+2)^4$ binary additions, products, Euler derivatives and scalar operations suffice for all orders combined, counting the logarithmic derivative of each base as a fixed Laurent multiplier. The only large final scalar $r!$ can be included as $r$ multiplications by integers at most $Q$. To bound every intermediate size start at $Q+10$, and after every operation replace the current bound $S$ by $10S^2$. For example on $v^h$, $D$ has two terms with coefficient sum $|h|$. Fixed factors, monomial shifts and multiplication by $a/j$ or $1/j!$ all obey this bound. Iteration gives $\log_2 S\le 2^{50(Q+2)^4}(\log_2(Q+10)+4)<2^J$. This also bounds $r!$ times the polynomials as claimed.

For even $h\ge0$ the contribution vanishes for $\ell>h/2$. For every other $h$, $R_h(\ell)$ has leading term $L_h\ell^{-(h+1)/2}$ with $L_h\ne0$. Start at $R_{-1}=1$ or $R_{-2}=4^\ell/\binom{2\ell}{\ell}$. The latter is between $\sqrt{\pi\ell}$ and $\sqrt{\pi(\ell+1)}$ by the Wallis inequalities. Move by steps of two using $R_{h+2}/R_h=(h+2)/(h+2-2\ell)$, staying in the odd indices or the strictly negative even indices. This construction gives $|L_h|\le(2V+4)^{V+2}$. When $\ell\ge(10V)^4$, the absolute log of the ratio to the signed leading term is at most $4(V+2)^2/\ell$. Indeed each nonconstant correction factor is $1+a/(2\ell)$ or its inverse with $|a|\le V+2$, and there are at most $V+1$ of them in addition to the Wallis factor. Including the factor $(1-\delta/(2\ell))^{-3r/2}$ in (1) raises this log bound to at most $6(V+2)^2/\ell$.

All nonvanishing terms in (1) have $h\ge-3r-1$. Otherwise the smallest such exponent would give a unique unbounded leading term, contradicting the uniform moment bound. The possible term $h=-3r-1$ has a constant limit, and every other term is $O(\ell^{-1/2})$ with the explicit factors just bounded. Using $|e^t-1|\le2|t|$ for $|t|\le1/2$, their sum differs from its limit by at most $V(2V+4)^{V+2}(12(V+2)^2+2)/\sqrt\ell$. This is bounded by $E/\sqrt n$. The limit is the moment of $Y$ by the tail bound, proving (2).

## Density lower bound and inversion

For every $0<u\le10^{-5}$ the density has the lower bound $b=2^{-\lceil10^8/u^2\rceil}$ on $[u,201]$. To verify the constant, use Imhof's relation from the [density argument](peak-window.md#curvature-of-the-limiting-density). For three-dimensional Brownian motion $W$ started at zero, the meander law is the law of $|W|$ reweighted by $\sqrt{\pi/2}/|W(1)|$. About each of the two straight paths $4xt e_1$, $x=u/2$ or $202$, take a tube of radius $a=u/8$ in uniform Euclidean distance. The half-area is within $a/2$ of $x$ there. The constant-drift change of measure bounds the Brownian tube mass below by $\exp(-8x^2-4xa)$ times the centered tube mass. Each Brownian coordinate stays within $[-a/2,a/2]$ through time one with probability at least $\exp(-\pi^2/(2a^2))$, by the killed eigenfunction $y\mapsto\cos(\pi y/a)$ on that interval. The coordinates are independent and the corresponding cube fits in the centered tube. The Imhof factor exceeds $1/810$ on both tubes. Each of the two area intervals therefore has mass at least $\exp(-10^7/u^2)>b$ and length less than one. Each contains a point of density at least $b$, one below $u$ and one above $201$. Log-concavity gives the assertion.

The untilted inversion below uses the specific rational numbers
$$u=10^{-272},\qquad b=2^{-10^{552}},\qquad \varepsilon=b^2/10^{40}.$$

Let $P_m(k)=b_k/\binom{m}{n}$ with $b_k$ the corank coefficient, and $\Delta P_m(k)=P_m(k+1)-P_m(k)$. We derive a uniform error at most $\varepsilon$ when approximating $s^{r+1}\Delta^r P_m(k)$ by $f^{(r)}(k/s)$ for $r=0,1,2$. The fair-walk characteristic function on the scaled interval $[-\pi s,\pi s]$ is bounded by $10e^{-|t|^{2/3}/4000}$. This is the [paired-label estimate](effective-middle.md#restoring-the-wall-without-losing-a-lattice-difference) using a surviving prefix to $\lceil m/2\rceil$ and the explicit ballot ratio $\Pr(E_{\lceil m/2\rceil})/\Pr(E_m)\le4$ for $m\ge4$. The same bound holds for the limiting characteristic function by weak convergence. Its integral with weight $1+|t|^3$ over the line is below $10^{30}$ by the substitution $y=|t|^{2/3}/4000$. In particular all derivatives of $f$ through order three have absolute value below $10^{30}$.

The [untilted derivative estimate](peak-rate.md) bounds all three errors by $10^{21}m^{-1/4}$. At the earlier sufficient threshold $n\ge10^{10^{554}}$ this is less than $\varepsilon$, and $10^{30}/s<\varepsilon$ as well. Indeed $(10^{554}/4)\log 10>2\cdot10^{552}\log 2+61\log 10$.

For the independent moment-based estimate take the integers and rational tolerance
$$
 T=\lceil10^{33}/\varepsilon\rceil,\qquad
 \tau=\varepsilon/(1000(1+T)^3),\qquad
 d=\lceil16T^2/\tau\rceil,\qquad Q=2d.
$$
Use $V,E$ above at this $Q$. It suffices to have
$$ n\ \ge\ N_0=\left\lceil\big(10V(Q+1)(1+T)^{Q+4}E/\tau\big)^4\right\rceil.\tag{3}$$
In fact, outside $[-T,T]$ the Fourier tails weighted by $|t|^r$ cost at most $2\cdot10^{30}/T$ for both transforms combined. Inside, expand $e^{itY_m}$ and $e^{itY}$ through order $2d-1$. Each remainder in expectation is at most
$$\frac{T^{2d}(1+2^{d+1}d!)}{(2d)!}\le3(2T^2/d)^d<\tau.$$
The sum of the moment errors is bounded by $(Q+1)(1+T)^Q E/\sqrt n<\tau$. Thus the characteristic functions differ by at most $3\tau$ on this interval. The scaled forward-difference multiplier $s(e^{-it/s}-1)$ differs from $-it$ by at most $t^2/(2s)$ and has modulus at most $|t|$. For its $r$th power the error is at most $r|t|^{r+1}/(2s)$ for $r=1,2$. Condition (3) ensures $\pi s>T$, $2(1+T)^4/s<\varepsilon/100$ and $10^{30}/s<\varepsilon$. Fourier inversion now gives the claimed three errors, including the zeroth derivative. These estimates use only rational polynomial operations, elementary functions and the proved tail and curvature bounds.

In the identity
$$P_m(k)^2-P_m(k-1)P_m(k+1)
 =\Delta P_m(k-1)\Delta P_m(k)-P_m(k)\Delta^2 P_m(k-1),$$
multiply by $s^4$ and put $x=k/s$. Evaluation at $(k-1)/s$ in place of $x$ costs at most $10^{30}/s$ per limiting derivative. The scaled determinant therefore differs from $f'(x)^2-f(x)f''(x)$ by at most $12\cdot10^{30}\varepsilon$. On $[u,201]$ the latter determinant is at least $12f(x)^2\ge12 b^2$. This proves strict log-concavity at every such lattice point for $n\ge10^{10^{554}}$, and independently under (3).

For either untilted threshold, $u(3n)^{3/2}+2<10^{-270}n^{3/2}$, so this window meets the [original small-area bound](effective-small-area.md). At its other end $201s>200s+2$ meets the [increasing-side bound](effective-middle.md). The bounded-tilt and lower-half arguments above then finish the independent reduction.
