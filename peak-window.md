# Strict log-concavity on the scale of the peak

For either central shape write $m=2n$ or $2n+1$, $D=\lfloor m^2/4\rfloor$, $s_m=m^{3/2}$ and $b_k=a_{D-k}$. The argument below uses the full ballot paths, with free endpoint.

**Theorem.** Fix $0<u<v<\infty$. For all sufficiently large $m$,
$$b_k^2>b_{k-1}b_{k+1}\qquad(us_m\le k\le vs_m).$$
There is a common constant $x_*>0$ for both families such that every global maximum satisfies $k/s_m\to x_*$. It is the mode of half the area under a standard Brownian meander of duration one. In particular, for large $m$ all the global maximizers consist of one rank or two consecutive ranks. Smaller peaks outside any fixed window around this scale still matter to Conjecture 3.4.

## A bound on the characteristic function

Give the $m$ independent steps equal probabilities before conditioning. Let $E$ be the event of staying nonnegative, let $S$ be the sum of the labels of the down steps (labels decrease from $m$ to 1), and put $K=D-S$. Write $\Phi_m(\theta)=\mathbb E[e^{i\theta K}\mid E]$. There are absolute positive constants $c,C$ such that
$$|\Phi_m(\theta)|\le C\exp(-cm|\theta|^{2/3})\qquad(-\pi\le\theta\le\pi).$$

To prove this, take a block of $2l$ consecutive labels. Its unrestricted complex transition kernel takes a starting height to an ending height with weight $e^{-i\theta S_{\rm block}}$ times the fair-word probability. On interchanging the two halves of a block the endpoint stays fixed, and the difference of the two label sums is, up to sign, $l(d_1-d_2)$, where $d_1,d_2$ are the numbers of downs in the two halves. Average the two orders before applying the triangle inequality at each endpoint. The sum of the absolute entries of any row is bounded by
$$\mathbb E|\cos(\theta l(d_1-d_2)/2)|
 \le \left((1+\cos^{2l}(\theta l/2))/2\right)^{1/2}.$$
Here $d_1,d_2$ are independent binomials with parameters $(l,1/2)$, which gives the last expression on squaring the cosine and taking its expectation.

For $0<|\theta|\le1$, set $l=\lfloor|\theta|^{-2/3}\rfloor$. Then $|\theta|l\le1$ and $\theta^2 l^3\ge1/8$. The elementary bound $\cos t\le e^{-t^2/2}$ for $|t|\le1$ makes the displayed expression at most an absolute $\rho<1$. For $1\le|\theta|\le\pi$, take $l=1$ and use $|\cos(\theta/2)|\le\cos(1/2)$. Enlarge $\rho<1$ to cover both ranges.

For a fixed nonnegative starting height let $p$ be the probability of surviving the block. Killing paths at the wall gives a row of absolute sum at most $p$. Deleting the rejected paths from the unrestricted kernel also gives the bound $\rho+1-p$ (regard both rows as indexed by all integer endpoints). Thus every killed row has absolute sum at most $(1+\rho)/2<1$. This bound is independent of the starting height and of the position of the block.

Split after $h=\lfloor m/2\rfloor$ steps. The complex row of surviving prefixes has absolute sum at most $\Pr(E_h)$. In the remainder use as many full blocks as fit, and bound the final partial block by one in maximum absolute row sum. The conditional expectation is bounded by
$$\frac{\Pr(E_h)}{\Pr(E_m)}
  \left(\frac{1+\rho}{2}\right)^{\lfloor(m-h)/(2l)\rfloor}.$$
The prefactor is bounded by the ballot counts $2^{-j}\binom{j}{\lfloor j/2\rfloor}$. Since $1/l\gg|\theta|^{2/3}$ throughout the Fourier interval, this proves the claim, including the case in which fewer than $2l$ steps remain.

## Differentiable local limits

Under survival, the scaled height process converges in distribution to the standard Brownian meander $M$ on $[0,1]$. For the strict-positivity convention, prepend one up step to the nonnegative walk; this gives the uniform strictly positive walk of length $m+1$ and changes the scaled area by $o(1)$. By the [corank identity](monotonicity.md#3-decrease-near-the-top),
$$K/s_m\ \Longrightarrow\ Y=\tfrac12\int_0^1 M(t)\,dt.$$
The factor $1/2$ comes from $\lfloor h_t/2\rfloor$. Takács studied this area limit; Denisov, Kolb and Wachtel also give local estimates for meander area. We need convergence of adjacent *differences*, which follows here from the block bound. [Conditioned-walk invariance principle](https://doi.org/10.1214/aop/1176996607) · [Takács](https://doi.org/10.2307/3215294) · [Denisov, Kolb and Wachtel](https://doi.org/10.1112/jlms/jdu078)

Set $p_m(k)=b_k/\binom{m}{n}$, extended by zero, and let $\Delta p_m(k)=p_m(k+1)-p_m(k)$. For each fixed integer $r\ge0$, the law of $Y$ has a smooth density $f$ and
$$\sup_{k\in\mathbb Z}\left|s_m^{r+1}\Delta^r p_m(k)-f^{(r)}(k/s_m)\right|\longrightarrow0.$$
Indeed in the inversion integral substitute $t=s_m\theta$. The characteristic function at $t/s_m$ converges pointwise by weak convergence, and for $|t|\le\pi s_m$ its modulus is bounded by $C e^{-c|t|^{2/3}}$. Each scaled forward difference inserts the multiplier $s_m(e^{-it/s_m}-1)$, which tends to $-it$ and has modulus at most $|t|$. Extending integrands by zero outside the inversion interval gives convergence in $L^1$ with every fixed polynomial weight, and hence the stated uniform estimates. In particular $f$ and its derivatives vanish at infinity.

## Curvature of the limiting density

Use a walk with independent standard Gaussian increments $G_i$, conditioned on all prefix sums being nonnegative. Its rescaled half-area
$$Y_m=\frac{1}{2s_m}\sum_{i=1}^m(m+1-i)G_i$$
has the same weak limit $Y$ by the conditioned-walk invariance principle. Before conditioning it is Gaussian with variance $V_m=\sum_{r=1}^m r^2/(4m^3)\to1/12$.

Project the Gaussian increment vector orthogonally onto the direction defining $Y_m$ and its orthogonal complement. The complement is independent of $Y_m$. In the resulting coordinates $(y,z)$ the survival region is convex, being defined by linear inequalities. Its indicator times the Gaussian density of the complement is log-concave in $(y,z)$. Integrating out $z$ by Prékopa's theorem gives a log-concave function of $y$. Thus for the conditioned density $f_m$, the function $e^{y^2/(2V_m)}f_m(y)$ is log-concave. [Prékopa, *On logarithmic concave measures and functions*](https://acta.bibl.u-szeged.hu/14411/)

This implies $e^{6y^2}f(y)$ is log-concave. For details, the weighted measures with densities $e^{y^2/(2V_m)}f_m(y)$ converge against compactly supported continuous tests to $e^{6y^2}f(y)\,dy$. Their masses of bounded intervals converge because the limit has a continuous density. Apply the log-concave measure inequality to two equal-length intervals and their interpolated interval, pass to the limit, divide by the common length, then shrink the intervals to points. The interval inequality itself follows by integrating the log-concave density against the indicator of a translated interval, another application of Prékopa's theorem.

The support of $Y$ is $[0,\infty)$. For instance Imhof's relation makes the meander law equivalent to the law of the norm of three-dimensional Brownian motion on $[0,1]$. This norm has positive probability in each uniform neighborhood of $t\mapsto at$, $a\ge0$, by Brownian full support applied to the path $(at,0,0)$. The half-areas of these paths range over $[0,\infty)$. Log-concavity and full support therefore give $f(x)>0$ for $x>0$. Smoothness and vanishing on $x<0$ give $f(0)=0$. [Imhof's density relation](https://www.cambridge.org/core/journals/journal-of-applied-probability/article/abs/density-factorizations-for-brownian-motion-meander-and-the-threedimensional-bessel-process-and-applications/F9310E6BCC0BFABB3DC295C35E3F29DD)

On $(0,\infty)$ we have $(\log f)''\le-12$. The continuous density tends to zero at both ends of this interval and has a unique maximum $x_*>0$.

## Consequences for the coefficients

At $x=k/s_m$ in a fixed compact subinterval of $(0,\infty)$, the difference limits give, uniformly,
$$s_m^4\big(p_m(k)^2-p_m(k-1)p_m(k+1)\big)
  =f'(x)^2-f(x)f''(x)+o(1)\ \ge\ 12f(x)^2+o(1).$$
This follows by expanding the determinant as the product of backward and forward first differences minus $p_m(k)\Delta^2p_m(k-1)$. The right-hand side has a positive uniform lower bound on that interval. This proves strict log-concavity there.

The zeroth-order limit is uniform over *all* ranks. Outside each fixed neighborhood of $x_*$ the supremum of $f$ is strictly below $f(x_*)$, since $f$ vanishes at infinity and has a unique maximizer. Taking the lattice point nearest $s_m x_*$ rules out a global maximum outside the neighborhood for large $m$. All global maxima therefore lie in one compact window of strict log-concavity, proving the assertion on ties.

## Remaining ranges

Together with the [two tail estimates](monotonicity.md), the result identifies two possible ways that a sequence of arbitrarily large counterexamples could escape these arguments. Extra reversals could occur with $k/n\to\infty$ and $k/m^{3/2}\to0$, or with $k/m^{3/2}\to\infty$ while $k=O(m^{3/2}\log m)$. The absolute error in the difference limits gives no relative control as $f$ tends to zero. An eventual result on both remaining ranges would also require a way to cover the sizes below its threshold to settle the conjecture for every $n$.
