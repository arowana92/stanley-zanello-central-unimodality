# A finite-size error bound at the peak

Let $m=2n$ or $2n+1$, $s=m^{3/2}$ and $P_m(k)=b_k/\binom{m}{n}$ for the corank $k$. Extend the probabilities by zero outside the support. Let $f$ be the density of $Y$, half the area of the standard Brownian meander of duration one. With $\Delta P(k)=P(k+1)-P(k)$, for $m\ge2$ and $r=0,1,2$ we have
$$
\sup_{k\in\mathbb Z}|s^{r+1}\Delta^r P_m(k)-f^{(r)}(k/s)|
\ \le\ E_m=\frac{10^{15}(1+\log m)^6}{\sqrt m}
\ \le\ 10^{21}m^{-1/4}. \tag{1}
$$
Here $\log$ is natural. Every maximizing corank lies between $s/5000$ and $7s$ for every $n\ge2$. For $m\ge10^{90}$ the ranks at half the maximum form an interval of strict log-concavity. The [tilted extension](tilted-peak.md) controls second differences in the tails.

## Coupling the area while retaining the wall

Start a standard Brownian motion $B$ at zero. Put $T_0=0$ and let $T_i$ be the first time after $T_{i-1}$ that $B$ moves one unit from its position there. Then $H_i=B(T_i)$ is a simple symmetric walk. The clock increments $D_i=T_i-T_{i-1}$ are independent and identically distributed, and the entire clock sequence is independent of all walk signs. These properties follow from the strong Markov property and reflection symmetry of a single exit. We use $\mathbb ED_i=1$ and $\operatorname{Var}D_i=2/3$. For example the first and second exit-time moments from $x\in[-1,1]$ are $1-x^2$ and $5/3-2x^2+x^4/3$. They solve the two exit-time differential equations with zero boundary values. [Brownian walk embedding, Lalley](https://galton.uchicago.edu/~lalley/Courses/383/BrownianMotion.pdf)

Write $J=\inf\{i:H_i=-1\}$, $A=\{J>m\}$ and $C=\{T_J>m\}$. The continuous first passage to $-1$ occurs at $T_J$. Thus $A$ is discrete survival and $C$ is Brownian survival to a deterministic time. We claim $\Pr(A\triangle C)\le64/m$. For fixed $J=j$, a mismatch costs at most $\min(1,j/(j-m)^2)$ by independence and Chebyshev, taking the bound one at $j=m$. When $j\le m/2$ or $j\ge2m$ this is at most $2/m$. In the intervening range,
$$\Pr(J=j)\le 2j^{-3/2}<6m^{-3/2}.$$
Indeed for $j=2h+1$ its mass is $2^{-j}\binom{2h}{h}/(h+1)$ by first passage and the Catalan count, and for even $j$ it vanishes. The sum over integer offsets $l=j-m$ of $\min(1,2m/l^2)$ is at most $1+4\sqrt{2m}$ by integral comparison. This proves the claim. For any complex random variable bounded by one in modulus, the two conditional expectations consequently differ by at most $2\Pr(A\triangle C)/\Pr(A)\le256/\sqrt m$, using $\Pr(A)=2^{-m}\binom{m}{\lfloor m/2\rfloor}\ge1/(2\sqrt m)$.

Put $M=\max_{0\le i\le m}H_i$. Under $A$ we have $\mathbb E[M^2\mid A]\le21m$. For an integer height $h\ge1$ first reach $\lfloor h/2\rfloor$ before $-1$, of probability at most $2/h$ by fair ruin probabilities. Then climb at least $h/2$ within $m$ steps, of probability at most $e^{-h^2/(8m)}$ by the exponential maximal inequality. Dividing by $\Pr(A)$ and rounding $h$ up gives the tail bound $4\sqrt m\, e^{-x^2/(8m)}/x$ for every real $x>0$. Integrating against $2x\,dx$ proves the moment bound.

The discrete area is $K=\sum_{i=1}^m\lfloor H_i/2\rfloor$. Under $A$, the conditional expectation of
$$\left|K-\frac12\int_0^m(1+B_u)\,du\right|$$
is at most $10m$. To verify this, replace $2K$ by $\sum H_i$ at cost at most $m$. Then replace $\sum H_i$ by $\sum H_iD_i$. Conditional on the signs the error is centered with variance $(2/3)\sum H_i^2$, so its conditional mean absolute value averaged over $A$ is below $4m$. The integral up to $T_m$ differs from $\sum H_iD_i$ by at most $3T_m$, since during each crossing the position differs from its final height by at most two. The conditional mean of $T_m$ is $m$.

To change the upper integration limit to $m$, put $V=|T_m-m|$. When $T_m\ge m$ the absolute integrand is at most $M+2$ through time $T_m$ on $A$. When $T_m<m$ the future Brownian increments are independent, so the conditional expected integral of their absolute values up to duration $V$ is at most $V^{3/2}$. The expected cost of the time correction on $A$ is therefore at most $(5\sqrt m+2)\mathbb E V+\mathbb E V^{3/2}\le8m$, by clock independence and $\mathbb EV^2=2m/3$. Adding the errors and dividing by two gives the asserted bound.

## Starting height and meander law

Under $C$, the scaled path $(1+B_{mt})/\sqrt m$ has the law of Brownian motion started at $a=m^{-1/2}$ conditional on survival to one. Let $W$ be a three-dimensional standard Brownian motion and $R^a_t=|W_t+a e_1|$. The conditioned path has the law of $R^a$ weighted by $g_a=1/R^a_1$ and normalized. Indeed integrating the three-dimensional heat kernel over a sphere gives the radial transition density $(y/x)(p_t(y-x)-p_t(y+x))$ from $x>0$. The difference in parentheses is the killed Brownian kernel by reflection. The factors $y/x$ telescope over successive times. At $a=0$ the reciprocal-endpoint weighting is Imhof's relation for the standard meander. [Imhof](https://www.cambridge.org/core/journals/journal-of-applied-probability/article/abs/density-factorizations-for-brownian-motion-meander-and-the-threedimensional-bessel-process-and-applications/F9310E6BCC0BFABB3DC295C35E3F29DD)

The two radial paths differ by at most $a$ everywhere. Also $\mathbb E|g_a-g_0|\le a\,\mathbb E(g_ag_0)\le a$. For the last bound $\mathbb E g_a^2\le1$ follows by integrating $\mathbb E e^{-v|W_1+a e_1|^2}=(1+2v)^{-3/2}\exp(-va^2/(1+2v))$ over $v>0$. For $0<a\le1$ the normalization $\mathbb E g_a=\Pr_a(\text{survival to one})/a=a^{-1}\int_{-a}^a e^{-x^2/2}\,dx/\sqrt{2\pi}$ exceeds $.48$. The normalized weights therefore differ in $L^1$ by less than $5a$.

Write $\Phi_m(t)=\mathbb E(e^{itK/s}\mid A)$ and $\Phi(t)=\mathbb E e^{itY}$. Comparing the two areas under $A$, replacing $A$ by $C$ for the Brownian area, and then using the radial coupling and weight bounds gives, for every real $t$,
$$|\Phi_m(t)-\Phi(t)|\le300(1+|t|)/\sqrt m. \tag{2}$$
Only the integrated path enters the comparison, which permits the independent clock to give a square-root rate.

## Fourier inversion for lattice differences

For the fair walk we sharpen the [paired-label estimate](effective-middle.md#restoring-the-wall-without-losing-a-lattice-difference) to
$$|\Phi_m(t)|\le 8e^{-|t|^{2/3}/100}\qquad(|t|\le\pi s). \tag{3}$$
Write $\theta=|t|/s>0$. An unrestricted block of $2l$ steps pairs the first $l$ labels with those $l$ places later. Conditioning on the number of downs in each pair fixes the endpoint. Averaging the modulus of the mixed-pair phase factor gives the absolute row-sum bound $\rho=((1+|\cos(l\theta/2)|)/2)^l$. Killing at the wall costs at most $(1+\rho)/2$ per block, since a row of survival probability $p$ has modulus sum at most both $p$ and $1+\rho-p$.

* For $\theta\le1/8$ choose $l=\lceil4\theta^{-2/3}\rceil$. Then $l\theta<\pi$, $l\theta^{2/3}\le4.25$ and $\rho=\cos^{2l}(l\theta/4)\le e^{-l^3\theta^2/16}\le e^{-4}$. The killed bound is below $e^{-.67}$.
* For $\theta>1/8$ take the nearest integer $l$ to $\pi/\theta$. If $l\ge2$, then $\theta\le2\pi/3$, $l\theta^{2/3}<7.2$, and $|\cos(l\theta/2)|\le\sin(\theta/4)\le1/2$. The killed bound is at most $(1+(3/4)^2)/2<e^{-.24}$. If $l=1$, then $\theta\ge2\pi/3$ and the killed bound is at most $7/8<e^{-.13}$, while $\theta^{2/3}<2.15$.

After a surviving prefix of length $h=\lfloor m/4\rfloor$ at least $3m/4$ steps remain. The prefix costs at most $\Pr(E_h)/\Pr(E_m)\le4$ after conditioning, using the central binomial bounds $\Pr(E_h)\le1/\sqrt{h+1}$ and $\Pr(E_m)\ge1/(2\sqrt m)$ for the survival events. In each case above, if the per-block bound is $e^{-c}$, then $3c/(8l)\ge\theta^{2/3}/100$. Rounding the number of full blocks down costs at most $e^{.67}<2$. This proves (3), including configurations with no full block. The limiting transform satisfies the same bound by weak convergence.

Extend $\Phi_m$ by zero outside $[-\pi s,\pi s]$ for inversion. Inequality (2) continues to hold there since its right side exceeds one. In inversion the error in (1) is bounded by the integral of $|t|^r|\Phi_m-\Phi|/(2\pi)$ plus the multiplier error. The latter is at most $r/(4\pi s)$ times the integral of $|t|^{r+1}|\Phi_m(t)|$, since $|s(e^{-it/s}-1)+it|\le t^2/(2s)$ and both multipliers have modulus at most $|t|$. In the first integral split at $|t|=T=(100\log m)^{3/2}$. Below $T$ use (2) for a bound of $300(1+T)^4/\sqrt m$. Above $T$ use $16m^{-1/2}\exp(-|t|^{2/3}/200)$ for the difference. Here $\int_0^\infty t^j e^{-t^{2/3}/c}\,dt=(3/2)c^{3(j+1)/2}\Gamma(3(j+1)/2)$. The large-frequency contribution is below $10^{13}/\sqrt m$ for $r\le2$, and the multiplier contribution is below $5\cdot10^{14}/s$. Also $(1+T)^4\le2(100\log m)^6$ for $m\ge2$. These estimates give (1), since the multiplier term for $m\ge2$ costs at most $2.5\cdot10^{14}/\sqrt m$. Finally $(1+\log m)^6m^{-1/4}\le24^6e^{-23/4}<10^6$.

## Locating every global maximum at every size

For $n\ge2$, every maximizing corank $k$ satisfies
$$s/5000< k<7s.$$
First the [area tail bound](finite-reduction.md#exact-area-moments) at $x=2$ gives $\max P_m\ge(1-e^{-2})/(2s+1)>.3/s$. The Fourier envelope gives $\sup|\Delta P_m|\le10^7/s^2$ by integrating $8t e^{-t^{2/3}/100}/(\pi s^2)$ over $t>0$. On either side of a maximizing index, the $\lfloor.15s/10^7\rfloor+1$ consecutive positions starting there therefore carry at least $2.25\cdot10^{-9}$ mass, including the maximum itself. At $x=7$ the upper tail is at most $2e^{-49/2}/7<2.25\cdot10^{-9}$, proving the upper bound.

For the lower tail take $n\ge1600$, $H=\sqrt{n/1600}$ and $\beta=H^{-3}$. We use the [real transfer operator and its two boundary estimates](effective-small-area.md#complex-tilts-near-the-saddle). Its eigenvalue satisfies $\lambda\le\exp(-1/(14H^2))$. In fact put $e=2-\rho$ for the unit ground state $u$ of $T_\beta$ and $h=\lceil H\rceil$. The unweighted gradient energy is at most $e$, extending $u$ by $u_{-1}=0$. Hence $\sum_{j<h}u_j^2\le h(h+1)e/2\le3H^2 e$ by telescoping from $-1$. For $j\ge h$ the potential $2-t_{j-1}-t_j$ is at least $1-\exp(-1/(2H^2))\ge1/(4H^2)$, and its mean is at most $e$ by the weighted Dirichlet form. Thus $1\le7H^2e$ and $1-\lambda=(2+\rho)e/4\ge e/2$.

With $l=\lceil H^2\rceil$, the boundary estimates give $\mathbb E[{\bf1}_A e^{-\beta K}]\le(10/H)\lambda^{n-2l}$. Exponential Markov and division by the survival probability yield
$$
\Pr(K\le s/5000\mid A)
\le20\sqrt{4800}\exp\!\left(\frac{4800^{3/2}}{5000}-\frac{1600-4}{14}\right)
<10^{-17}.
$$
Here $m/H^2\le4800$ and $2l/H^2\le4$. This contradicts the one-sided mass at a maximizer if $k\le s/5000$. For $2\le n<1600$ the [row-end counting bound](monotonicity.md#3-decrease-near-the-top) gives $k\ge\lceil(n-1)/2\rceil>s/5000$. At $n=1$ the empty corank can attain the maximum, so the strict lower bound needs the size restriction.

## A bound for the largest coefficients before global unimodality is known

At every $m\ge10^{90}$ the ranks attaining at least half the maximum form an interval, and the sequence is strictly log-concave throughout that interval, including its endpoints. In particular there are at most two maximizing ranks, adjacent in case of a tie.

Indeed $E_m<10^{-16}$ at $10^{90}$ and decreases thereafter. The Fourier envelope bounds the density and its first two derivatives by $10^{11}$, and its third derivative by $10^{15}$, by integration as above. If $k_1\le k_2$ and $sP_m(k_i)\ge1/8$, then $f(k_i/s)\ge1/9$ and log-concavity gives that lower bound throughout their interval. Apply (1) to the exact identity
$$
P_m(k)^2-P_m(k-1)P_m(k+1)
=\Delta P_m(k-1)\Delta P_m(k)-P_m(k)\Delta^2P_m(k-1).
$$
After multiplication by $s^4$, the error from replacing the right side by $f'^2-ff''$ at $k/s$ is at most $12\cdot10^{11}(E_m+10^{15}/s)$, using the derivative bounds to shift the arguments by one lattice spacing. The limiting expression is at least $12f^2\ge12/81$ by [strong log-concavity](peak-window.md#curvature-of-the-limiting-density), so the discrete determinant is strictly positive throughout. The [first area moment](finite-reduction.md#exact-area-moments) is below $1/2$, hence more than half the limiting mass belongs to $[0,1]$. Some point has density above $1/2$. Taking a grid point within $1/s$ gives $s\max_kP_m(k)>.49$ by (1). Thus the extremal indices at half the maximum satisfy the two-endpoint test, proving the interval assertion. It leaves open the possibility of smaller local peaks outside this interval at sizes below the global threshold.

There is also a rate for the mode. At a maximizing $k$, the forward difference is nonpositive and the backward difference nonnegative. Applying (1) at both sites yields $|f'(k/s)|\le E_m+10^{15}/s$. Since $f(k/s)>.48$ and $(\log f)''\le-12$, the unique limiting mode $x_*$ satisfies
$$|k/s-x_*|\le (E_m+10^{15}/s)/5 \qquad (m\ge10^{90}).$$
In particular $.19<k/s<.75$ there. To see the numerical bounds, $(x_*-x)f'(x)$ is a probability density by unimodality and integration by parts. Its mean and second moment are $2\mu-x_*$ and $3\mathbb E Y^2-2x_*\mu$, where $\mu=\mathbb E Y$. Nonnegative variance gives $|x_*-\mu|\le\sqrt{3\operatorname{Var}Y}$. The [exact moments](finite-reduction.md#exact-area-moments) $\mu=3\sqrt{2\pi}/16$ and $\mathbb E Y^2=59/240$ put both endpoints strictly inside $(.19,.75)$ with margin exceeding $.001$.
