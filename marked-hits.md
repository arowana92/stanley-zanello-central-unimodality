# Marking a vertex before the first hit

Let $m=2n$ for the odd-part staircase and $m=2n+1$ for the even-part staircase. Write $D=\lfloor m^2/4\rfloor$, $s=m^{3/2}$, $j$ for rank, $k=D-j$ for corank and $a_j$ for the rank count. For both families and every $n$ the following assertions hold.

1. $a_{j+1}>a_j$ when $j\ge D/2$ and $k\ge 3s/5$.
2. $a_j^2>a_{j-1}a_{j+1}$ when $j\ge D/2$ and $k\ge 3s/4$.
3. Every global maximum has $k<3s/5$. Every coefficient at least half the maximum has $k<18s/25$.

Together with the [small-corank inequality](folded-saddle.md), the first assertion confines the missing adjacent comparisons to the interval between $s/35$ and $3s/5$, up to the steps at its endpoints. The peak may be inside this interval. Establishing a single change of sign there for the outstanding sizes would finish the conjecture.

## An excursion with a marked vertex

Let $H$ be a uniform Dyck path of length $2d$ and let $I$ independently select one of its $2d+1$ vertices uniformly. Its height has the exact tail
$$
 \Pr(H_I\ge b)=\frac{\binom{2d+1}{d-b}}{\binom{2d+1}{d}}
 \le e^{-b(b+1)/(d+1)},\qquad b=0,1,\ldots .
 \tag{1}
$$
A binomial coefficient with negative lower index is zero. At a mark at height $b$, the prefix and the reversed suffix each end at $b$. Cutting at the final up-crossings of levels $0,\ldots,b-1$ splits each into $b+1$ Dyck paths and $b$ up-steps. With $C=1+zC^2$ the number of marked paths at height exactly $b$ is
$$
 [z^{d-b}]C^{2b+2}
 =\frac{b+1}{d+1}\binom{2d+2}{d-b}
 =\binom{2d+1}{d-b}-\binom{2d+1}{d-b-1}.
$$
The first equality is the coefficient formula from Lagrange inversion. Summation proves the identity. The ratio has factors $(d-j)/(d+j+2)$ for $0\le j<b$. Bound each by $\exp[-2(j+1)/(d+1)]$.

A fair walk first hitting $-1$ at $t=2d+1$ consists of such an excursion followed by one down-step. Give its signs $X_i$ the independent natural parameters $u_i=\lambda(t+1-2i)/(4s)$, so a sign has probability proportional to $e^{u_i X_i}$. Summation by parts on a hit gives
$$
 \sum_{i=1}^t u_iX_i=\frac{\lambda(t-1)}{4s}
                +\frac{\lambda}{2s}\sum_{i=0}^{t-1}H_i .
$$
For $\lambda\ge0$ put $y=\lambda t\sqrt{d+1}/(2s)$. Jensen's inequality over the marked vertex, then (1) and integration of the tail, give
$$
 \mathbb E_{\rm exc}\exp\left(\frac{\lambda}{2s}\sum_{i=0}^{t-1}H_i\right)
 \le 1+y\int_0^\infty e^{yw-w^2}\,dw
 \le e^{y^2/4}\left[1+\frac y2(\sqrt\pi+\min(\sqrt\pi,y))\right].
 \tag{2}
$$
Indeed $\Pr(H_I>x)\le e^{-x^2/(d+1)}$, and the integral from $-y/2$ to zero of $e^{-w^2}$ is bounded by both $y/2$ and $\sqrt\pi/2$.

The first-hit mass under these parameters is at most the fair mass times the right side of (2), times $e^{\lambda(t-1)/(4s)}/\prod_i\cosh u_i$. For $t>1$ the fair mass is $2^{-t}C_d<.8/(t-1)^{3/2}$ by Wallis. The denominator matters even though the parameters sum to zero. Integrating $\tanh u\ge u-u^3/3$ yields
$$
 \sum_i\log\cosh u_i \ge \frac{\lambda^2 t(t^2-1)}{96s^2}
          \left(1-\frac{\max_i u_i^2}{6}\right).
 \tag{3}
$$
These bounds apply to individual first hits at arbitrary length.

Lean proves (1) by a bijection. For a path marked at height $h$, keep its prefix, insert an up-step and traverse the suffix backwards with every step reversed. The result is a ballot path ending at $2h+1$. Its last up-step out of height $h$ recovers the mark. A height of at least $b$ corresponds to at most $d-b$ down-steps, so the ballot triangle telescopes to the numerator in (1). The kernel then checks Jensen's inequality on the $2d+1$ vertices, integration against the Gaussian tail, and the lower bound on the product of hyperbolic cosines. With $c=\lambda/(2s)$, the resulting theorem bounds the actual probability of the first hit at $t=2d+1$ for independent signs with natural parameters $c(d-i)$ at zero-based step $i$. It includes the fair prefactor $2^{-t}C_d$ and the shift $e^{cd}$. [Marked paths](CentralUnimodality/MarkedExcursion.lean) · [Gaussian integral](CentralUnimodality/MarkedAreaIntegral.lean) · [Tilted first-hit bound](CentralUnimodality/MarkedHitBound.lean)

The independent exact check chooses $c=\log 2$. It compares an absorbing walk on heights with the tilted area sum obtained by direct Dyck path enumeration. The remaining estimates in the sections below combine individual first hits with an independent suffix and bound their combined contribution to the staircase differences. Lean also proves the exact change of tilt on any rank event and the identity transferring the centered hit mass to the original length-$m$ tilted walk. In that law the comparison $e^{-2c}P(S=j,E_m)<P(S=j+1,E_m)$ is equivalent to $a_j<a_{j+1}$. [Rank and prefix identities](CentralUnimodality/RankTilt.lean)

## The maximum at finite size

Let $P(k)=a_{D-k}/\binom m{\lfloor m/2\rfloor}$. For $m\ge256$, $s\max P>1.805$. In the [exact variance argument](mode-bounds.md#height-of-the-maximum-from-the-exact-variance) use $\ell\ge128$ and $C^2\ge\pi\ell$. After division by $\ell^3$ the two numerator bounds have positive coefficients in $1/\ell$. Their maximum and the smallest allowed $m/\ell=2-\delta/\ell$ can be evaluated at $\ell=128$. The variance bound for a density bounded by $\max P$ gives the claimed number.

Tilt the independent rank sum by $e^{-6S/s}$, retain survival for $L=\lceil m/10\rceil$ steps, then bound the remaining point probability. The suffix has $B\ge229$ labels, single-label drift at most $3/16$ and Bernoulli variance at least $p=(1-9/256)/4$. The [Gaussian comparison for an independent suffix](rising-window.md#prefix-and-suffix-estimates) gives supremum at most $.410/\sigma_B$, with $\sigma_B/s\ge z=\sqrt{p(.9-1/256)^3/3}$. Fair survival for $m$ steps is at least $.79/\sqrt m$ by Wallis, using $\sqrt{2/(\pi(m+2))}$ for either parity.

For the prefix couple to homogeneous drift $d_0=3/\sqrt m$. Its escape probability is $2d_0/(1+d_0)$. At first-hit time $t$ the likelihood relative to fair is $e^{-u}/\cosh^t u\le e^{-d_0^2t/2}$, $u=\operatorname{arctanh}d_0$. For $iL<t\le(i+1)L$ bound this by $e^{-ix}$, $x=9/20$, and use the bound at $i=20$ for the final tail. The fair survival probabilities satisfy $P_0(E_L)\le.8/\sqrt L$ and $P_0(E_{iL})\ge.78/\sqrt{iL}$ for $i\ge2$, since $2L\ge52$. Summing the differences gives the upper bound $6/\sqrt m+R/\sqrt L$ on prefix survival, where
$$
 R=.8e^{-x}-.78\sum_{i=2}^{20}(e^{-(i-1)x}-e^{-ix})/\sqrt i .
$$
Undoing the tilt costs at most $e^{c-6k/s}$ with $c=36(1+1/256)(2+1/256)/48$ by Hoeffding. Thus
$$
 sP(k)\le \frac{.410}{z}\frac{6+\sqrt{10}R}{.79}e^{c-6k/s}.
$$
The bound is below $1.805$ at $k/s=3/5$ and below $1.805/2$ at $18/25$. The verifier checks every coefficient at the smaller sizes. This proves assertion 3 independently of the adjacent-sign estimates.

## The signed contribution of a first hit

For $m\ge4096$ and $k\le 2s$ use the notation of the [separate-tilt proof](hit-tilts.md). Under tilt $e^{-\gamma S/s}$ the independent rank $S$ has mean $j$, with $11.99k/s\le\gamma<25$. Keep a prefix of length $L=\lceil lm\rceil$ and put $P=\Pr_\gamma(E_L)$ and $\sigma$ equal to the standard deviation of its free suffix. For a surviving event $A\subset E_L$ use mass $F(j)=\Pr_\gamma(S=j,A)/P$. The two tests are positivity of $\sigma^2(F(j+1)-e^{-\gamma/s}F(j))$ and negativity of $\sigma^3(F(j-1)-2F(j)+F(j+1))$. The latter implies strict log-concavity by the arithmetic-geometric mean inequality. Take $l=3/40$ for the first test and $l=1/16$ for the second. Formulae (2) and (3) of the separate-tilt proof bound the conditional prefix second moment and both initial tests for $A=E_L$.

Subtract the mass of paths with a first hit after $L$. For $L<t\le T=\lceil hm\rceil$, use a separate rank shift $\Delta\ge0$, $\lambda=\gamma+\Delta$, and remove the mean natural parameter on the first $t$ signs. Formula (6) of the separate-tilt proof bounds the joint likelihood cost. The remaining first-hit law has precisely the parameters in (2)–(3). As a second upper bound on that hit probability, take $\lfloor t/c\rfloor$ steps at each end with $c\in\{3,5,8\}$. Bound the two outer survivals against homogeneous walks of drift $b/\sqrt m$, where $b\ge\lambda t/(4m)$. For an outer section of at least $um$ steps *after reserving the initial reverse up-step*, survival costs at most $(2b+.8e^{-b^2u/2}/\sqrt u)/\sqrt m$ by the same homogeneous likelihood calculation. Multiply by $(1/2+b/128)$ for that initial step.

The remaining middle displacement is prescribed. For $J\ge80$ independent signs with Bernoulli variances at least $.238$, the maximal point probability is below $.831/\sqrt J$. The span-two Fourier integral is bounded by $(2/\pi)\int_0^{\pi/2}\exp[-2pJ\sin^2 v]dv$. On $x=\sin v\le3/5$ use $(1-x^2)^{-1/2}\le1+x^2$ and extend the Gaussian integral to infinity. The remaining integral is at most $e^{-2pJ(3/5)^2}$. The resulting scaled bound is
$$
 \frac{1+1/(4pJ)}{\sqrt{2\pi p}}+\sqrt J e^{-2pJ(3/5)^2}.
$$
It decreases over the stated range. This also gives $.84/\sqrt J$ for $p\ge.235$, $J\ge255$. The recentered middle signs satisfy the first variance bound.

For the independent suffix after $t$ write $z_B=\sigma_B/s$. At orders $0,1,2$ the scaled approximation by the standard normal density $\varphi$ and its derivatives has uniform absolute error at most $.007,.0138,.030$. To check this, split $B\ge255$ at $512,1024,2048,4096$. In a bin with upper end $b$ use drift bound $(57/128)\min(b/4096,1)$, since $m\ge4096$. Apply the independent-suffix comparison above with these drift and variance bounds. Include the forward and centered lattice-multiplier errors, bounded under the Gaussian integral by $|x|^2/(2\sigma_B)$ and $|x|^4/(12\sigma_B^2)$ respectively.

For the first sign test, after changing the tilt, the signed contribution is at most $1.001$ times the supremum of the scaled forward difference plus $(1-e^{-\lambda/s})$ times the scaled mass, taken at a common location. In units of $\sigma_B^{-2}$ this is bounded, before the factor $1.001$, by
$$
 M(w)+.0138+.007w,\qquad
 M(w)=\frac{w+r}{\sqrt{2\pi}}e^{-r^2/2},\qquad
 r=2/(\sqrt{w^2+4}+w),\quad w=\lambda z_B .
$$
Indeed $M(w)=\max_y(|\varphi'(y)|+w\varphi(y))$. After division by $z_B^2$ each term in this maximization decreases in $z_B$, so we may use the lower bound for $z_B$ throughout. For curvature put $u=\Delta/s$ and $w=\sigma_Bu$. The tilted second-difference operator is exactly
$$ e^{-u}D_2+2\sinh(u)D_1+2(\cosh u-1)I. $$
After taking out $e^{-u}$ its normal approximation on the $\sigma_B^3$ scale is
$$
 \varphi''+2h_1\varphi'+q\varphi
 =[(y-h_1)^2-1+q-h_1^2]\varphi(y),\quad
 h_1=\sigma_B(e^{2u}-1)/2,\quad q=\sigma_B^2(e^u-1)^2 .
$$
For $0\le u\le32/4096^{3/2}$, $h_1\le1.001w$, $q\le1.001w^2$ and $h_1^2-q=q((e^u+1)^2/4-1)<.0002w^2$ when $u>0$. Adding the three independent-suffix errors bounds the negative part of the scaled operator by $.429+.028w+.0072w^2$. Division by $z_B^3$ makes this majorant decreasing in $z_B$ as well.

For the sum over odd $t$, replace each point by its interval $((t-1)/m,(t+1)/m]$ of length $2/m$. These intervals are disjoint and lie in $[l,h+2/4096]$. In a bin $[v,w]$ bound all parameters using $v-1/4096\le t/m\le w+1/4096$, and multiply the scaled first-hit bound by $(w-v)/2$. This accounts for integer rounding at the two ends without paying for extra hit times in every bin.

## Reflection after the last cut

For $E_T$ and a subsequent hit keep the endpoint $H_T=y$ of the complex prefix row. Read $N=m-T$ further steps. Coupling their nonnegative drifts to fair signs and reflecting a fair walk at its first visit to $-(y+1)$ bounds the hit probability by $2\Pr_0(S_N^*\ge y+1)$, where $S_N^*$ is a sum of fair signs. In this paragraph $u=a/\sqrt m>0$ is a height tilt. Under the homogeneous tilt by $e^{uS_N^*}$ let $p_{\max}$ be the largest endpoint probability. Summing over endpoints of one parity gives
$$
 2\Pr_0(S_N^*\ge y+1)
 \le e^{-uy+Nu^2/2}\frac{2e^{-u}p_{\max}}{1-e^{-2u}}
 \le e^{-uy+Nu^2/2}\frac{p_{\max}}{u}.
$$
Here $p_{\max}<.84/\sqrt N$ by the preceding point bound, since $N\ge255$ and the trial tilts have $u\le.24$. The exponential maximal inequality gives the same bound with the prefactor one. Thus the joint late-hit likelihood in (7) of the [separate-tilt proof](hit-tilts.md#hits-after-the-cut) gains the factor $\min(1,.84/(a\sqrt{1-h-1/4096}))$. In its auxiliary prefix law, survival through $L$ is bounded against a homogeneous walk as in the preceding section, including the exponential discount on the fair late first-hit tail.

It remains to smooth the middle $T-L$ steps of the complex prefix row, with survival imposed. In an even block of $N'$ labels pair the first with the last, then work inwards. At harmonic $j=1,2$ and lattice frequency $\theta$, the unrestricted sum of endpoint moduli is at most
$$
 \rho_j=\exp\left(-.20\sum_{d=1,3,\ldots,N'-1}\sin^2(jd\theta/2)\right).
$$
Indeed a mixed pair of separation $d$ has two probabilities $A,B$ for its orders. Fixing the displacement of every pair fixes the endpoint. Squaring its two-term transform shows a loss at least $2AB\sin^2(jd\theta/2)/(A+B)$ in the modulus sum. The coefficient is at least $.20$ for the down probabilities in $[.36,.62]$, as in the [paired-label bound](rising-window.md#fourier-bound-for-a-hit-after-the-cut). For an arbitrary subset retained by the wall, rotate each endpoint phase to make its retained sum real and nonnegative. The upper bound
$$ (\cos x)_+\le 3/8+(\cos x)/2+(\cos 2x)/8 $$
gives block row norm at most $3/8+\rho_1/2+\rho_2/8$. This bound multiplies over blocks, uniformly in the entering height.

For $0\le t=s|\theta|\le4096$ the verifier integrates over bins $[v,w]$. It tries $b=1,\ldots,64$ blocks of equal largest even length fitting in $T-L$. With $\epsilon=1/4096$, the scaled block length lies between $W=(h-l-\epsilon)/b-2\epsilon$ and $(h-l+\epsilon)/b$. Put $U=w(h-l+\epsilon)/(128b)$. When $W>0$ and $U\le1.4$, a lower bound on $-\log\rho_j$ is
$$
 .20\,j^2v^2(W^3-W\epsilon^2)(1-(jU)^2/6)_+^2/24
$$
provided $W^3-W\epsilon^2>0$. This uses $\sum d^2=N'(N'^2-1)/6$, $\sqrt m\ge64$ and the sine Taylor bound. Raise the resulting block bound to power $b$ and take the best valid bound in each bin. Multiplication by $\int_v^w t^i\,dt$ then bounds the integral for difference order $i$.

For the rest of $|\theta|\le1/8$ pair the two halves of a block at fixed separation $L'=\lceil3.5|\theta|^{-2/3}\rceil$. Here $L'|\theta|/2\le15/16$ and $L'|\theta|^{2/3}\le3.75$. The same two-harmonic bound, now with $L'$ pairs of that separation, gives block norm at most $e^{-.65}$. Taking whole blocks gives $2e^{-c t^{2/3}}$ with $c=.65(h-l-\epsilon)/7.5$. Beyond $t=4096$ use $x=ct^{2/3}$ and $x^{b-1}\le x_0^{b-1}\exp((b-1)(x/x_0-1))$ for $b=3(i+1)/2$ and $x_0=256c$. On $|\theta|\ge1/8$ use the [four full-period arc bounds](rising-window.md#fourier-bound-for-a-hit-after-the-cut).

Let $I_i$ denote the resulting integrals including the factor $(\sigma/s)^{i+1}/\pi$. For the signed first difference the cost is at most $1.001(I_1+\lambda(\sigma/s)I_0)$. For the second difference take the smaller of the earlier one-sided bound and $I_2+1.001(\Delta\sigma/s)^2I_0$. Indeed the absolute value of $e^{v+i\theta}+e^{-v-i\theta}-2$ is exactly $2(\cosh v-\cos\theta)$ with $v=\Delta/s$.

## Signs and reproduction

Use $h=37/40$ for both tests. The [verifier](verify_marked_hits.py) uses rational outward bounds throughout the inequalities. It tests bins of width at most $1/8$ in $\gamma$, starting at $11.99\cdot3/5$ for growth and $11.99\cdot3/4$ for curvature. For each term it selects the least upper bound over the listed rank shifts. The positive lower bounds for the normalized growth test and the negated curvature test are $.012$ and $.032$, respectively. The growth bins extend to $9$ and the curvature bins to $11.25$. Above those values, the existing [sign certificate](hit-tilts.md#signs-and-reproduction) applies to every $\gamma\le25$ in its respective parameter range. At $k\ge2s$ the [first-passage theorem](rising-window.md) covers both signs. These estimates prove assertions 1–2 for $m\ge4096$.

Below $m=4096$ the [finite curvature certificate](certified-window.md) gives strict log-concavity throughout the upper half for $n\ge9$. Assertion 3 puts every maximizing rank strictly above each rank in assertion 1, giving strict increase there. For $n<9$ these rank ranges are empty.

~~~sh
python3 -B verify_marked_hits.py
python3 -B verify_hit_tilts.py
python3 -B verify.py --max-n 64 --direct-n 12 --upper-curvature
~~~

The first command also enumerates all Dyck excursions through semilength ten and checks (1) at every height. It evaluates both staircase rows exactly through $n=127$, including 444,705 strictly increasing steps and 382,374 positive log-concavity determinants in the stated ranges. Direct strict-partition enumeration through $n=12$ checks each coefficient independently. The last command also compares with the Catalan recurrences and reproduces the published four-row valley for the separate shape $(9,7,5,3)$.
