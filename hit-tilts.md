# Separate tilts for paths that hit the ballot boundary

For the two central staircases write $m=2n$ or $2n+1$, $D=\lfloor m^2/4\rfloor$, $s=m^{3/2}$ and $k=D-j$. Let $a_j$ be the number of strict partitions of rank $j$. For every $n$, at every integer $j\ge D/2$ in the indicated ranges,
$$
\begin{aligned}
 a_{j+1}>a_j &\qquad (k\ge 3s/4),\\
 a_j^2>a_{j-1}a_{j+1} &\qquad (k\ge 15s/16).
\end{aligned} \tag{1}
$$
In particular a possible failure of unimodality in either family is confined, up to the adjacent indices at the two ends, to $s/35\le k\le 3s/4$. The other two all-size inputs are [strict growth at small corank](folded-saddle.md) and [weak growth below the middle rank](monotonicity.md#1-lower-half-for-all-sizes). The normalized margins in the proof are uniform over the previously unverified sizes.

For $m<4096$ use [the finite strict upper-half curvature certificate](certified-window.md) and the [global peak bound $k<.65s$](mode-bounds.md). Strict log-concavity on the upper half and a maximum strictly above the stated rank interval give the first inequality. At $n<9$ both intervals are empty. For $k\ge2s$ both conclusions follow from the [earlier first-passage bounds](rising-window.md). Take $m\ge4096$ and $k\le2s$ below.

## Choice of law and prefix variance

Take independent signs $X_r=+1,-1$ with natural parameter $g r/(2s)$, so their probabilities are proportional to $\exp(g r X_r/(2s))$. Read $r=m,\ldots,1$. The rank is $S=\sum_r r(1-X_r)/2$, and the admissible paths are those whose heights never become negative. Write $E_t$ for survival through time $t$ and $\tau$ for the first visit to $-1$. Let $Z(g)=\prod_{r=1}^m(1+e^{-gr/s})$ be the partition function in rank coordinates. Choose $\gamma$ by $\mathbb E_\gamma S=j$. Throughout the range of interest
$$ 11.99\,k/s\le\gamma<25. $$
In fact $\mathbb E_0 S>D$, and the derivative in $g$ has absolute value at most $\sum r^2/(4s)$. At $g=25$, use $\tanh u\ge u-u^3/3$, $\sum r^2\ge m^3/3$ and $\mathbb E_0 S-D\le(m+1)/4$ to put the mean below $D-2s$.

Put $l=1/10$ for growth and $l=1/14$ for curvature, $L=\lceil lm\rceil$, $M=m-L$, and $\sigma^2=\operatorname{Var}_\gamma(\sum_{r\le M}r(1-X_r)/2)$. Let $P=\Pr_\gamma(E_L)$, $d_0=\tanh(\gamma/(2\sqrt m))$, $f=l+1/4096$, and let $U$ be the contribution of the first $L$ steps to $S$. The minimum prefix drift is at least $(1-f)d_0$ by concavity of $\tanh$. With $G(d)=2d/(1+d)$ the probability of never hitting $-1$ at homogeneous drift $d>0$, this gives $P\ge G((1-f)d_0)$.

We use the following bound with $z=\sigma/s$, $\kappa=d_0\sqrt m$, and $Y=(\mathbb E_\gamma U-U)/\sigma$:
$$
 \mathbb E_\gamma(Y^2\mid E_L)\le V=
 \frac{f+\dfrac{1+d_0}{1-f}\big(f^2+1/(2\kappa^2)\big)}{4z^2}. \tag{2}
$$
To prove it let $U_t$ denote the prefix contribution through $t\le L$. Conditional on the path through a first hit at $t$, the rest of the prefix is independent. Subtract its contribution to the unconditional second moment about $\mathbb E_\gamma U$. This gives
$$
 P\,\mathbb E_\gamma[(U-\mathbb EU)^2\mid E_L]
 =P\operatorname{Var}_\gamma U+
 \sum_{t\le L}\Pr_\gamma(\tau=t)
 \left(\operatorname{Var}_\gamma U_t-
 \mathbb E_\gamma[(U_t-\mathbb EU_t)^2\mid\tau=t]\right),
$$
where zero-probability terms are omitted. Bound $\operatorname{Var} U_t\le tm^2/4$. The truncated first moment of $\tau$ in the sum equals $\sum_{t=0}^{L-1}(\Pr(E_t)-P)$. By coupling the prefix from above with homogeneous drift $d_0$, this is at most
$$ L\big(G(d_0)-G((1-f)d_0)\big)+1/d_0\le 2Lf d_0+1/d_0 . $$
Indeed the homogeneous walk conditional on an eventual hit has drift $-d_0$ until hitting and expected hitting time $1/d_0$. The likelihood ratio between the two homogeneous walks on a first hit is constant since their final height is $-1$. The mean under negative drift follows by summing the stopped drift identity, with an exponentially decaying survival tail by Hoeffding's inequality. Divide by $P\ge 2(1-f)d_0/(1+d_0)$ to obtain (2).

Denote the rank mass conditioned on $E_L$ by $F_L$. Write $D_1G(j)=G(j+1)-G(j)$ and $D_2G(j)=G(j+1)+G(j-1)-2G(j)$. The remaining $M$ independent labels give
$$
 \begin{aligned}
 \sigma F_L(j)&\ge .3989 e^{-V/2}-.005,\\
 \sigma^2|D_1F_L(j)|&<.25,\\
 \sigma^3D_2 F_L(j)&\le \varphi(0)\big(V/(1+V/2)-e^{-V/2}\big)+.010 ,
 \end{aligned} \tag{3}
$$
where $\varphi$ is the standard normal density. To check the constants, use the [Bernoulli Fourier comparison](rising-window.md#prefix-and-suffix-estimates) with $M\ge3685$, $p_r(1-p_r)>.24$ and maximum drift at most $25/128$. In the error integral with multiplier power $i=0,1,2$, integrate the same cubic and quartic error against $|x|^i$. The resulting errors relative to $\varphi^{(i)}(Y)$ are below $.005,.007,.010$. For the order-one forward multiplier its difference from the derivative costs at most $\int |x|^2e^{-x^2/2}dx/(4\pi\sigma)<.0001$. The corresponding centered second-difference cost is smaller. Use $\|\varphi'\|_\infty<.2421$, Jensen for $\mathbb E e^{-Y^2/2}$, and concavity of $w/(1+w/2)$ for $\mathbb E(Y^2e^{-Y^2/2})$.

Lean proves (2) for the finite word law. At a constant positive parameter $u$, the finite-horizon survival from distance $a$ above the absorbing boundary equals $1-\rho^a+\rho^a P_{-u}$, where $\rho=e^{-2u}$ and $P_{-u}$ is survival from the same distance under the opposite drift. A finite recursion bounds the expected hitting time truncated at any horizon by $a/\tanh u$ under that opposite drift. Comparing every prefix parameter with its two endpoints and summing the first-hit probabilities with their time weights gives the required correction to the second moment. The centered square of the prefix rank minus its unrestricted variance has zero mean at every step. Stopping it at the first hit gives the bound on the actual surviving words. The theorem permits any $0\le f<1$ with $L\le fm$ and any positive scale $\sigma$. An independent exact enumeration checks the stopped-square identity and the bounds at all 65 cuts of lengths 1 through 10 using $c=\log(5/4)$. [Prefix survival](CentralUnimodality/TiltedPrefixSurvival.lean) · [Stopped variance](CentralUnimodality/StoppedPrefixVariance.lean) · [Normalized bound](CentralUnimodality/ConditionalRankVariance.lean) · [Exact word check](verify_marked_hits.py)

For (3), Lean proves the convolution of the surviving prefix and the independent suffix on integer ranks, including the zero tails. At a saddle rank $j$ the displacement of the suffix site from its mean equals the negative centered prefix rank. The conditional second moment from (2) then bounds the Gaussian mixture and its curvature. The theorem `conditional_prefix_differences` gives all three constants in (3) when the unrestricted suffix has uniform errors at most $.005,.007,.010$ for its scaled mass, forward difference and centered second difference. Proving those errors by Fourier inversion is still required. [Rank convolution and centering](CentralUnimodality/PrefixRankMixture.lean) · [Gaussian inequalities](CentralUnimodality/GaussianMixtureBounds.lean) · [Three difference estimates](CentralUnimodality/PrefixDifferenceBounds.lean)

## Changing the label tilt for a discarded path

For $\lambda=\gamma+\Delta$ put
$$ R_\Delta=\frac{Z(\lambda)}{Z(\gamma)}\,e^{\Delta j/s}. $$
A rank mass at $j+b$ under $\gamma$ equals $R_\Delta e^{\Delta b/s}$ times its mass under $\lambda$, for any fixed event. We apply this to discarded paths, keeping the denominator $P$ from the original law throughout. The height at time $t$ is $H_t$. Define
$$ v_t=t/m,\qquad c_t=\sum_{r>m-t}r/m^2=v_t(1-(t-1)/(2m)),\qquad C_2=\sum r^2/m^3. $$
The cost of changing both the rank and the height parameters satisfies, for $a\ge0$,
$$
 R_\Delta\mathbb E_\lambda e^{-aH_t/\sqrt m}
 \le \exp\left(\frac{\Delta^2C_2}{8}+
          \frac{a^2 v_t}{2}-a(\kappa+\Delta/2)c_t\right). \tag{4}
$$
Under the $\gamma$ law the left side is $\mathbb E_\gamma\exp[-\Delta(S-j)/s-aH_t/\sqrt m]$. Its mean exponent is $-a\mathbb E_\gamma H_t/\sqrt m\le-a\kappa c_t$. Each centered sign has log moment generating function at argument $w$ at most $w^2/2$. Summing the squares of the combined sign parameters gives the cross term $-a\Delta c_t/2$. Keeping this term makes late hits much cheaper than an estimate at a common label tilt.

If a discarded mass, including $R_\Delta/P$, has scaled bounds $A_0,A_1,A_2$ on its mass and its first and second differences under $\lambda$, the costs under $\gamma$ needed here are at most
$$ A_0,\quad 1.001 A_1+1.001\Delta z A_0,\quad A_2+2.002\Delta z A_1. \tag{5}
$$
The first difference needs an upper bound, the second a lower bound with a minus sign. The factors at shifts $\pm1$ are $e^{\pm u}$, $u=\Delta/s$, and $0\le\Delta\le32$. In the centered second difference the extra $(\cosh u-1)(F_++F_-)$ is nonnegative and the cross term is $\sinh u\,(F_+-F_-)$. This proves (5), including when different tilts are chosen for the three orders.

## First hits through the cut

Take $h=15/16$, $T=\lceil hm\rceil$. First suppose $L<t=\tau\le T$. Remove the mean natural parameter on the first $t$ signs under $\lambda$ by taking $a=\lambda c_t/(2v_t)$ in (4). The resulting signs in this prefix have natural parameters decreasing linearly from $\lambda(t-1)/(4s)$ to its negative. On a hit the factor $e^{aH_t/\sqrt m}$ restoring the prefix law is at most one. For $v_t\in(v,e]$ the joint normalization costs at most
$$
 \exp\left(\Delta^2 C_2/8
       -v(1-e/2)^2(\gamma+\Delta)
                     \big(\gamma(1-\gamma^2/(6m))+\Delta\big)/8\right). \tag{6}
$$
Indeed $\kappa\ge(\gamma/2)(1-\gamma^2/(12m))$, and substituting $a$ into (4) gives the estimate. The suffix still has its independent $\lambda$ law.

To bound the hit probability under the recentered prefix, take $\lfloor t/3\rfloor$ steps at each end. At the front the path must survive. Read from the hit backwards, negating signs, and the path must be strictly positive relative to its final height. In the intervening independent block its displacement has one prescribed value once the two outer sections are given. Put $b=(\gamma+\Delta)e/4$ and $u=v/3-2/4096$. Each outer drift is bounded above by $b/\sqrt m$, also for the negated reverse signs. A homogeneous walk of drift $d\ge0$ survives $j$ steps with probability at most $2d+.8/\sqrt j$. This follows by splitting its survival into escape and eventual first hit, whose time masses are at most the fair first-hit masses, then using the Wallis bound for fair survival. The reverse path must also take its first positive step. The two outer probabilities are therefore at most
$$ (2b+.8/\sqrt u)/\sqrt m,\qquad
 (1/2+b/128)(2b+.8/\sqrt u)/\sqrt m .
$$
The middle point probability is at most $1/\sqrt{um}$. For detail, over $r\ge um\ge80$ independent signs with Bernoulli variances at least $.238$, the point bound is at most $(2/\pi)\int_0^{\pi/2} e^{-2(.238)r\sin^2 w}\,dw$ by the span-two Fourier formula. Use $\sin w\ge5w/6$ through 1 and $\sin w\ge5/6$ thereafter. The integral times $\sqrt r$ is below one. The variance bound follows from $b/\sqrt m\le57(h+1/4096)/256$. These estimates use independence across the three blocks. No factor is required for paths that may have touched the boundary in the middle.

Use successive time bins from $v=l$ to $h$, of width at most $1/80$. In the bin $(\lceil vm\rceil,\lceil wm\rceil]$ take $e=w+1/4096$. A hit time is odd, giving at most $m((w-v)/2+1/4096)$ terms. Multiply this count by (6), the three prefix bounds and $1/P$. The remaining suffix has at least $m(1-e)$ steps. Its standard deviation satisfies
$$
 \sigma'_B/s\ge \sqrt{(1-((\gamma+\Delta)(1-v)/128)^2)(1-e)^3/12}.
$$
For $B\ge255$, $\gamma+\Delta\le57$, the [independent suffix estimates](rising-window.md#prefix-and-suffix-estimates) bound its scaled norms by $.46,.46,.56$ for orders $0,1,2$. Here every down-indicator variance is greater than $.196$. Multiply the bounds by $(\sigma/\sigma'_B)^{i+1}$, apply (5) and sum over bins. This bounds the three scaled contributions of first hits through $T$. Choosing $\Delta$ separately in each bin uses exact change of measure throughout.

## Hits after the cut

On a path surviving to $T$, the probability of a later hit from height $y$ under $\lambda$ is at most $\exp[-ay/\sqrt m+(m-T)a^2/(2m)]$. The future signs have nonnegative drift, so the exponential maximal inequality gives this bound for every $a\ge0$. Combine it with (4) at $T$. If $g\le\gamma$ and $\kappa_g=(g/2)(1-g^2/(12\cdot4096))$, take $a=(\kappa_g+\Delta/2)h(1-h/2)$. The log normalizer, including the future bound, is at most
$$ \Delta^2 C_2/8-a^2/2 . \tag{7}
$$

For the Fourier estimate, condition on the endpoint $H_T$ of the surviving prefix before taking absolute values. Multiplication of that endpoint row by $e^{-aH_T/\sqrt m}$ changes its sign parameters to $\lambda r/(2s)-a/\sqrt m$. Include the survival of the first $L$ steps under this auxiliary law, of probability at most $(2(\lambda/2-a)+.8/\sqrt l)/\sqrt m$ whenever the displayed drift bound is nonnegative. Divide by $P$ as before. In the remaining $T-L$ steps use the [killed-block row bound](rising-window.md#fourier-bound-for-a-hit-after-the-cut). Its proof uses only the independent down probabilities in $[.36,.62]$. The verifier takes candidates with both $a$ and $\lambda/2-a$ bounded in absolute value by $.24\sqrt{4096}$ using their parameter bounds. For $0<|\theta|\le1/8$ the resulting envelope is $2e^{-\eta m|\theta|^{2/3}}$ with $\eta=(h-f).56/8.5$. For the four larger arcs use the rates $.013,.019,.022,.028$ from the same bound over at least $(h-f)m$ steps.

Inversion at derivative order $i$ costs the integral of this envelope times $\sigma^{i+1}|\theta|^i/(2\pi)$. The small arc contributes at most $3z^{i+1}\Gamma(3(i+1)/2)/(\pi\eta^{3(i+1)/2})$. On the larger arcs use their lengths integrated against $|\theta|^i$ and the maximum of the polynomial times exponential at $m=4096$. Multiply by the normalized survival bound and (7), then use (5). These estimates concern the rank mass jointly with a late hit and survival up to $T$.

## Lean proofs of the changes of measure

Lean proves the saddle bracket and the estimates (4)–(7) used when changing the law of a discarded path. Its sign parameter is $cr$ at label $r$, so $\gamma=2cs$, $\Delta=2zs$ for the increment $z$, and the height parameter is $b=a/\sqrt m$. The saddle theorem computes the mean from the full independent word law. For $m\ge4096$ and $0\le D-j\le2s$, it produces a nonnegative $c$ with that mean equal to $j$ and with $11.99(D-j)/s\le 2cs<25$. [Saddle theorem](CentralUnimodality/SaddleRank.lean)

For (4) the proof expands the joint change of rank and height one label at a time, retaining the cross term. A pointwise equality for each word gives the exact prefix height transform, including on a prescribed endpoint. For (6), Lean bounds the actual mass of a first hit in a length-$m$ word by the centered first-hit mass times the displayed exponential factor, uniformly in the indicated time bin. For (7), a finite-horizon induction starting at height $y$ bounds the probability of a later crossing by $\exp(-b(y+1)+(m-T)b^2/2)$. Summing over the surviving prefixes and applying the joint tilt gives (7) for the mass of the event $E_T\setminus E_m$, with $a$ chosen from the lower endpoint $g$ of the saddle bin. [Joint cost](CentralUnimodality/JointTilt.lean) · [Word and event identities](CentralUnimodality/HitTiltCost.lean) · [Bin bounds](CentralUnimodality/HitTiltBins.lean)

For (5), Lean transfers the signed forward and centered second differences on any fixed rank event. With $u=\Delta/s\le1/8192$, the forward error costs at most $1.001$ times the changed forward difference in absolute value plus $1.001u$ times the changed center mass, all at the common normalizer $R_\Delta$. The second-difference lower bound loses at most $1.001u$ times the sum of the two adjacent absolute differences. Multiplying by the powers of $\sigma$ gives (5). Strict negative second difference on the tilted ballot masses implies strict log-concavity of the integer staircase counts. Deducing (1) still requires the uniform Fourier estimates for the unrestricted suffix and the rank-resolved losses, followed by the final sign comparisons. [Signed differences](CentralUnimodality/TiltedDifferences.lean)

## Signs and reproduction

Write $F(j)=\Pr_\gamma(S=j,E_m)/P$. Subtract the two losses from $F_L$. In (3) and (5)–(7) the [rational verifier](verify_hit_tilts.py) partitions $11.99\,k_{\min}/s\le\gamma\le25$ into intervals of width at most $1/2$, using $k_{\min}/s=3/4$ or $15/16$. It bounds the increasing drift and energy factors in (6) at the lower endpoint and the error prefactors at the upper endpoint. Checks at $m=4096$ use $C_2\le(1+1/4096)(2+1/4096)/6$ and
$$
 \sqrt{(1-(\gamma/128)^2)(1-f)^3/12}
 \le z\le \sqrt{(1-l+1/4096)^3/12}.
$$
All bounds are rational with outward square-root and exponential estimates. The selected shifts belong to $\{0,1,2,4,6,9,12,16,20,24,28,32\}$. The respective conclusions are
$$
 \sigma^2\{D_1F(j)+(1-e^{-\gamma/s})F(j)\}>.107,\qquad
 \sigma^3D_2F(j)<-.069 .
$$
The first uses $1-e^{-\gamma/s}\ge .999\gamma/s$. Undoing the positive rank tilt gives strict growth. For the second, the center exceeds the arithmetic mean of the two tilted neighbors, hence also their geometric mean. The exponential tilt cancels from the log-concavity comparison. Together with the initial cases this proves (1).

For a quantitative consequence, when $m\ge4096$ and $3s/4\le k\le2s$ in the indicated upper half, $a_{j+1}/a_j>1+.75/s$. Indeed $F\le F_L\le .46/\sigma$ and $\sigma<.30s$, so undoing the tilt in the first margin adds more than $.107/(.46\sigma)$ to the ratio lower bound one.

~~~sh
python3 -B verify_hit_tilts.py
python3 -B verify_rising.py
python3 -B verify.py --max-n 64 --direct-n 12 --upper-curvature
~~~

The first command also checks 146,063 increasing steps and 108,095 strictly positive determinants on the exact rows through $n=96$. The last command compares every coefficient with direct partition enumeration through $n=12$. All-size coverage of the region between the small-corank and large-corank bounds still requires a new argument.
