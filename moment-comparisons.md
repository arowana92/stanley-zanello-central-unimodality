# Reflected comparisons from twenty area moments

**Theorem.** Let $b_k$ count partitions of corank $k$ in either central staircase with $n$ rows. Set $m=2n$ for the odd-part family and $m=2n+1$ for the even-part family, $N=\lceil m/2\rceil$, $s_0=(2N)^{3/2}$ and $d=(m+1+N)/2$. At every size, if the row is unimodal, then
$$
 b_i\le b_j\qquad(0\le i<j,\quad i+j+2d\le .524s_0). \tag{1}
$$
In particular every unimodal odd-part row has these comparisons through $i+j\le (2n)^{3/2}/2$ at $n\ge2049$, since $(3n+1)/(2n)^{3/2}<.024$. The theorem uses only the first twenty moments and interval superlevel sets. It has no approximation by a limiting area density.

**Consequence for Conjecture 3.4.** It suffices to verify unimodality in both families on the following *subsequences*, one per shape, where $s=m^{3/2}$:
$$
 2049\le n<300000,\qquad
 \lfloor .1366s\rfloor\le k\le\lceil .6s\rceil .
 \tag{2}
$$
For $n\ge4096$ the lower endpoint can be increased to $\lfloor .1378s\rfloor$. The proof tests the odd-part row before the even-part row of the same size. The window in (2) remains unverified across the indicated sizes. [Earlier size descent](size-descent.md) · [Results through 2048](certified-window.md)

## An interval test for a unimodal row

Give $K$ probabilities proportional to $b_k$. Add an independent uniform $U$ on $[-1/2,1/2]$ and put $X=(K+d+U)/s_0$. Its density is constant on each cell centered at $z_k=(k+d)/s_0$. For a unimodal row, each positive superlevel set is an interval up to its endpoints. The density is the sum of finitely many positive multiples of indicators of these intervals, by subtracting consecutive distinct heights.

Take $0<a<B<t$ and a real polynomial $Q$. Let $g(x)=(B-x)(t-x)Q(x)^2$ and let $G$ be any antiderivative. Suppose
$$
 G(t)>G(a),\qquad \mathbb E g(X)<0. \tag{3}
$$
Then $b_i\le b_j$ whenever $i<j$, $z_i\le a$, $z_j\le B$ and the row is unimodal. Indeed, $G$ increases weakly up to $B$, decreases weakly from $B$ to $t$ and increases weakly past $t$. If $b_i>b_j$, all modes precede $j$. A superlevel interval ending before cell $j$ has right endpoint below $z_j\le B$, hence nonnegative integral of $g$. Every other superlevel interval contains cell $j$ and cell $i$, since its height is at most the density in cell $j$. Its left endpoint $l$ satisfies $l\le z_i\le a$. If its right endpoint $r$ exceeds $B$, then $G(r)\ge G(t)>G(a)\ge G(l)$. If $r\le B$, monotonicity gives the same weak integral sign. Summing the layers contradicts (3).

Two choices suffice. In each row of the table take $Q$ monic with the listed roots. All decimals in this note are exact rationals.

| $a$ | $B$ | $t$ | Roots of $Q$ |
| ---: | ---: | ---: | --- |
| .262 | .355 | 1.0825 | .142, .215, .562, .716, .873, 1.010, 1.307, 1.578, 1.894 |
| .169 | .524 | .9365 | .335, 1.191 |

If $z_i+z_j\le .524$ then $z_i<.262$. Use the first row when $z_j\le .355$. Otherwise $z_i<.169$ and the second row applies, since $z_i\ge0$. The two integrals from $a$ to $t$ exceed $10^{-10}$ and $10^{-5}$, respectively. At every $N\ge96$ the expectations of the two polynomials are below $-10^{-10}$ and $-7\cdot10^{-6}$, respectively, in both families.

## Certifying a polynomial expectation uniformly in the length

Write $\delta=m\bmod 2$, so $d=(3N+1-\delta)/2$. Start with the Laurent polynomials $A_r(v)$ supplied by the two [exact Catalan moment recurrences](finite-reduction.md#exact-area-moments), where $v=(1-4z)^{1/2}$. The $z^N$ coefficient divided by $\binom{2N}N$ gives $\mathbb E K^r$ for $N\ge1$. To form the numerator of $\mathbb E(K+d)^r$, take
$$
 H_r=\sum_{j=0}^r\binom rj
       \left(\tfrac32 z\partial_z+\tfrac{1-\delta}{2}\right)^{r-j} A_j .
$$
The Euler operator sends $v^h$ to $h(v^h-v^{h-2})/2$. For the cell average, replace $H_r$ by $\sum_{l\le r,\ l\ \mathrm{even}}\binom rl H_{r-l}/(2^l(l+1))$. The verifier constructs these Laurent polynomials at all orders $0\le r\le20$ and checks that each nonconstant exponent has parity opposite to $r$ and belongs to $[-3r-1,-1]$. The constant contributes zero at $N\ge1$.

For $x=1/N$ set $S_N=4^N/(\binom{2N}N\sqrt{2N})$. After division by $s_0^r$ the resulting moment is a polynomial in $x$ at even $r$, and $S_N$ times a polynomial in $x$ at odd $r$. Indeed, if $h=-1-2a$ the normalized $z^N$ coefficient of $v^h$ is $\prod_{j=1}^a(2N+2j-1)/(2j-1)$. If $h=-2-2a$ it is $(4^N/\binom{2N}N)\prod_{j=1}^a(N+j)/j$. These follow from the binomial series. Thus the exact expectation in (3) has the form $P(x)+S_N R(x)$.

Here are details of the high-precision enclosure of the common scalar. Its consecutive ratio is $S_N/S_{N+1}=(1+x/2)/\sqrt{1+x}$. For a trial polynomial $p$ of degree $e$ compute the polynomial
$$
 (1+x)^{2e}\left[(1+x)p(x)^2-(1+x/2)^2p(x/(1+x))^2\right].
$$
Start at $p(0)=1$. For each $j=1,\ldots,9$ select the coefficient at $x^j$ to cancel the coefficient at $x^{j+1}$ in this display. The verifier solves the linear equation by evaluating at zero and one. For the resulting $p$, the ratio test is strictly negative for $p_-=p-x^{10}$ and strictly positive for $p_+=p+x^{10}$ throughout $0<x\le1/96$. It checks both polynomials are positive there. To verify a strict negative sign after removing any initial power of $x$, retain the constant and add the sum of the positive higher coefficients times their respective powers of $1/96$.

Iteration of the consecutive-ratio inequalities gives $p_-(1/N)\le S_N/S_\infty\le p_+(1/N)$, since both trial polynomials approach one and the Wallis limit $S_\infty=\sqrt{\pi/2}$ exists. At $N=8192$ the factor $\sqrt{2N}$ is the integer 128. Enclose $S_\infty$ between $S_{8192}/p_+(1/8192)$ and $S_{8192}/p_-(1/8192)$, rounding out to multiples of $10^{-23}$. This gives two rational polynomial endpoints for $S_N$. At each endpoint the same coefficient sign test gives $P(x)+S_N R(x)<0$ uniformly for $0<x\le1/96$. Since this expression is affine in $S_N$, the two endpoint checks suffice. [Exact verifier and both polynomials](verify_moment_comparisons.py)

For $N<96$ use the exact ballot rows. Put $L=\lfloor .524s_0\rfloor-2d$. The verifier checks unimodality and $b_i\le b_{L-i}$ for $i<L-i$. Unimodality then gives $b_j\ge\min(b_i,b_{L-i})=b_i$ whenever $i<j\le L-i$. The verifier also independently enumerates the strict partitions through twelve rows and integrates the powers of $X$ over their cells, checking all 21 moments for both parities.

## Induction on the staircase size

Let $E(l)$ be the sum of the $l$ smallest total degrees of distinct monomials in two variables. The ordinary Dyck polynomial $C_l$ is a sum of intervals with endpoint sums at least $E(l)$, by the [type A diagonal coinvariant theorem](excursion-centers.md#ordinary-excursions-and-two-variable-characters). We use
$$ E(l)\ge c l^{3/2}-l,\qquad c=2\sqrt2/3. $$
At $l=t(t+1)/2$ the degrees $0,\ldots,t-1$ are filled. Thus $E(l)+l=t(t+1)(2t+1)/6\ge c l^{3/2}$ by squaring $2t+1\ge2\sqrt{t(t+1)}$. Between successive triangular numbers the left side is linear and the right side is convex.

Use the [two corank recurrences](size-descent.md#descent-in-the-two-recurrences). A term $q^\sigma B_h(q)(q^u+\cdots+q^v)$ in the row at $n$ has $u+v\ge E(n-h)$ and $\sigma\ge h$. A negative step from $k$ to $k+1$ would give coefficients of $B_h$ with $b_i>b_j$, $i=k-\sigma-v\ge0$, $j=k+1-\sigma-u>i$. By (1), if $B_h$ is unimodal this requires
$$
 2k+1>2h+E(n-h)+.524(2h)^{3/2}-(3h+1)
 \ \ge M n^{3/2}-n-1,\qquad
 M=(9/8+1/(8\cdot .524^2))^{-1/2}.
$$
The last inequality minimizes $c(1-y)^{3/2}+.524(2y)^{3/2}$ over $0\le y\le1$. At $h=0$ the comparison threshold $-1$ is vacuous and the inequality still holds. The isolated $C_n$ has no negative difference when $2k+1\le M n^{3/2}-n-1$, since $E(n)\ge c n^{3/2}-n$ and $c>M$.

For $n\ge2049$, $2(.1366)(2n+1)^{3/2}+1<M n^{3/2}-n-1$. At $n\ge4096$ use $.1378$ in its place. Divide by $n^{3/2}$ and check the smallest allowed $n$ in each case. Consequently, if the smaller odd-part rows are unimodal, the odd-part row is nondecreasing through the start of (2). After its unimodality is established, the same holds for the even-part row, which can also involve $B_n$. The [all-size right flank](marked-hits.md) and the [lower-half rank inequality](monotonicity.md#1-lower-half-for-all-sizes) give weak decrease from $\lceil .6s\rceil$ onward in both. A unimodal window joins these two ends. Induction through $n=299999$ followed by [size descent](size-descent.md) proves the equivalence in (2).

Run the verifier from the checkout with

~~~sh
python3 -B verify_moment_comparisons.py
~~~
