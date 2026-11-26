# Finite-size bounds on every global peak

Write $m=2n$ for the odd-part staircase and $m=2n+1$ for the even-part staircase, $s=m^{3/2}$, and $P(k)=a_{D-k}/\binom{m}{n}$ for the corank law. For every $n\ge2$, every maximizing corank satisfies
$$\frac{1}{6\sqrt6}\ \le\ \frac{k}{s}\ <\ \frac{13}{20}.$$
The lower constant is sharp. In fact $k/s>1/14$ except possibly at $m=6$. The odd-part shape $(5,3,1)$ has maximum coefficient three at coranks $1,2,3,4$, giving equality at corank one. At $n=1$ the full shape has a maximizing coefficient at corank zero.

For $m\ge3136$ the estimates below also place every coefficient reaching half the maximum in $s/15<k<3s/4$. Both bounds allow multiple local peaks.

## Height of the maximum from the exact variance

Let $\delta=m\bmod 2$, $\ell=(m+\delta)/2$ and $C=4^\ell/\binom{2\ell}{\ell}$. The [first two exact moments](finite-reduction.md#exact-area-moments) give
$$
16\operatorname{Var}K=\frac{472}{15}\ell^3+A_\delta(\ell)-(3\ell+2-2\delta)^2 C^2,
$$
where $A_0(\ell)=228\ell^2/5+344\ell/15+4$ and $A_1(\ell)=44\ell^2/15+8\ell/5$. For example, in the cited formula $R_{-2}=C$, $R_{-4}=(\ell+1)C$ and $R_{-6}=(\ell+1)(\ell+2)C/2$. The odd negative exponents give $R_{-1}=1$, $R_{-3}=2\ell+1$, $R_{-5}=(2\ell+1)(2\ell+3)/3$, and $R_{-7}=R_{-5}(2\ell+5)/5$. Subtracting the square of the mean $((3\ell+2-2\delta)C-6\ell-2+2\delta)/4$ cancels every term linear in $C$.

The [moment verifier](verify_moments.py) compares this closed form with the first two moments of the exact rank sequences.

For $m\ge640$, $\operatorname{Var}K<.026s^2$. Use the Wallis bound $C^2\ge\pi\ell$. After division by $\ell^3$, the upper bounds on $16\operatorname{Var}K/\ell^3$ have constant $472/15-9\pi$ and positive coefficients on the inverse powers of $\ell$. They are largest at $\ell=320$ and $m/\ell=2-\delta/\ell$ is smallest there for each parity. Substitution gives $\operatorname{Var}K/s^2<.0252$ in both cases.

Add an independent uniform variable on $[-1/2,1/2]$ to $K$. Its sum with $K$ has density bounded by $A=\max P$ and variance $\operatorname{Var}K+1/12$. Any real density bounded by $A$ has variance at least $1/(12A^2)$ by integrating $\Pr(|X-\mathbb EX|>t)\ge1-2At$ up to $1/(2A)$. Thus
$$s\max P\ge (12\operatorname{Var}K/s^2+1/s^2)^{-1/2}>1.78 \qquad(m\ge640). \tag{1}$$

## Upper bound for a single large corank

Use the independent down indicators from the [first-passage estimate](first-passage.md#tilt-and-prefix-variance). Under the fair law their rank sum $S$ has mean $m(m+1)/4>D$. Tilt by $e^{-tS}$ with $t=8/s$ and set $L=\lceil m/10\rceil$, $B=m-L$. Impose the wall only on the prefix to bound the probability at one rank. The remaining suffix is independent, with maximal rank probability $\|g_B\|_\infty$. Undoing the tilt and applying Hoeffding to its normalizer gives
$$P(k)\le \exp(-8k/s+t^2\sum_{r=1}^m r^2/8)
 \frac{\Pr_t(E_L)}{\Pr_{\rm fair}(E_m)}\,\|g_B\|_\infty.$$
For $m\ge640$ the positive exponent is below $2.673$. Wallis gives $\Pr_{\rm fair}(E_m)=1/C\ge.79/\sqrt m$, including odd $m$, for which survival equals the fair probability at length $m+1$.

The largest prefix drift is $d=\tanh(4/\sqrt m)\in[.99\cdot4/\sqrt m,4/\sqrt m]$. The [homogeneous survival estimate](first-passage.md#tilt-and-prefix-variance) bounds $\Pr_t(E_L)$ by $2d+e^{-d^2L/2}/\sqrt L$. Hence the survival ratio is below $12$. For the suffix $B\ge.898m$, $p_r(1-p_r)>.24$ and $\sigma_B\ge\sqrt{.24 B^3/3}$. At order zero [the suffix inversion bound (3)](first-passage.md#independent-suffix-estimates) is less than $.422$ on the $\sigma_B$ scale, using $B\ge574$. This gives $\|g_B\|_\infty<1.77/s$. Consequently
$$sP(k)\le 21.24\,e^{2.673-8k/s}.\tag{2}$$
At $k/s\ge13/20$ the right side is below $1.78$, and at $k/s\ge3/4$ it is below $.89$.

## Upper bound for a single small corank

First we need the following real eigenvalue estimate. For the [edge-weighted transfer operator](effective-small-area.md#real-transfer-operator) with $\beta=H^{-3}$, $\rho=\|T_\beta\|$ and $\lambda=\rho^2/4$,
$$\rho\le 2-1.65/H^2,\qquad \lambda\le e^{-1.65/H^2}\quad (H\ge8). \tag{3}$$

Put $z=1/H$, $c=.8z$ and use the positive square-summable vector $v_j=(j+1)e^{-cj}$. Direct division, also at $j=0$, gives
$$
(T_\beta v)_j/v_j=e^{-\beta j/2}\big(A-B/(j+1)\big),\quad
A=e^{c+\beta/2}+e^{-c},\quad B=e^{c+\beta/2}-e^{-c}.
$$
Here $A\le2+.65z^2+.56z^3$ and $B\ge1.6z$. For the first bound write $A=2\cosh c+e^c(e^{z^3/2}-1)$ and use the positive Taylor series at $z\le1/8$. Let $a=1.65$ and $b=(1-az^2/2)z^3$. By the arithmetic-geometric mean inequality,
$$ B/(j+1)+bj\ge 2\sqrt{Bb}-b
 \ge z^2(2\sqrt{1.6(1-a/128)}-1/8)>A-2+az^2.$$
Therefore $A-B/(j+1)\le(2-az^2)(1+\beta j/2)\le(2-az^2)e^{\beta j/2}$. Pair $T_\beta v\le(2-az^2)v$ with the positive top eigenvector to obtain (3).

Now take $m\ge3136$, $H=\sqrt{m/49}\ge8$, $r=\lfloor.45m\rfloor$, $B=m-2r$ and $l=\lceil H^2\rceil$. On a surviving path the area of the first $2r$ steps cannot exceed its total corank. Given this prefix, the unrestricted fair suffix rank has point probabilities at most $55/s$. Indeed $B\ge m/10$, $\sigma_B\ge B^{3/2}/\sqrt{12}$, and the order-zero bound (3) in the [suffix estimates](first-passage.md#independent-suffix-estimates) is below $.50$ for fair steps and $B\ge313$. The suffix rank and prefix together determine the total corank by $K=D-S$. A positive area tilt on the prefix and the [two transfer boundary estimates](effective-small-area.md#complex-tilts-near-the-saddle) thus give
$$
sP(k)\le 55\cdot 2\sqrt m\, e^{\beta k}\,(10/H)\lambda^{r-2l}
 \le 7700\,\exp(343k/s-33).
\tag{4}
$$
We used $\Pr_{\rm fair}(E_m)\ge1/(2\sqrt m)$ and $(r-2l)/H^2\ge.45\cdot49-2-3/64>20$. The boundary estimates bound the transform of the surviving prefix with free endpoint. Conditioning on its final height for the subsequent suffix estimate introduces no further factor. At $k/s\le1/14$ the right side is below $1.78$, and at $k/s\le1/15$ it is below $.89$. Equations (1)–(4) give the assertions in this range.

For $640\le m<3136$ the [strict tail theorem](finite-tail.md) gives $k\ge9n+42>s/14$ at every global maximum. Here $n\le1567$ and $s/n\le(2+1/n)^{3/2}\sqrt n$. For the remaining $2\le n\le320$ the [full rank verifier](README.md#exact-coefficient-checks) checks the first and last maximizing coranks in both families, including the exceptional tie at $m=6$. This finishes the uniform bounds.
