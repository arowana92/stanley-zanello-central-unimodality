# Adjacent ranks beyond four times the area scale

Let $m=2n$ or $2n+1$, $D=\lfloor m^2/4\rfloor$ and $s=m^{3/2}$. For both staircases and every integer rank
$$D/2\le j\le D-4s,$$
we have
$$a_{j+1}\ge a_j e^{5(D-j)/m^3}>a_j,\qquad a_j^2>a_{j-1}a_{j+1}.$$
The interval first contains a rank at $m=1024$, where it consists of $j=131072$. Together with weak lower-half growth, this leaves only the last $4s+O(1)$ ranks in which to test for a reversal. The [high-rank tail estimate](finite-tail.md) removes a further linear interval.

The proof imposes survival through a short prefix and counts the paths lost after it. If the first forbidden step occurs early, the remaining independent steps smooth the area distribution. If it occurs late, an exponential weight on the height at an earlier cut bounds the probability of a hit while preserving cancellation in the area of the surviving prefix. We work with the discarded mass before renormalizing. This keeps the bounds valid for adjacent differences.

## Tilt and prefix variance

Use the [ballot encoding](README.md#exact-coefficient-checks) and the [independent rank tilt](effective-middle.md#tilt-and-survival). In descending label order take down probabilities $p_r=(1+e^{\alpha r/m})^{-1}$, rank $S=\sum r X_r$, heights $H_t$, and survival events $E_t$. Choose $\mathbb ES=j$. The interval implies $m\ge1024$. At zero tilt the mean exceeds $D$. At $\alpha=2$ it is at most $m(m+1)/4-(.38/m)\sum r^2<D/2$ by $\tanh(r/m)\ge .76r/m$. Throughout, the absolute derivative of the mean is at most $\sum r^2/(4m)\le m^2/11.9$. Thus
$$0<\alpha<2,\qquad \alpha\ge11.9(D-j)/m^2,\qquad \gamma=\alpha\sqrt m\ge47.6.$$

Set $L=\lceil m/64\rceil$, $M=m-L$, $U=\sum_{r>M}r X_r$ and $\sigma^2=\sum_{r\le M}r^2p_r(1-p_r)$. Then $L/m\le17/1024$, $.177s\le\sigma\le.30s$, by $.1<p_r(1-p_r)\le1/4$ and the sum of squares. We claim
$$\mathbb E[(U-\mathbb EU)^2\mid E_L]<.29\sigma^2. \tag{1}$$

Write $d_0=\tanh(\alpha/2)\ge.38\alpha$, $d_*=(1-L/m)d_0$ and $G(d)=2d/(1+d)$. All prefix drifts are at least $d_*$ by concavity of $\tanh$, so $\Pr(E_L)\ge G(d_*)$ by coupling and the homogeneous ruin probability. A homogeneous walk of drift $0\le d<1$ survives $L$ steps with probability at most
$$G(d)+e^{-d^2 L/2}/\sqrt{L+1}.$$
Indeed each first hit of $-1$ at time $i$ has probability $\sqrt{(1-d)/(1+d)}(1-d^2)^{i/2}$ times its fair-walk probability. Sum over $i>L$ and use $\Pr_{\rm fair}(E_L)=2^{-L}\binom L{\lfloor L/2\rfloor}\le1/\sqrt{L+1}$. The bound at $d=1$ holds directly.

Tilt the prefix again by $\exp(\pm tU)$ for $t=2/(m\sqrt L)$. The positive sign only decreases survival. Under the negative sign the maximum drift is at most $d'=\min(1,d_0+1/\sqrt L)$ by the Lipschitz bound on $\tanh$. Applying the preceding estimate and $G(d_*)\ge d_*$, the survival ratio is at most
$$\frac{1+(1+e^{-d_0^2L/2})/(d_0\sqrt L)}{1-L/m}<1.51,$$
since $d_0\sqrt L\ge.38(47.6)/8$. Here $G(d')/G(d_*)\le d'/d_*$. Hoeffding's bound on each unconditioned centered exponential moment is $e^{1/2}$. Since $\cosh z\ge1+z^2/2$, averaging the two conditional moments bounds the left side of (1) by $(m^2L/2)((1+1.51)e^{1/2}/2-1)<.29\sigma^2$.

## Independent suffix estimates

Let $g_B$ be the mass function of $\sum_{r\le B}rX_r$ and $\sigma_B$ its standard deviation. Use $D_0=I$, $D_1g(v)=g(v+1)-g(v)$ and $D_2g(v)=g(v-1)-2g(v)+g(v+1)$. For $B=M$, $\sigma_M=\sigma$, $x=(v-\mathbb E(S-U))/\sigma$ and $\varphi$ the standard normal density, we use
$$|\sigma g_M(v)-\varphi(x)|<.04,\qquad
\sigma^2|D_1g_M(v)|<.37,\qquad
|\sigma^3D_2g_M(v)-\varphi''(x)|<.16. \tag{2}$$

Here are uniform bounds for (2) and for suffixes left after a first hit. Write $a=\sigma_B/B$, $b=2/\pi^2$, and $p_*=\min_{r\le B}p_r(1-p_r)$. In $|\theta|\le1/B$ the characteristic function has modulus at most $e^{-.45\sigma_B^2\theta^2}$ by its Bernoulli product. Through $|\theta|\le\pi/B$ its modulus is at most $e^{-b\sigma_B^2\theta^2}$ using $\sin(r|\theta|/2)\ge r|\theta|/\pi$. On $\pi/B\le|\theta|\le\pi$ the bound is $e^{-p_*B/2}$, since
$$\sum_{r\le B}\sin^2(r\theta/2)\ge B/2-1/(4\sin(|\theta|/2))\ge B/4$$
by the finite cosine sum. In particular, for $r=0,1,2$ and $B\ge127$ the quantity $\sigma_B^{r+1}\|D_rg_B\|_\infty$ is at most
$$
\frac{\Gamma((r+1)/2)}{2\pi\,(.45)^{(r+1)/2}}
+\frac1\pi\int_a^\infty x^r e^{-b x^2}\,dx+4(.30B^{3/2})^3 e^{-p_* B/2}. \tag{3}
$$
The last term uses the unscaled multipliers bounded by $1,2,4$, respectively, and $1\le\sigma_B\le.30B^{3/2}$. In the two integrals use their scaled bounds $1,|x|,x^2$.

For (2) telescope the centered product against $e^{-x^2/2}$ at Fourier argument $x/\sigma$ on $|x|\le\sigma/M$. The [Bernoulli Taylor estimate](effective-middle.md#a-local-gaussian-estimate-with-the-wall-imposed-through-l) bounds its difference by $.23(M/\sigma)|x|^3e^{-.45x^2}$. After integration against $1$ or $x^2$ and division by $2\pi$, the costs are at most $.23m/(\pi\sigma)$ times $1/(2\cdot.45^2)$ or $1/.45^3$. They are below $.032$ and $.142$ since $\sigma/m\ge.177\sqrt m$. The remaining inner tails cost at most $\pi^{-1}\int_{5.65}^\infty x^r(e^{-b x^2}+e^{-x^2/2})\,dx<.008$ for $r=0,2$ (below $.001$ for $r=0$). The outer term in (3) and the centered second-difference multiplier error $\pi^{-1}\int_0^\infty x^4e^{-x^2/2}\,dx/(12\sigma^2)$ each cost less than $.001$. For the first difference use (3) directly. This proves (2).

For clarity, the following are bounds from (3), valid simultaneously for all three orders. The last row will be used only after half the labels have been read.

| Conditions | Upper bound in (3) |
| --- | ---: |
| $B\ge894$, $p_*\ge.1$ | $.50$ |
| $B\ge511$, $p_*\ge.1$ | $3$ |
| $B\ge127$, $p_*\ge.195$ | $1500$ |

To check the numbers use $a\ge\sqrt{p_*B/3}$. Integration by parts bounds the order-two tail integral by $e^{-ba^2}(a/(2b)+1/(4b^2a))$, and the orders zero and one by $e^{-ba^2}/(2ba)$ and $e^{-ba^2}/(2b)$. The polynomial times exponential in (3) decreases beyond each listed endpoint. Also, for $B\le M$,
$$\sigma/\sigma_B\le(M/B)^{3/2}.$$
Indeed $p_r(1-p_r)$ decreases with $r$, so the variance ratio is at most $\sum_{r\le M}r^2/\sum_{r\le B}r^2\le(M/B)^3$.

## Paths lost before the late cut

Write $F_L(v)=\Pr(S=v\mid E_L)$ and $F(v)=\Pr(S=v,E_m)/\Pr(E_L)$. Put $u=\lceil m/8\rceil$, $w=\lceil m/2\rceil$, $h=\lceil7m/8\rceil$. For failures after $L$ and through $h$, condition on the first hitting time $i$ of $-1$ and its entire prefix. The remaining suffix is independent, with exactly the law $g_{m-i}$ shifted by the prefix rank. For each of the three time intervals below, its total contribution to $\sigma^{r+1}\|D_r(F_L-F)\|_\infty$ is bounded by its conditional first-hit probability times the entry from (3) times $(m/(m-i_{\rm end}))^{3(r+1)/2}$.

* For $L<i\le u$, the hit probability given $E_L$ is at most $\mathbb E[e^{-\alpha H_L/2}\mid E_L]$. Through time $w$ the up drifts are at least $\tanh(\alpha/4)$, and the probability to hit $-1$ from $H_L$ for that homogeneous walk is $e^{-\alpha(H_L+1)/2}$. Weighting the first $v$ signs by $e^{-\alpha H_v/2}$ gives nonpositive drifts and normalizer
$$
Z_v=\prod_{r=m-v+1}^m \frac{\cosh(\alpha(1-r/m)/2)}{\cosh(\alpha r/(2m))}.
$$
For $v=L$, this is at most $e^{-.103\alpha^2 L}$. In fact $\log\cosh z\ge.43z^2$ on $[0,1]$ because $\log\cosh z/z^2$ decreases there, and $\log\cosh z\le z^2/2$. The new survival probability is at most $1/\sqrt L$. Dividing by $\Pr(E_L)\ge d_*$ gives a hit probability below $.012$.
* For $u<i\le w$, the same ruin bound from time $u$ gives probability at most $Z_u$ given $E_L$. The auxiliary survival probability through $u$ is at most the original one through $L$ by monotone coupling. Since $u/m\le.126$, the same hyperbolic-cosine bounds give $Z_u\le e^{-.08\alpha^2u}<1.5\cdot10^{-10}$.
* For $w<i\le h$, a hit implies some $H_i<0$ on that interval. This decreasing event has conditional probability given $E_L$ at most its unconditioned probability by product-measure association. For every $i\ge w$, concavity of $\tanh$ gives $\mathbb EH_i\ge.38\alpha i(1-(i-1)/(2m))\ge.1425\alpha m$. The exponential maximal inequality for the centered independent height increments up to $h\le.877m$ now gives probability at most $\exp(-.1425^2\gamma^2/(2\cdot.877))<4.1\cdot10^{-12}$.

The three suffix lengths are bounded below by $m-u\ge.874m$, $m-w\ge.499m$ and $m-h\ge m/8-1$, respectively. In the last interval $B=m-i\le m/2$, so $p_*\ge e/(1+e)^2>.195$. Thus the three rows of (3) apply in order. For all $r\le2$ their combined cost is at most
$$
.012\cdot.50\cdot1.85+
1.5\cdot10^{-10}\cdot3\cdot24+
4.1\cdot10^{-12}\cdot1500\cdot13000<.012. \tag{4}
$$

## A height tilt for paths lost after the cut

For the remaining loss $E_h\setminus E_m$, let $\Xi(\theta)=\mathbb E[e^{i\theta S}{\bf1}_{E_h\setminus E_m}]/\Pr(E_L)$. We prove
$$|\Xi(\theta)|\le 2 e^{-(.186)^2\gamma^2/2}\exp(-m|\theta|^{2/3}/1600),\qquad |\theta|\le\pi. \tag{5}$$
From height $v$ at time $h$, the chance of a later hit is at most $e^{-tv+(m-h)t^2/2}$ for any $t>0$. This follows from the exponential maximal inequality since each remaining drift is nonnegative. Condition on $H_h=v$, retaining the complex row of surviving prefixes indexed by $v$. Multiplication of that row by $e^{-tv}$ is precisely an auxiliary product law on the first $h$ signs times the constant $\mathbb E e^{-tH_h}$. Its log down/up odds are $-\alpha r/m+2t$. Take $t=.186\alpha$. The deterministic normalizers cost at most
$$\exp(-t\mathbb EH_h+mt^2/2)\le e^{-(.186)^2\gamma^2/2},$$
since $\mathbb EH_h\ge .38\alpha h(1-(h-1)/(2m))\ge.186\alpha m$. This estimate multiplies the absolute row sum for prefix oscillation under the auxiliary law.

The auxiliary law has down probabilities above $.22$ and up probabilities above $.32$ (its log odds are in $[-1.256,.744]$). Its survival probability to $L$ is at most $\Pr(E_L)$ by monotone coupling. After $L$, apply the [paired-label row bound](effective-middle.md#restoring-the-wall-without-losing-a-lattice-difference) under the auxiliary law. Both mixed probabilities in any pair exceed $.22\cdot.32>1/18$. Thus a killed block of $2l$ steps has absolute row sum at most $e^{-1/200}$, where $l=\lceil2|\theta|^{-2/3}\rceil$ for $0<|\theta|\le1$ and $l=1$ otherwise. In particular $l\le3|\theta|^{-2/3}$, and $h-L\ge.85m$ leaves at least $.85m|\theta|^{2/3}/6-1$ full blocks. These estimates give (5), also at frequency zero by the probability bound.

Invert with multipliers bounded by $|\theta|^r$ for $r=0,1,2$. The contribution of the late loss on the scale $\sigma^{r+1}$ is bounded by
$$\frac{3}{\pi}(.30)^{r+1}\,1600^{3(r+1)/2}\Gamma(3(r+1)/2)\, e^{-(.186)^2(47.6)^2/2}<.001.$$
This is the integral of (5) after substituting $x=m^{3/2}|\theta|$ and extending to infinity. Together with (4) it gives $\sigma^{r+1}\|D_r(F_L-F)\|_\infty<.013$ for all three orders.

## Sign, curvature and exact checks

Under $E_L$ the independent suffix in (2) is evaluated at $j-U$, with $x=(\mathbb EU-U)/\sigma$. The pointwise inequalities $\varphi(x)\ge\varphi(0)(1-x^2/2)$ and $\varphi''(x)\le\varphi(0)(-1+3x^2/2)$ follow from $e^{-x^2/2}\ge1-x^2/2$ and $x^2e^{-x^2/2}\le x^2$. Equations (1), (2), and the bound on $F_L-F$ yield
$$\sigma F(j)>.27,\qquad \sigma^2|D_1F(j)|<.40,\qquad \sigma^3D_2F(j)<-.05.$$
In particular the tilted mass strictly exceeds the average of its two neighbors, which gives strict log-concavity. Also $F(j+1)/F(j)\ge1-2/\sigma$ and $\log(1-2/\sigma)\ge-4/\sigma$. Since $\alpha\sigma/m\ge.177\gamma>8$, removing the rank tilt increases the log ratio by $\alpha/m$ and leaves at least $\alpha/(2m)\ge5(D-j)/m^3$. Removing the tilt also preserves strict log-concavity.

The verifier computes the window and its two neighbors exactly at a chosen size. In a prefix of length $t$ with $d$ down steps and height $t-2d$, the existing parts gain $(m-t)d$ by the end. To maximize the additional weight from new down steps, descend to zero as early as possible, then alternate up and down. This maximizes every prefix down count. Truncating each prefix polynomial to ranks that can reach the target therefore keeps every required coefficient. At small sizes the verifier compares windows against direct enumeration of the partitions. The comparison of the exponential growth bound uses the stronger rational bound $1/(1-5(D-j)/m^3)$.

~~~sh
python3 -B verify_middle.py --n 512
~~~

At 512 rows the exact checks pass at rank 131072 for the odd-part staircase and at every rank from 131328 through 131391 for the even-part staircase. These are checks of the stated interval at that size. The ranks between this interval and the high-rank tail remain relevant to full unimodality.
