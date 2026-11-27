# An increasing-side bound at every size

Let $m=2n$ or $2n+1$, $s=m^{3/2}$ and $D=\lfloor m^2/4\rfloor$. For both central staircases and every integer rank $j\ge D/2$,
$$
\begin{aligned}
 a_{j+1}>a_j&\qquad\text{if }D-j\ge 3s/2,\\
 a_j^2>a_{j-1}a_{j+1}&\qquad\text{if }D-j\ge 2s .
\end{aligned} \tag{1}
$$
Thus a potential reversal is confined to the final $3s/2+O(1)$ ranks, before using the growth in corank near the full diagram. This improves the [four-scale bound](first-passage.md). Below we count the effect of the first forbidden ballot step on an independent rank distribution. The prefix length differs for first and second differences. Keeping the actual tilted drift and separating the Fourier frequencies of the late-hit term permits the smaller thresholds.

For $m<770$ use the original [exact rank checks through 384 rows](README.md#exact-coefficient-checks). The interval in (1) is empty for $m<144$. At the other sizes in this finite range the upper half is strictly log-concave, every global maximum has corank below $.65s$ by the [mode bound](mode-bounds.md), and hence every step in the first interval is strictly increasing. The rest of the proof assumes $m\ge770$. The argument at these sizes is independent of coefficient enumeration.

## Prefix and suffix estimates

Use the independent rank tilt of the [first-passage proof](first-passage.md#tilt-and-prefix-variance). The down probability at label $i$, read in descending order, is $p_i=(1+e^{\alpha i/m})^{-1}$. Choose $\alpha$ so that the unconditional mean of the down-label sum $S$ equals $j$. The mean at zero exceeds $D$, at two it is below $D/2$, and its derivative has magnitude at most $\sum i^2/(4m)\le m^2/11.9$ for $m\ge770$. Thus $0<\alpha<2$ and $\gamma=\alpha\sqrt m\ge11.9(D-j)/s$. Write $d_0=\tanh(\alpha/2)$, $\kappa=d_0\sqrt m$, $E_v$ for survival through step $v$, and $H_v$ for the walk height.

Take $L=\lceil m/d\rceil$ with $d=24$ for growth and $d=48$ for log-concavity. Put $M=m-L$, $\ell=1/d+1/770$, and $\sigma^2=\sum_{i\le M}i^2 p_i(1-p_i)$. Write $p$ for a lower bound on $p_i(1-p_i)$, $i\le m$, in the given tilt range. Then $\sigma/s\ge z=\sqrt{p(1-\ell)^3/3}$, $\sigma\le.30s$, and $\sigma/M\ge a=\sqrt{p(1-\ell)770/3}$. For the prefix label sum $U=S-\sum_{i\le M}iX_i$ put $X=(\mathbb EU-U)/\sigma$. The [conditional second-moment proof](first-passage.md#tilt-and-prefix-variance), with this $L$, gives
$$\mathbb E(X^2\mid E_L)\le V=\frac{\ell}{2z^2}\left(\frac{(1+R)e^{1/2}}2-1\right),\qquad
 R=\frac{1+(1+e^{-v^2/2})/v}{1-\ell},\quad v=\kappa/\sqrt d.$$
Indeed the smallest prefix drift is at least $(1-\ell)d_0$. The two tilts of $U$ by $\pm2/(m\sqrt L)$ give survival ratios at most one and $R$, respectively, by the homogeneous survival and ruin estimates. The unconditional centered exponential moments are at most $e^{1/2}$ by Hoeffding. Apply $\cosh u\ge1+u^2/2$.

For a suffix of $B$ labels let $g_B$ denote its mass function with variance $\sigma_B^2$. Write $D_0g=g$, $D_1g(k)=g(k+1)-g(k)$, and $D_2g(k)=g(k-1)-2g(k)+g(k+1)$. For $B\ge95$ the following upper bounds hold on $\sigma_B^{r+1}\|D_rg_B\|_\infty$.

| $B$ | $r=0,1$ | $r=2$ |
| --- | ---: | ---: |
| $95\le B<192$ | .46 | 1.6 |
| $192\le B<384$ | .46 | .56 |
| $B\ge384$ | .46 | .56 |

Here is an integral check. On $|\theta|\le1/B$ the product modulus is at most $e^{-.45\sigma_B^2\theta^2}$. On $1/B\le|\theta|\le2/B$ replace $.45$ by $.35$, using $2\sin^2(u/2)\ge.35u^2$ for $|u|\le2$. Up to $\pi/B$ use $2/\pi^2$. Beyond $\pi/B$ the [finite cosine sum](first-passage.md#independent-suffix-estimates) gives $\sum_{i\le B}\sin^2(i\theta/2)\ge B/4$, and beyond $8\pi/B$ it gives $15B/32$. For $p_*=\min_{i\le B}p_i(1-p_i)$ use the lower bounds $.234,.196,.104$, respectively, in the three rows, by $\alpha<2$ and $m\ge770$. Write $a_B=\sqrt{p_*B/3}$, $J_r(a,b)=\int_a^\infty x^r e^{-b x^2}dx$. Outside $|\theta|\le1/B$ the scaled inverse-transform integral is at most
$$\frac{J_r(a_B,.35)+J_r(2a_B,2/\pi^2)}{\pi}
 +\frac{(.30\sqrt B\,8\pi)^{r+1}e^{-p_* B/2}}{(r+1)\pi}
 +2^r(.30B^{3/2})^{r+1}e^{-15p_*B/16}.$$
Each term decreases with $B$ in the stated range at fixed lower bound on $p_*$. Add $J_r(0,.45)/\pi$ from the inner arc. For $B=M\ge736$, the bound outside the inner arc, the normal tail $J_r(a_B,.5)/\pi$ and the centered multiplier error are together below $.002$. The multiplier error at order two is bounded by $J_4(0,.5)/(12\pi\sigma^2)<.00001$. In particular $\sigma^2\|D_1g_M\|_\infty<.37$.

On the inner arc improve the Gaussian comparison by keeping the signed third Bernoulli moment. For one centered Bernoulli variable with variance $w$ and down probability $p_i$, its characteristic function at $u$ differs from $e^{-wu^2/2}$ by at most
$$ w\left(|1-2p_i||u|^3/6+|u|^4/24\right).$$
Taylor through the cubic term uses the fourth moment $w(1-3w)$, and the quadratic remainder in the Gaussian is bounded by $w^2u^4/8$. In the telescoping product the omitted factor costs at most $e^{.45/4}$ on the Gaussian scale. With $d_{\max}\ge d_0$, this bounds the local approximation error at orders $r=0,2$ by
$$e_r=.002+\frac{.187d_{\max}J_{r+3}(0,.45)/a+.047 J_{r+4}(0,.45)/a^2}{\pi}.$$
Specifically the comparison is with $\varphi(X)$ and $\varphi''(X)$ for the scaled suffix mass and centered second difference at $j-U$, where $\varphi$ is the standard normal density.

## First hits up to the late cut

Put $h=\lceil7m/8\rceil$. Normalize the law with the full wall by $\Pr(E_L)$, writing $F(j)=\Pr(S=j,E_m)/\Pr(E_L)$. Dropping the wall after $L$ gives $F_L(j)=\Pr(S=j\mid E_L)$. For a first hit after $\lceil vm\rceil$ and up to $\lceil em\rceil\le h$, condition on the entire prefix through that hit. The remaining labels are independent. If the conditional hit probability given $E_L$ is at most $P$, the cost in $\sigma^{r+1}\|D_r(F_L-F)\|_\infty$ from this group is at most
$$ P\,c_r(1-e-1/770)^{-3(r+1)/2},$$
where $c_r$ is the applicable suffix bound above. Indeed $\sigma/\sigma_B\le(M/B)^{3/2}$ since $p_i(1-p_i)$ decreases with $i$ and the unweighted sums of squares have this ratio bound.

Use successive cut fractions $1/d,1/8,1/4,1/2,5/8,3/4,13/16,7/8$. For a pair $v,e$ with $e\le1/2$, the homogeneous ruin probability after the first cut is at most $\exp(-\alpha H_{\lceil vm\rceil}/2)$ on surviving paths, because subsequent drifts through the second cut are at least $\tanh(\alpha/4)$. As in the [height-tilt calculation](first-passage.md#paths-lost-before-the-late-cut), the auxiliary prefix law has nonpositive drifts and hence survival at most $.81/\sqrt{vm}$ by the fair central binomial bound. Divide by $\Pr(E_L)\ge 2(1-\ell)d_0/(1+d_{\max})$. The deterministic normalizer is bounded using $\log\cosh u\ge.43 u^2$ for $0\le u\le1$ and $\log\cosh u\le u^2/2$. This gives
$$P\le \frac{.81(1+d_{\max})}{2(1-\ell)\kappa\sqrt v}
 \exp\left[-\gamma^2 v\left(.1075(1-b)^2-b^2/8\right)\right],\qquad b=v+1/770.$$

For $v\ge1/2$, a negative height at any time in the interval is a decreasing event in the up signs. Product-measure association bounds its probability given $E_L$ by its unrestricted probability. Each of these times has mean height at least $d_0 m v(1-v/2)$ by concavity of the drift as a function of the label. The exponential maximal inequality for independent centered increments up to $\lceil em\rceil$ gives
$$P\le\exp\left[-\kappa^2 v^2(1-v/2)^2/(2(e+1/770))\right].$$
Denote the sum of these seven bounds on the scaled difference by $A_r$, including the suffix norm and variance-ratio factors. For the first three terms $B\ge384$. All later terms have $B\ge95$.

## Fourier bound for a hit after the cut

Take $t=.49d_0$. From height $H_h$ the probability of a later hit is at most $\exp(-tH_h+(m-h)t^2/2)$ by nonnegative drift. Condition on the endpoint at $h$, keeping the complex prefix row indexed by that endpoint. The positive factor $e^{-tH_h}$ changes the down/up log odds on the prefix to $-\alpha i/m+2t$. The overall normalizer times the future bound is at most
$$e^{-t\mathbb EH_h+mt^2/2}\le e^{-(.49\kappa)^2/2},$$
since $\mathbb E H_h\ge.49d_0m$. The auxiliary survival probability through $L$ is at most $\Pr(E_L)$ by coupling. We bound the absolute row sum for the remaining $h-L$ prefix steps under that auxiliary law, retaining the wall.

In a pair of labels at spacing $l$, the two mixed choices have probabilities $A=p_i(1-p_j)$ and $B=(1-p_i)p_j$ under the auxiliary law. Averaging phases at fixed endpoint loses at least $2AB\sin^2(l\theta/2)/(A+B)$ from the unrestricted modulus row sum of this pair. This follows by squaring the modulus. Here $2AB/(A+B)\ge w$ with $w=.20$ at $\alpha\le1$ and $w=.12$ otherwise. Indeed the auxiliary down probabilities are in $[.36,.62]$ or $[.22,.68]$, respectively, by their log odds. The sum $1/A+1/B$ is convex separately in the two probabilities, so the four corners of the rectangle suffice. Pair the two halves of a block of $2l$ steps. The unrestricted bound becomes $\rho=\exp[-wl\sin^2(l\theta/2)]$, and retaining the wall gives $(1+\rho)/2$, by the [retained-mass inequality](peak-rate.md#fourier-inversion-for-lattice-differences).

For $0<|\theta|\le1/8$ use $l=\lceil4|\theta|^{-2/3}\rceil$. Then $l|\theta|/2\le1.063$, $\sin^2(l\theta/2)\ge.65(l\theta/2)^2$ and $l|\theta|^{2/3}\le4.25$. A block costs at least $.56$ or $.41$ in the negative log, respectively. Over $h-L$ steps the bound is $2e^{-\eta m|\theta|^{2/3}}$ with $\eta=.054$ or $.039$. For larger frequencies choose $l$ nearest $\pi/|\theta|$. The row bound is $2e^{-\eta_i(h-L)}$ on each arc in the table.

| Absolute frequency | Maximum $l$ | Lower bound on $\sin^2(l\theta/2)$ | $\eta_i$ at $\alpha\le1$ | $\eta_i$ otherwise |
| --- | ---: | ---: | ---: | ---: |
| $[1/8,.18]$ | 25 | .99 | .013 | .012 |
| $[.18,1/4]$ | 17 | .99 | .019 | .016 |
| $[1/4,1/2]$ | 13 | .98 | .022 | .019 |
| $[1/2,\pi]$ | 6 | .75 | .028 | .019 |

The sine bounds follow from $\big|l\,|\theta|-\pi\big|\le|\theta|/2$. In the last row with $l=1$, use $|\theta|\ge2\pi/3$ directly. For $l\ge2$ there we have $|\theta|\le2\pi/3$. At each sine-square lower bound $c$, $-\log((1+e^{-wlc})/2)$ is concave in $l$ and vanishes at zero, so the loss per step is smallest at the maximum length. Rounding down the number of full blocks costs at most two.

Denote the resulting bound for the scaled order-$r$ inversion integral of the late-hit term by $B_r$. For clarity, the small arc contributes at most
$$ e^{-(.49\kappa)^2/2}\frac{3(.30)^{r+1}\Gamma(3(r+1)/2)}{\pi\,\eta^{3(r+1)/2}}.$$
On each other arc $[a_i,b_i]$ add at most
$$ e^{-(.49\kappa)^2/2}\frac{2(.30m^{3/2})^{r+1}(b_i^{r+1}-a_i^{r+1})}{(r+1)\pi}
     e^{-\eta_i(7/8-\ell)m}.$$
Here $m=770$ majorizes the polynomial times exponential for every $m\ge770$, by its logarithmic derivative. These estimates use the multiplier bound $|\theta|^r$.

## Signs and verification

Jensen's inequality gives $\mathbb E(\varphi(X)\mid E_L)\ge\varphi(0)e^{-V/2}$. For the second derivative use $x^2e^{-x^2/2}\le x^2/(1+x^2/2)$ and concavity of $u/(1+u/2)$ on $u\ge0$. Consequently
$$
\begin{aligned}
 \sigma F(j)&\ge \varphi(0)e^{-V/2}-e_0-A_0-B_0=:G,\\
 \sigma^2|D_1F(j)|&\le .37+A_1+B_1=:J,\\
 \sigma^3D_2F(j)&\le \varphi(0)\big(V/(1+V/2)-e^{-V/2}\big)+e_2+A_2+B_2 .
\end{aligned}$$
The following parameters in those formulas suffice. The columns for $\gamma,\kappa,p$ are lower bounds. Use $\sqrt m\tanh(\gamma/(2\sqrt m))$ increasing in $m$ at fixed $\gamma$ to check the $\kappa$ column.

| $d$ | $\alpha$ | $\gamma$ | $\kappa$ | $d_{\max}$ | $p$ |
| ---: | --- | ---: | ---: | ---: | ---: |
| 24 | $(0,1]$ | 17.85 | 8.62 | .463 | .196 |
| 24 | $(1,2)$ | 27.74 | 12.81 | .762 | .104 |
| 48 | $(0,1]$ | 23.80 | 11.21 | .463 | .196 |
| 48 | $(1,1.5]$ | 27.74 | 12.81 | .636 | .149 |
| 48 | $(1.5,2)$ | 41.62 | 17.61 | .762 | .104 |

At $d=24$, $G>.21$, $J<.70$, and $.997z\gamma G-J>.20$. Since $(1-e^{-\alpha/m})\sigma\ge.997z\gamma$, this implies $F(j+1)>e^{-\alpha/m}F(j)$. Restoring the rank tilt gives strict growth. At $d=48$ the upper bound on $\sigma^3D_2 F(j)$ is below $-.01$. The tilted mass exceeds the arithmetic mean of its neighbors, hence also their geometric mean. Removing the tilt preserves strict log-concavity. This proves (1).

The [rational verifier](verify_rising.py) checks the suffix integrals, all block lengths and the five parameter cases. It bounds $e^{-x}$ above by the reciprocal of a positive Taylor sum and uses outward rational square-root bounds. The optional exact run computes the three adjacent coefficients at each new boundary in each family. At 385 rows both tests pass, just beyond the original full rank scan.

~~~sh
python3 -B verify_rising.py
python3 -B verify_rising.py --exact-n 385
~~~

The [finite curvature certificate](certified-window.md) covers the complementary interval through 2048 rows.
