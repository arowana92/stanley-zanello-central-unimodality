# The second term in the location of the peak

For either central staircase put $m=2n$ or $2n+1$, $s=m^{3/2}$, and let $P_m(k)$ be the probability of corank $k$ under the uniform law on the shifted subdiagrams. Let $x_*$ be the unique mode of the density $f$ of half the area under a standard Brownian meander. Every maximizing corank satisfies
$$
 k=s x_*-\frac{3m}{4}+O\!\left(\sqrt m(1+\log m)^6\right).
$$
There is also a finite conclusion inside the outstanding size gap. For $m\ge10^{19}$ every nonempty upper level set $\{k:sP_m(k)\ge u\}$ with $u\ge.006$ is an interval, and the coefficients are unimodal on that interval. For $m\ge10^{20}$ the same holds down to $u=.001$. In either case there are at most two consecutive global maxima. The bounds allow secondary peaks below these levels.

The improvement comes from averaging the duration errors of the Brownian crossings and controlling the second difference with respect to **word length**. All estimates below concern the fair law. Put $c_m=(m+\lceil m/2\rceil)/2$. We prove the characteristic-function estimate
$$
 \left|\mathbb E e^{it(K+c_m)/s}-\int e^{itx}f(x)\,dx\right|
 \le \frac{10^4(1+|t|)^2}{m}\qquad(m\ge10^8,\ t\in\mathbb R), \tag{1}
$$
where $K$ has law $P_m$. Centering the two areas this way removes an error of order $m^{-1/2}$.

## A coupling at the absorbing boundary

Write $H_i$ for the heights of a fair sign walk, $S_j=\sum_{i=0}^{j-1}H_i$ and $A_j=\{\min_{i\le j}H_i\ge0\}$. For even $j=2d$ the mass $b_j=\Pr(A_j,H_j=0)=4^{-d}C_d$ involves the Catalan number $C_d$. Couple uniform excursions of lengths $2d$ and $2d+2$ so that $S_{2d+2}\ge S_{2d}$. To do this, encode a full planar binary tree recursively as $U L D R$, where $L,R$ encode its two subtrees and a leaf encodes the empty word. Choose any of its $2d+1$ vertices uniformly. Replace its subtree word $W$ with $UW D$ or $UDW$, each with probability one half. This is Rémy's tree growth. Each output tree with a distinguished new leaf recovers the old tree, chosen vertex and order by removing the leaf and contracting its parent. Each output has $d+2$ leaves, proving uniformity. Both insertions increase left-height area, since the current height is nonnegative. [Rémy growth and uniformity, Evans, Grübel and Wakolbinger](https://arxiv.org/abs/1411.2526)

The excursion mean is $M_d=4^d/C_d-(2d+1)$. Indeed, if $C(z)=1+zC(z)^2$ and $V(z)$ enumerates the sums of $S_{2d}$, first return with a left excursion of semilength $i$ adds $2i+1$. Hence
$$V=2zCV+2z^2 C'C+zC^2,\qquad V=(C-1)/(1-4z).$$
Its coefficient is $4^d-(2d+1)C_d$ by the Catalan ratio, including $d=0$. Monotonicity of the coupling makes the mean **absolute** increment exactly $3(4^d/C_d)/(2d+1)-2$. By $4^d/\binom{2d}{d}\le2\sqrt d$ for $d\ge1$, this is at most $5\sqrt m$ for $m/2-4\le 2d\le2m+4$, $m\ge10^8$.

## Dependence on word length at fixed frequency

Fix $\alpha=t/(2s)$, $p=\Pr(A_m)$ and set $G_j(\alpha)=\mathbb E[1_{A_j}e^{i\alpha S_j}]$. In the window $m/2-4\le j\le2m+4$ we have $\Pr(A_j)\le3p$, $b_j\le20p/m$ at even indices, and $\mathbb E[\max_{i\le j}H_i^2\mid A_j]\le43m$. The first two follow from the central binomial bounds $1/(2\sqrt m)\le p$, $\Pr(A_j)\le1/\sqrt{j+1}$ and $b_{2d}\le(d+1)^{-3/2}$. The last is the [conditional maximal height estimate](peak-rate.md#coupling-the-area-while-retaining-the-wall). Write $v=1+|t|$.

One step changes $G$ by at most $11pv/m$. Use $|e^{i\alpha h}-1|\le|\alpha|h$ on surviving paths. Killing costs at most $b_j/2$ if $j$ is even and costs zero if $j$ is odd. For $\Delta_2 G_j=G_{j+2}-G_j$ there is an extra power of $m$ in the second difference:
$$ |\Delta_2^2G_j|\le250p v^2/m^2 \qquad(j\text{ even}). \tag{2}$$
For a two-step transition from height $h$ use the phase $e^{i\alpha(2h+u)}$, where $u$ is the first sign and $w$ the second. Put $L(h)=e^{2i\alpha h}\cos\alpha-1$, and $B_j=\mathbb E[1_{A_j,H_j=0}e^{i\alpha S_j}]$. Then
$$\Delta_2G_j=\mathbb E[1_{A_j}e^{i\alpha S_j}L(H_j)]-\tfrac12 e^{-i\alpha}B_j.$$
On applying another two steps to the first term, the unrestricted increment at $h$ is $L(h)^2$ plus the average of $e^{i\alpha(2h+u)}(L(h+u+w)-L(h))$. The latter has modulus at most $|\cos(3\alpha)\cos(2\alpha)-\cos\alpha|\le7\alpha^2$. Removing the forbidden transitions at zero costs at most $5|\alpha| b_j$, since $|L(h)|\le|\alpha|(2|h|+1)$. For the boundary term the excursion coupling gives
$$ |B_{j+2}-B_j|\le b_j(7+3|t|)/m.$$
Here $b_{j+2}/b_j=(j+1)/(j+4)$ and the difference of the two phases costs at most $5|\alpha|\sqrt m$. Combining these bounds with the conditional height moment proves (2).

Allow the frequency to change by a factor $c=m/j$. Write $D_j=\mathbb E[1_{A_j}i\alpha S_j e^{i\alpha S_j}]$. Then $|D_m|\le 3p|t|$ and $|D_{j+1}-D_j|\le100p(|t|+t^2)/m$. For the latter bound, use $|i(x+y)e^{i(x+y)}-ix e^{ix}|\le |y|(1+|x|)$ with $y=\alpha H_j$. The additional mass killed at zero contributes at most $b_j|\alpha|M_{j/2}/2$ at even $j$, where the excursion mean above is at most $3m^{3/2}$. On $m/2\le j\le2m$, $\mathbb E[1_{A_j}(\alpha S_j)^2]\le130pt^2$. Taylor expansion in $c$, using $c-1=-(j-m)/m+(j-m)^2/(jm)$, gives
$$ \left|G_j(c\alpha)-G_j(\alpha)+\frac{j-m}{m}D_m\right|
 \le 500p v^2(j-m)^2/m^2. \tag{3}$$

## Averaging the crossing clock

In the [Brownian embedding](peak-rate.md#coupling-the-area-while-retaining-the-wall), let $T_i$ be successive times that Brownian motion $B$ has moved one unit and let $D_i^*=T_i-T_{i-1}$. The signs are independent of the durations, which have mean one, second moment $5/3$ and $\mathbb E e^{D_i^*/2}=1/\cos(1)<2$, $\mathbb E e^{-D_i^*}=1/\cosh(\sqrt2)$. These transforms follow by solving the exit-time equation on $[-1,1]$. Write $J=\max\{i:T_i\le m\}$, $a=m-T_J$, $G=\{m/2\le J\le2m\}$. Brownian survival above $-1$ up to time $m$ is exactly $A_J$ up to null events. The two exponential moments give $\Pr(G^c)\le 2e^{-.1m}$ by testing $T_{\lceil m/2\rceil}$ and $T_{2m}$.

The interval covering $m$ satisfies $\mathbb E D_{J+1}^*<11$, $\mathbb E(D_{J+1}^*)^2<400$. Indeed, any interval of length one contains at most $1+\mathbb E J_1<4$ renewal epochs in expectation, where $J_1=\max\{i:T_i\le1\}$ and $\mathbb E J_1\le e/(\cosh(\sqrt2)-1)$. Start counting at the first epoch in the interval and use independence of subsequent durations. Group the candidate left endpoints $T_{i-1}\le m$ by $l\le m-T_{i-1}<l+1$. Summing $4\mathbb E[(D_1^*)^b 1_{D_1^*\ge l}]$ over $l\ge0$ gives $4\mathbb E[(D_1^*)^b(1+D_1^*)]$ as an upper bound for the $b$th moment. For $b=2$ use $\mathbb E(D_1^*)^3\le48\mathbb E e^{D_1^*/2}<96$.

For $L=\min(J+1,2m+1)$ the stopped sum $T_L-L$ has mean zero and second moment $(2/3)\mathbb E L$. On $G$, $J-m=(L-T_L)+(T_L-m)-1$, with $0\le T_L-m\le D_{J+1}^*$. Cauchy–Schwarz on $G^c$ and the preceding moment bounds imply
$$ |\mathbb E[(J-m)1_G]|\le13,\qquad \mathbb E[(J-m)^2 1_G]\le4m. \tag{4}$$
Also $\mathbb E[1_G\sum_{i\le J}(D_i^*)^2]\le (5/3)(2m+1)<4m$.

In (2), take the discrete Taylor expansion from $m_0=2\lfloor m/2\rfloor$ to $2\lfloor j/2\rfloor$. With $l=(G_{m_0+2}-G_{m_0})/2$, the error in $G_j-G_m-(j-m)l$ is at most $40pv/m+65pv^2(|j-m|+4)^2/m^2$. This follows by summing (2) over the triangle of intervening two-step increments and using the one-step bound at the two parity corrections. In particular $|l|\le11pv/m$. Equations (3) and (4) now give
$$ \left|\mathbb E[1_G G_J(m\alpha/J)]-\Pr(G)G_m(\alpha)\right|
 \le 2600pv^2/m. \tag{5}$$
For the constants, the two linear terms cost at most $(11+3)13$, the parity terms 40, the length remainder $65(2+4/\sqrt m)^2$, and the frequency remainder $500\cdot4$, all in units of $pv^2/m$.

To compare the Brownian integral $R=\int_0^m B_u\,du$ with $(m/J)S_J$, record for each completed crossing its duration and its integrated displacement from the left endpoint multiplied by its exit sign. Denote the latter mark by $V_i$, with $|V_i|\le D_i^*$. Reflection makes the pair $(D_i^*,V_i)$ independent of its sign. Given $J=j$, the unordered list of these $j$ pairs and the age $a$, their ordering is uniform and independent of the first $j$ signs. This follows by permuting whole completed crossings, since $T_j\le m<T_{j+1}$ depends only on their total duration and the next crossing.

For fixed surviving signs write $M=\max_{i\le j}H_i$. Subtract the empirical means of the two lists in the sums $\sum H_{i-1}D_i^*$ and $\sum (H_i-H_{i-1})V_i$. The resulting sums have conditional mean zero and respective conditional second moments at most $2M^2\sum(D_i^*)^2$ and $2\sum(D_i^*)^2$. This uses the variance of a random permutation sum, $\sum(x_i-\bar x)^2\sum(y_i-\bar y)^2/(j-1)$. The remaining error in $R-(m/j)S_j$ has absolute value at most $(2a+2)M+a$. In fact the mean duration is $(m-a)/j$, the mean mark has modulus at most $m/j\le2$ on $G$, the signs sum to $H_j$, and the incomplete crossing lies within one of $H_j$.

The conditional mean error, integrated on $G\cap A_J$, therefore costs at most $480p\sqrt m$ in absolute value, also when multiplied by any unit-modulus function of the signs and the conditioning data. Its full second moment on this event is below $3200pm^2$. For the latter bound square the sum of the two centered terms and the remainder using $(x+y+z)^2\le3(x^2+y^2+z^2)$. After the signs are averaged, the contribution is at most
$$9p\big[2(43m+1)4m+8(400+22+1)43m+800\big].$$
We used $a\le D_{J+1}^*$, $\Pr(A_j)\le3p$ and the conditional height moment. Taylor's inequality $|e^{iz}-1-iz|\le z^2/2$ and (5) now show that
$$ \left|\mathbb E[1_{A_J} e^{i\alpha R}]-G_m(\alpha)\right|\le4000pv^2/m.$$
The rare event costs at most $2\Pr(G^c)$. At $t=0$ this bounds the difference in survival probabilities by $4000p/m$. Normalizing the two expectations costs at most another $4000v^2/m$ after division by $p$, using that the conditional Brownian characteristic function has modulus at most one.

## Moving the Brownian starting point to zero

Add one to the Brownian path in the integral, multiplying the characteristic function by $e^{i\alpha m}$. After space and time rescaling this gives half the area from starting height $d=m^{-1/2}$ conditional on survival to time one. In the [three-dimensional radial representation](peak-rate.md#starting-height-and-meander-law), take standard Brownian motion $W$ and an independent uniform unit vector $U$. The area $Y_d=\tfrac12\int_0^1 |W_v+dU|\,dv$ has the desired law after weighting by $g_d=1/|W_1+dU|$ and normalizing. At $d=0$ it gives $f$. Write $g=g_0$. Angular averaging gives
$$
 \mathbb E_U g_d=1/\max(d,|W_1|),\qquad
 0\le \mathbb E_U[|W_v+dU|-|W_v|]\le d^2/(2|W_v|).
$$
The first follows by integration in the polar cosine and the second by Jensen applied to the norm and then to the square root. Consequently $\mathbb E[g-\mathbb E_U g_d]\le d^2/2$ by the radial Gaussian density. Also $\mathbb E|g_d-g|\le d$ by the reciprocal-square moments from the radial representation. Use $|Y_d-Y_0|\le d/2$ for the product of the weight and phase changes. In the term with weight $g$, average the linear Taylor term in $Y_d-Y_0$ over $U$ first. Its cost is at most $|t| d^2/2$, since $\mathbb E[g/|W_v|]\le v^{-1/2}$. The quadratic error is at most $t^2 d^2/8$. Including the change of normalization, using $\mathbb E g_d>.48$, gives an error below $5v_t^2/m$, where $v_t=1+|t|$.

Finally $2K=S_m+H_m-\lceil m/2\rceil$. Replacing $\alpha(S_m+m)$ by $t(K+c_m)/s$ costs at most $3|t|/m$ under $A_m$. This proves (1). The same shift works for both endpoint parities.

## Fourier inversion and the peak

For $|t|/s=\theta\le1/64$ the shifted and unshifted characteristic functions have modulus at most $40e^{-.12|t|^{2/3}}$. Here is a direct improvement to the [fair paired-label bound](peak-rate.md#fourier-inversion-for-lattice-differences). In an unrestricted block of $2l$ fair steps, pair labels a distance $l=\lceil3.25\theta^{-2/3}\rceil$ apart when $\theta>0$. The row sum of the endpoint moduli at each harmonic $d=1,2$ is at most $\rho_d=e^{-d^2 l^3\theta^2/16}$, since $2l\theta<\pi$. Rotate each endpoint phase by the argument of its retained sum. For the rotated path angle $z$, the surviving contribution to the real part is bounded by
$$ (\cos z)_+\le3/8+(\cos z)/2+(\cos 2z)/8.$$
This follows from $|x|\le(1+x^2)/2$. Summing over the unrestricted paths gives row bound $3/8+\rho_1/2+\rho_2/8<e^{-.83}$. The rotation does not affect the absolute harmonic bounds. Condition on survival for a prefix of length $\lfloor m/64\rfloor$, costing a factor at most 16. Multiply the block bounds on the remaining steps, using $l\theta^{2/3}\le3.3125$. The floor in the number of blocks costs less than $e^{.83}$. This proves the envelope, including $t=0$. The limit inherits it for every real $t$.

For $x=(k+c_m)/s$, approximate $sP_m(k),s^2\Delta P_m(k),s^3\delta^2 P_m(k)$ respectively by $f(x),f'(x),f''(x)$, using the forward first and centered second lattice differences. The uniform absolute errors are as follows.

| Word length | Fourier cutoff $T$ | Density | First derivative | Second derivative |
| --- | ---: | ---: | ---: | ---: |
| $m\ge10^{19}$ | 2680 | $.000003$ | $.0054$ | $12.3$ |
| $m\ge10^{20}$ | 3040 | $.0000004$ | $.00088$ | $2.3$ |

For order $i=0,1,2$, integrate (1) below $T$ against $|t|^i/(2\pi)$. Above $T$, the two envelopes cost at most
$$ \frac{120}{\pi}\,(.12)^{-b}\frac{e^{-z}z^{b-1}}{1-(b-1)/z},
 \qquad b=3(i+1)/2,\quad z=.12T^{2/3}.$$
Include the additional lattice tail above $s/64$ via $8e^{-.01|t|^{2/3}}$, extracting $e^{-m/3200}$. This tail and the lattice multiplier errors together cost less than $10^{-12}$ in each row. For the latter use the same lattice envelope on the full period and multiplier discrepancies $t^2/(2s)$ and $t^4/(12s^2)$ respectively. The [verifier](verify_centered_clock.py) bounds the integrals by rational numbers.

Between two sites meeting the stated level, log-concavity puts $f$ above $.0054$ throughout in the first row and above $.00088$ in the second. If $g=\log f$ has $|g'|\ge1$, the first-difference sign therefore agrees with $g'$. For $|g'|<1$, the [curvature bound](peak-window.md#curvature-of-the-limiting-density) $g''\le-12$ puts the point within $1/12$ of the mode, so $f\ge e^{-1/12}\sqrt{6/\pi}$. Consequently $f''\le-11f<-12.3$. The centered second difference is strictly negative throughout that middle region. Since $g'$ decreases, these three sign tests yield the claimed unimodal interval. The [finite variance bound](mode-bounds.md#height-of-the-maximum-from-the-exact-variance) gives $s\max P_m>1.78$, ensuring that the level includes the global maxima. The strictly decreasing differences in the middle allow a tie of at most two.

For the asymptotic assertion, take $T=(100\log m)^{3/2}$. The first derivative error is $O((1+\log m)^6/m)$ by (1) and the same integration. At a maximizing site the two adjacent differences straddle zero, so $|f'(x)|$ has this bound there, using bounded $f''$ for the shift by $1/s$. The density estimate and $s\max P_m>1.78$ bound $f(x)$ away from zero. Then $12|x-x_*|\le |f'(x)|/f(x)$. Multiplication by $s$ and $c_m=3m/4+O(1)$ give the peak expansion. The small-coefficient tails in the outstanding sizes are still needed for global unimodality.

~~~sh
python3 -B verify_centered_clock.py
python3 -B verify.py --max-n 12 --direct-n 12 --upper-curvature
~~~
