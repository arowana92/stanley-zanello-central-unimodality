# Deleting flat pairs and locating the peak

Let $m=2n$ for the odd-part central staircase and $m=2n+1$ for the even-part staircase. Put $s=m^{3/2}$ and $D=\lfloor m^2/4\rfloor$. For a uniform shifted subdiagram, $P_m(k)=b_k/\binom{m}{n}$ is the probability of missing $k$ cells, where $b_k=a_{D-k}$.

**Theorem.** For both families and every $n\ge10^{13}$, the sequence $(b_k)_{k=\lceil .18s\rceil}^{D}$ is unimodal and contains every global maximum. There are at most two consecutive global maximizers. Every nonempty set $\{k:sP_m(k)\ge u\}$ with $u\ge.016$ is an interval. Together with [strict growth through $s/35$](folded-saddle.md), this reduces the outstanding step at these sizes to proving weak growth for $s/35<k<\lceil .18s\rceil$. The [tilted pair-deletion comparison](tilted-thinning.md) proves that step for every $n\ge10^{13}$.

## Exact law after deleting flat pairs

A surviving sign walk has corank $K_m=\sum_{i=1}^m\lfloor H_i/2\rfloor$, where $H_i$ is its height after step $i$. Remove the forced first up-step and split the remainder into $L=\lfloor(m-1)/2\rfloor$ pairs and $v=m-1-2L$ final steps. A pair starting at height $2z+1$ moves up or down two units, or holds with one of two colors. On the scale of $z$ the moving pairs form a surviving ordinary sign walk of length $j$ and heights $z_0=0,\ldots,z_j=e$. Both hold colors are allowed at zero. The final single sign, when present, is unrestricted. [Paired-step weights](paired-steps.md#an-exact-stabilization-identity)

Before conditioning on survival and after the first up-step, $J\sim\mathrm{Bin}(L,1/2)$. Given $J=j$, the directions of the moves are independent fair signs. Survival is precisely survival of those signs. Given any surviving sequence of moves, the $w=L-j$ holds have counts $(g_0,\ldots,g_j)$ in its $j+1$ slots distributed as a uniform weak composition of $w$. Indeed each possible placement of the $j$ moves is equally likely. The $w$ colors are independent fair coins. Write $S_j=\sum_{i<j}z_i$ (starting at $i=0$), $Q_j=S_j+e$, and $B\sim\mathrm{Bin}(w+v,1/2)$ independent of the composition. Conditional on these moves,
$$
 K_m=2S_j+(j+3e)/2+2\sum_{i=0}^jg_i z_i+ve+B .
$$
The moving pairs add $2z+2$ for up and $2z-1$ for down. A hold costs $2z$ plus its color. In particular this gives the whole conditional counting polynomial by multiplying $q^{2S_j+(j+3e)/2+ve}(1+q)^{w+v}$ by the complete homogeneous polynomial of degree $w$ in the $j+1$ variables $q^{2z_i}$.

Let $V_z$ be the variance of the numbers $z_0,\ldots,z_j$ under the uniform distribution on slots. Then
$$
 \mathbb E[K_m\mid z]=\frac{2(L+1)Q_j}{j+1}+\frac{L-e}{2}+v(e+1/2),\qquad
 \operatorname{Var}(K_m\mid z)=\frac{4w(L+1)}{j+2}V_z+\frac{w+v}{4}. \tag{1}
$$
For $d=j+1$ exchangeable boxes the mean of a count is $w/d$. Its second factorial moment is $2w(w-1)/(d(d+1))$ and the mixed moment for different boxes is half that. These follow by differentiating $[t^w]\prod_i(1-u_it)^{-1}$ at $u_i=1$ and dividing by the composition count. Substitution gives (1), including $j=0$.

## Comparing the characteristic functions at lengths $m$ and $4m+1$

Write $A_l$ for survival of a fair walk to length $l$, $p_l=\Pr(A_l)$, $p=p_m$, and $S_l=\sum_{i=0}^{l-1}H_i$. Set $Z_m=(S_m+m)/(2s)$ and $M=4m+1$. We prove
$$
 |\mathbb E(e^{it Z_M}\mid A_M)-\mathbb E(e^{it Z_m}\mid A_m)|
 \le (5+8|t|+t^2)/m \qquad(m\ge10^8). \tag{2}
$$

For the fine walk $L=2m$ and $J\sim\mathrm{Bin}(2m,1/2)$ before imposing survival on the moving signs. Take $G=\{|J-m|\le m/200\}$. Its complement has probability at most $2e^{-m/40000}$ by Hoeffding. The following bounds allow all intermediate indices $.99m\le j\le1.01m$, including parity corrections. Wallis gives $\sqrt{2/(\pi(l+2))}\le p_l\le\sqrt{2/(\pi l)}$ for $l\ge1$. Consequently $p_j/p\le1.02$. At even $j$ the boundary mass $b_j^0=\Pr(A_j,H_j=0)=2p_j/(j+2)$ is at most $2.1p/m$. For $i\le j$,
$$
 \mathbb E[H_i;A_j]/p\le1.26\sqrt m,\qquad
 \mathbb E[H_i^2;A_j]/p\le2.3m .
$$
Indeed the walk $H_i+1$ absorbed at zero has first moment one and third moment $1+3i$ by the one-step recursion. Its second moment is at most $\sqrt{1+3i}$ by Cauchy–Schwarz. Restrict either moment to $A_j$ and divide by the Wallis lower bound.

Put $\alpha=t/(2s)$, $a=|t|$, $v_t=1+a$, $G_j(\alpha)=\mathbb E[e^{i\alpha S_j};A_j]$ and $D_j=\mathbb E[i\alpha S_j e^{i\alpha S_j};A_j]$. We need the following estimates for the unnormalized functions:
$$
\begin{aligned}
 |G_{j+1}-G_j|/p&\le 1.1v_t/m, &
 |G_{j+4}-2G_{j+2}+G_j|/p&\le4v_t^2/m^2\quad(j\text{ even}),\\
 |D_m|/p&\le .63a, &
 |D_{j+1}-D_j|/p&\le(2.3a+.60a^2)/m .
\end{aligned} \tag{3}
$$
For one step the phase costs $|\alpha|\mathbb E[H_j;A_j]$ and absorption costs at most $b_j^0/2$ at even $j$. For two successive two-step differences use the [two-step formula and excursion coupling](centered-clock.md#dependence-on-word-length-at-fixed-frequency). Its unrestricted term is bounded by $\alpha^2\mathbb E[(2H_j+1)^2+7;A_j]$. Removing forbidden steps costs at most $5|\alpha|b_j^0$. The remaining boundary term costs at most $b_j^0(3/(j+4)+5|\alpha|\sqrt m)/2$ by the Catalan mass ratio and the monotone excursion coupling there. The two height moments above give the stated constants. For the last difference use $|i(x+y)e^{i(x+y)}-ixe^{ix}|\le|y|(1+|x|)$, $y=\alpha H_j$. By Cauchy–Schwarz the mixed height bound is $\mathbb E[H_j S_j;A_j]/p\le2.3mj$. At a killed step the additional cost is at most $b_j^0|\alpha|(3m^{3/2})/2$ using the excursion mean in the same proof. Jensen also gives $\mathbb E[(\alpha S_j)^2;A_j]/p\le .59a^2$.

For $l=j-m$, $c=m/j$, Taylor expansion in $c$ now gives
$$
 |G_j(c\alpha)-G_j(\alpha)+(l/m)D_m|/p
 \le (3.1a+.93a^2)l^2/m^2 . \tag{4}
$$
Use $c-1=-l/m+l^2/(jm)$, $|c-1|\le1.02|l|/m$ and (3) for the change of $D$. For the change of length set $m_0=2\lfloor m/2\rfloor$ and $d_0=(G_{m_0+2}-G_{m_0})/2$. Summing the even second differences in (3) bounds the error in $G_j-G_m-l d_0$, divided by $p$, by
$$ 3.3v_t/m+ v_t^2(|l|+4)^2/(2m^2). $$
The first term allows both single steps and the correction of their linear part. The second bounds the triangle of two-step increments in either direction. On $G$ the linear terms in $J-m$ average to zero by binomial symmetry. Also $\mathbb E(J-m)^2=m/2$ and $\mathbb E(|J-m|+4)^2<.51m$.

It remains to compare the fine area at fixed $j$ with the phase in (4). In the fine numerator $S_M+M$, use $2K_M=S_M+H_M-\lceil M/2\rceil$ and $H_M=2e+1$. Formula (1) gives its conditional mean
$$ 4(2m+1)(S_j+e)/(j+1)+8m+1-3e. $$
The target numerator is $d((m/j)S_j+m)$ with $d=(M/m)^{3/2}\in[8,8+4/m]$. The coefficients of $S_j$ differ by at most $17/m$, the coefficient of $e$ has modulus at most six and the constants differ by at most four. Integrating the absolute difference of the conditional means on $A_j$ costs at most $32p\sqrt m$. The conditional variance of the fine numerator is $16w(2m+1)V_z/(j+2)+w$ by (1). Its integral on $A_j$ is at most $76pm^2$, using the average second height moment to bound $V_z$. Taylor expansion about the conditional mean, then the Lipschitz bound for the mean displacement, cost at most $p(2a+.16a^2)/m$ since $2M^{3/2}\ge16s$. The resulting expression in the characteristic function is exactly $e^{i\alpha m}G_j(m\alpha/j)$.

Finally the exceptional lengths cost at most $2\Pr(G^c)/p<.001/m$. The survival mass after the first obligatory up-step is $p^*=\mathbb E p_J=2p_M$. Wallis gives $|p^*/p-1|<1/m$. To normalize, compare the unnormalized expectations in units of $p$ and use that the normalized fine characteristic function has modulus at most one. Collecting the costs gives (2): in units $1/m$ they are bounded by
$$
 3.3v_t+.255v_t^2+(3.1a+.93a^2)/2+2a+.16a^2+.001+1.
$$

## Inversion and signs around the maximum

Iterate (2) along $m\mapsto4m+1$. The reciprocal lengths sum to at most $4/(3m)$. The [conditioned walk limit](peak-window.md#differentiable-local-limits) gives the law of $Y$, half the unit Brownian meander area, with density $f$. Put $c_m=(m+\lceil m/2\rceil)/2$. The difference between $(K_m+c_m)/s$ and $Z_m$ is $H_m/(2s)$, with conditional mean at most $.63/m$. Thus the centered finite and limiting characteristic functions differ by at most
$$ (7+12|t|+1.34t^2)/m . \tag{5} $$

For $m\ge2\cdot10^{13}$ and $z=(k+c_m)/s$, the errors in approximating $sP_m(k),s^2\Delta P_m(k),s^3\delta^2P_m(k)$ by $f(z),f'(z),f''(z)$ are below $.000016,.015,15.5$ respectively. Here $\Delta$ is the forward difference and $\delta^2$ the centered second difference. Integrate (5) up to $T=1200$ against $t^i/\pi$ for orders $i=0,1,2$. Above $T$ use the [fair first-hit bound](prefix-clock.md#a-fourier-block-stopped-at-its-first-hit) $100e^{-.19t^{2/3}}$ for both transforms through $t=10^{-9}s$, and on the whole line for the limit. With $w=.19T^{2/3}$ and $b=3(i+1)/2$, their combined tail costs at most
$$ (300/\pi) (.19)^{-b}e^{-w}w^{b-1}/(1-(b-1)/w). $$
The [full-period bound](peak-rate.md#fourier-inversion-for-lattice-differences) $8e^{-t^{2/3}/100}$ handles the extra lattice tail by extracting $e^{-m/(2\cdot10^8)}$. It also controls multiplier errors $t^2/(2s)$ and $t^4/(12s^2)$ over the full period. These additional errors total less than $10^{-7}$ per order.

Write $g=\log f$. We use $g''\le-12$, $f(x_*)\ge1.78$ and $.19<x_*\le.65$ for the unique mode $x_*$. These follow from [strong log-concavity](peak-window.md#curvature-of-the-limiting-density), the [moment lower bound on its location](peak-rate.md#a-bound-for-the-largest-coefficients-before-global-unimodality-is-known) and the [finite height and location bounds](mode-bounds.md) by uniform convergence. Between any two sites at scaled height at least $.016$, log-concavity gives $f(z)>.015$ throughout. Thus where $|g'(z)|\ge1$ the forward difference has the sign of $g'$. Where $|g'(z)|<1$ the mode is within $1/12$ and $f''(z)\le-11 f(x_*)e^{-1/12}<-15.5$. The centered second difference is strictly negative there. Since $g'$ decreases, the signed differences allow only a single turn between the two sites. This proves the superlevel assertion and the bound on ties.

In addition, all global maximizers have $|z-x_*|<.002$. Indeed $f(z)\le f(x_*)e^{-6(z-x_*)^2}$. At distance $.002$ the drop exceeds twice the density error plus $10^{-8}$. Rounding the mode to the nearest lattice site costs less than $10^{-8}$ in $f$, using the integral of $8t e^{-t^{2/3}/100}/\pi$ to bound $\|f'\|_\infty$. Thus every maximum lies above corank $.18s$.

## A strip bound for the small-area probability

For any integer $H\ge0$ of the same parity as $m$, at least half of the walks surviving in $[0,H]$ satisfy
$$ K_m\le (m+1)H/4-\lceil m/2\rceil/2. \tag{6} $$
This holds separately at each final height $y$, with $y$ in place of $H$ in the additive term $H/4$. For a reachable endpoint, take the uniform strip bridge from zero to $y$. Reversing time and reflecting about $H/2$ gives a uniform strip bridge from $H-y$ to $H$. The second bridge stochastically dominates the first pathwise. Indeed the matrix of fixed-length strip path counts has nonnegative two-by-two minors for ordered starts and ends on compatible parities. A pair of paths with inverted endpoints must meet, and swapping their suffixes after the first meeting injects it into the pairs with ordered endpoints. At equal current heights this minor inequality makes the up-step probability nondecreasing with the target endpoint. Couple the two next steps by one uniform variable. At unequal heights the gap is at least two, preserving order automatically. Induction proves domination, including forced steps.

The trapezoid area $T=S_m+y/2$ of the upper bridge is distributed as $mH-T$ for the lower bridge. Therefore at least half the lower bridges have $T\le mH/2$. Since $2K_m=T+y/2-\lceil m/2\rceil$, this proves (6).

Take $H/\sqrt m\to b=4a>0$ along the prescribed parity. The unconditioned fair strip survival probability, with $d=H+2$, is
$$ \frac2d\sum_{1\le l<d,\ l\ \mathrm{odd}}
 (1+\cos(\pi l/d))\cos^m(\pi l/d). $$
Indeed the normalized adjacency matrix of the interval has sine eigenvectors and eigenvalues $\cos(\pi l/d)$. Summing the terminal sine vector gives zero for even $l$ and $\cot(\pi l/(2d))$ for odd $l$. After multiplying by $\sqrt m$, the limit is $(4/b)\sum_{l\ge1,\ l\ \mathrm{odd}}e^{-\pi^2l^2/(2b^2)}$. To pass to the limit split the sum at $d/2$. The reflected high modes have a factor $1-\cos(\pi(d-l)/d)$ tending to zero for fixed $d-l$. Both sides are bounded by summable Gaussians from $\cos x\le e^{-x^2/2}$ for $0\le x\le\pi/2$. Dividing (6)'s count by $p_m\sim\sqrt{2/(\pi m)}$ and using weak convergence and continuity of the area law yields
$$ \Pr(Y\le a)\ge\frac{\sqrt{2\pi}}{4a}
 \sum_{l\ge1,\ l\ \mathrm{odd}}e^{-\pi^2l^2/(32a^2)} . \tag{7} $$
The strip survival limit itself is classical. [Chung, *Excursions in Brownian motion*](https://archive.ymsc.tsinghua.edu.cn/pacm_download/116/7247-11512_2006_Article_BF02385832.pdf)

For $.18\le z\le x_*$, (7) and monotonicity give $f(z)\ge\Pr(Y\le .18)/.18>.0013$. If $g'(z)\ge1$ and $f(z)\ge.016$ the first-difference sign follows directly. At smaller densities concavity gives
$$ f'(z)\ge f(z)\log(1.78/f(z))/(x_*-z)>.0013\cdot7/.47>.015 . $$
Here $v\log(1.78/v)$ increases on $[.0013,.016]$. For $x_*\le z\le .751$ the [Gaussian regression bound](airy-overlap.md#the-decreasing-side-in-corank) gives $f(z)\ge1.78 e^{-6z^2}>.015$, sufficient wherever $g'(z)\le-1$. The same strict second-difference test covers $|g'(z)|<1$. At $.75s$ these signs overlap the [all-size first-passage bound](hit-tilts.md), and weak decrease in corank beyond the rank midpoint follows from the [lower-half inequality](monotonicity.md#1-lower-half-for-all-sizes). This completes the theorem.

The verifier reconstructs every coefficient from the smaller walks, checks both conditional moments for every skeleton against the exact polynomial, and compares with direct enumeration of strict partitions through twelve rows. It separately checks the fixed-end strip domination and the rational bounds used in (2), (5) and inversion.

~~~sh
python3 -B verify_thinning.py
python3 -B verify.py --max-n 64 --direct-n 12 --upper-curvature
~~~
