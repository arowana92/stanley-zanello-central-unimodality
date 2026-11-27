# Comparing ballot areas after a positive tilt

**Theorem.** For both central staircases, the rank sequence is unimodal for every $n\ge10^{13}$. More precisely, put $m=2n$ for $(2n-1,2n-3,\ldots,1)$ and $m=2n+1$ for $(2n,2n-2,\ldots,2)$. With $s=m^{3/2}$, the corank counts increase strictly at every integer step $s/35<k<\lceil .18s\rceil$ in this size range. The [all-size estimate](folded-saddle.md) gives strict growth up to $s/35$. The [fair pair-deletion theorem](thinning.md) gives unimodality on the rest of the row and places every maximum there. These three ranges cover every step.

The new comparison retains the cancellation in the length of the shorter walk after weighting by area. At positive tilt a boundary return is rare, and its weighted change on adding two steps matters. We first estimate this change, then control the area fluctuations conditional on the shorter walk.

## Real weights and the absorbing boundary

Let $A_j$ be survival through time $j$ of a fair sign walk from zero, let $p_j=\Pr(A_j)$, and write $S_j=\sum_{i=0}^{j-1}H_i$ for its left-endpoint area. Let $Y$ have the law of half the unit Brownian meander area, with density $f$, and put $L(h)=\mathbb E e^{-hY}$. Throughout,
$$
 m\ge 2\cdot10^{13},\quad 13\le h=r^3\le31^3,\quad
 w=h-it,\quad |t|\le500000,\quad q=|w|,\quad
 \alpha=-w/(2s),\quad D=p_m L(h).
$$
In the following estimates the local indices satisfy $|j/m-1|\le.000011$, allowing rounding and four additional steps, and the real scale factor $b$ is in $[1-.00002,1+.00002]$. Put $L_0=\lfloor m/(2r^2)\rfloor$. Then
$$
 \mathbb E[e^{-bh S_i/(2s)};A_i]\ \le\
 \begin{cases}1.5D&i=j,\\3.8D&i=j-L_0.\end{cases} \tag{1}
$$

Here are details for the absolute normalization in (1). For $i\ge.9m$, $u=bh(i/m)^{3/2}\le29800$, apply the [centered Brownian clock comparison, (1)–(4)](centered-displacement.md#a-centered-displacement-estimate) with length $i$, cap $\lceil10\sqrt i\rceil$, $V=3\sqrt i$, and earlier deterministic time $i-V$. Given any signs, its two duration estimates succeed with probability at least $1-4e^{-9/1.344}$. The cap discards a fraction at most $5e^{-44}$ of the real surviving mass weighted by $e^{-uK_i/i^{3/2}}$, by the [height association and hitting bound](prefix-clock.md#shortening-the-walk-before-testing-a-clock-failure). On success the capped walk implies Brownian survival at the earlier time. Comparing the two areas there costs $3/\sqrt i+1.26V(\lceil10\sqrt i\rceil+4)/i^{3/2}$ in displacement. The [radial comparison](localized-mode.md#positive-tests-under-the-random-clock) adds $1/\sqrt i$ in displacement, $3R^2/\sqrt i$ in log weight and at most $i^{-4}$ in units $i^{-1/2}I_u(0)$, where $R=\max(50,\sqrt{\log i})$ and $I_u(0)=\sqrt{2/\pi}\,L(u)$. Its discarded-tail estimate uses $I_u(0)\ge e^{-16R^2}$, which follows here from Jensen and the [Airy ground-state bound](variation-overlap.md#normalization-at-all-positive-tilts-and-location-of-the-tilted-mode). Finally $2K_i=S_i+H_i-\lceil i/2\rceil$, so changing $K_i$ to $S_i/2$ costs a factor at most $e^{u/(2\sqrt i)}$. Wallis bounds $i^{-1/2}\sqrt{2/\pi}/p_i\le\sqrt{1+2/i}$. Combining the factors gives an upper bound $1.39p_i L(u)$. The same proof gives this bound at any single length $i\ge.9m$ and $0\le u\le29800$ for which the radial denominator bound holds.

For $r\ge13^{1/3}$ the Airy bound $I_h(0)\ge (r/2)e^{-ar^2/2}$, $a<2.339$, gives $L(h)\ge e^{-1.17r^2}$. Thus $L(u)/L(h)\le\exp[1.17r^2(1-u/h)_+]$ by concavity of the power $v^{u/h}$ when $u<h$. For the shorter length use $r^2(1-u/h)_+\le .75+r^2(.00002+1.5\cdot.000011)$. For the local indices the $.75$ term drops out. Applying Wallis once more proves (1).

Under survival, positive tilt by left area reduces expectations of increasing functions of the heights. The surviving Markov walk can be generated from independent uniforms by ordered one-step transitions. The same argument applies with an additional prescribed endpoint, since on each parity class different current heights have ordered next-step supports. The [fair conditional height estimates](thinning.md#comparing-the-characteristic-functions-at-lengths-m-and-4m1) give $\mathbb E[H_i\mid A_j]\le1.27\sqrt m$ and $\mathbb E[H_i^2\mid A_j]\le2.31m$ for each local terminal time $j$ and $0\le i\le j$. In units $D$, (1) therefore bounds the weighted first and second moments by $2\sqrt m$ and $3.5m$. The mixed moment $H_j S_j$ and second moment $S_j^2$ are at most $3.51m^2$ and $3.51m^3$ in the same units, by Cauchy–Schwarz.

Write $B_j=\mathbb E[e^{\alpha S_j};A_j,H_j=0]$ and let $B_j^h$ denote its real positive counterpart. Dropping the tilt on the last $L_0$ steps gives
$$ B_j^h\le9r^2 D/m. \tag{2} $$
Indeed the killed transition from height $a$ to zero in $l=L_0$ steps equals $[2(a+1)/(l+a+2)]\Pr(W_l=a)$ for a fair unrestricted walk $W$ and compatible parity. This follows by reflection. The [binomial point bound](prefix-clock.md#a-fourier-block-stopped-at-its-first-hit) gives $\sup_a a\Pr(W_l=a)<.49$ and Wallis gives $\sup_a\Pr(W_l=a)<.056$ at these lengths. The transition is at most $1.1/l$. Apply (1) to the prefix.

**Tree-growth identity.** For a uniform Dyck excursion of even length $j=2d$, encode a planar full binary tree by $U L D R$ recursively, with the empty word at a leaf. For its tree $T$ put $S=S_j$ and let $S^\mathrm{mir}$ be the left area of the tree with left and right children interchanged throughout. If $T'$ is the next tree under Rémy growth, then
$$
 S(T')\ge S(T),\qquad
 \mathbb E[S(T')-S(T)\mid T]
 =1+\frac{5S+S^\mathrm{mir}}{2(j+1)}. \tag{3}
$$
The heights at the $j+1$ word positions are precisely the left depths of the vertices in preorder, including the final position at height zero. This follows directly by applying the encoding to each child. Thus $S+S^\mathrm{mir}$ is the sum of ordinary vertex depths. Choose a uniform vertex and replace its word $W$ by $UWD$ or $UDW$ with equal probability. The area increment at height $v$ is $2v+1$, plus $|W|$ in the first case. Summing $|W|/2$ over choices gives $\sum_{\rm internal}(1+\mathrm{depth})$ by counting ancestors. This is half the sum of all depths, since every nonroot vertex is one of the two children of an internal vertex. Averaging proves (3). The larger tree is uniform because marking the new leaf determines the inverse contraction and every output tree has the same number of leaves. [Rémy growth, Evans, Grübel and Wakolbinger](https://arxiv.org/abs/1411.2526)

The same construction gives an all-size polynomial identity. Let $C_d(x)=\sum_T x^{K(T)}$ for excursion corank $K(T)=(S(T)-d)/2$, and write $[a]_x=\sum_{i=0}^{a-1}x^i$, including $[0]_x=0$. For a vertex $v$ let $h_v$ be its left depth and $d_v$ its number of internal subtree vertices. Then
$$
 \frac{2(2d+1)C_d(x)-(d+2)C_{d+1}(x)}{1-x}
 =\sum_T x^{K(T)}\sum_{v\in T}\bigl([h_v]_x+[h_v+d_v]_x\bigr).
$$
Indeed the two placements increase corank by $h_v$ and $h_v+d_v$. Sum the two differences over trees and marked vertices, counting each larger tree $d+2$ times. In particular the quotient has nonnegative integer coefficients for every $d$. This compares the cumulative counts of excursions at successive lengths. Unimodality of the central families concerns individual counts after summing over the allowed endpoints.

For a fair excursion, the [marked-height tail](marked-hits.md#an-excursion-with-a-marked-vertex) has $\Pr(H_I>v)\le e^{-v^2/(j/2+1)}$ for a uniform vertex $I$. Integration gives $\mathbb E S/(j+1)<.64\sqrt m$. The same upper bound holds after a positive tilt by the endpoint-conditioned association above. For the mirror term in (3), truncate the marked height of the mirrored tree at $r\sqrt m$ and use the *unweighted* tail for the excess. Its integral is at most $.26\sqrt m\,e^{-1.99 r^2}/r$ by the Gaussian tail inequality. The fair returning mass is $2p_j/(j+2)\le2.1p_m/m$ at these even lengths. Since $L(h)\ge e^{-1.17r^2}$, (3) gives
$$
 \mathbb E[e^{-hS/(2s)}(S(T')-S(T)); A_j,H_j=0]
 \le (r+2)\sqrt m\,B_j^h+D/\sqrt m .
$$
Here the expectation includes the random vertex and orientation. The ratio of the returning masses at $j+2,j$ is $(j+1)/(j+4)$. Monotonicity of the increment gives $|e^{\alpha S'}-e^{\alpha S}|\le|\alpha|(S'-S)e^{\Re\alpha S}$. Consequently
$$
 |B_{j+2}-B_j|\le (D/m^2)\,[28r^2+(4.5r^2(r+2)+1)q]. \tag{4}
$$

## Cancellation in the length of the shorter walk

Put $G_j(\alpha)=\mathbb E[e^{\alpha S_j};A_j]$ and $D_j=\mathbb E[\alpha S_j e^{\alpha S_j};A_j]$. With $\Delta$ the unit forward difference and $\Delta_2$ the forward difference of step two, (1)–(4) imply
$$
\begin{aligned}
 |\Delta G_j|/D &\le (q+4.5r^2)/m,\\
 |\Delta_2^2G_j|/D &\le [15r^2+(3r^2(r+2)+2)q+4q^2]/m^2
       &&(j\text{ even}),\\
 |D_j|/D &\le1.01q,\qquad
 |\Delta D_j|/D\le[(1+2r^2)q+.9q^2]/m .
\end{aligned} \tag{5}
$$
For a single step bound the phase change by $|\alpha|H_j$ and the killed mass by $B_j^h/2$. For the last difference the phase change costs at most $|\alpha|H_j(1+|\alpha|S_j)$ times the old real weight. The killed derivative costs at most $|\alpha|B_j^h(j+1).64\sqrt m/2$. For the even second difference use the [exact two-step formula](centered-clock.md#dependence-on-word-length-at-fixed-frequency) with $U(v)=e^{2\alpha v}\cosh\alpha-1$. The unrestricted term at height $v\ge0$ has modulus bounded by $|U(v)|^2+7.1|\alpha|^2$. Indeed the second summand factors as $e^{4\alpha v}\cosh\alpha$ times $\cosh(3\alpha)\cosh(2\alpha)-\cosh\alpha$. The power series bounds its modulus by $7.1|\alpha|^2$ at $|\alpha|<10^{-10}$. Also $|U(v)|\le1.001|\alpha|(2|v|+1)$ for $v\ge-2$. The forbidden transitions from zero in that term cost at most $5.1|\alpha| B_j^h$. The remaining boundary difference costs at most $.501|B_{j+2}-B_j|$. Substitution of the two height moments and (2), (4) gives (5).

For the comparison with length $M=4m+1$, remove the first obligatory up-step and delete flat pairs. Before imposing survival, $J\sim\mathrm{Bin}(2m,1/2)$ is the number of moving pairs. Survival of the remaining signs is $A_J$. Let $l=j-m$, $c=m/j$ and retain the symmetric event $G=\{|J-m|\le10^{-5}m\}$. Taylor expansion in the real factor $c$ gives
$$
 |G_j(c\alpha)-G_j(\alpha)+(l/m)D_m|
 \le D(l/m)^2[(2.1+2.1r^2)q+1.4q^2]. \tag{6}
$$
Use $c-1=-l/m+l^2/(jm)$, (5) for $D_j-D_m$, and (1)'s weighted bound on $S_j^2$ for every intermediate factor between $1$ and $c$. Next set $m_0=2\lfloor m/2\rfloor$ and $d_0=(G_{m_0+2}-G_{m_0})/2$. In $G_j-G_m-l d_0$ sum the even second differences from $m_0$ to $2\lfloor j/2\rfloor$. The number counted with multiplicity is at most $(|l|+4)^2/8$ by the triangular sum. The two single-step corrections and the change in the linear term cost in total at most three times the first bound in (5). On $G$ both linear terms in $J-m$ have mean zero. We use $\mathbb E(J-m)^2=m/2$ and $\mathbb E(|J-m|+4)^2<.51m$. The omitted probability is at most $2e^{-10^{-10}m}\le D/m^2$ by Hoeffding, Wallis and the lower bound on $L(h)$.

## The average over placements of the flat pairs

Let $Z_i=(S_i+i)/(2i^{3/2})$. For a retained skeleton $(z_0,\ldots,z_j)$ write $V=Z_M$, $V_0=\mathbb E[V\mid j,z]$ and $V_1=(cS_j+m)/(2s)$. All fine-walk expectations in this section start after the obligatory up-step. By the [exact conditional moments for the pair placement](thinning.md#exact-law-after-deleting-flat-pairs),
$$
 |V_0-V_1|\le (17S_j/m+6z_j+4)/(16s),\qquad
 \operatorname{Var}(V\mid j,z)\le(33m V_z+1.01m)/(256m^3),
$$
where $V_z$ is the uniform variance of the slot heights $z_i$. We have $h|V_0-V_1|<.02$ even with $S_j\le j^2$ and $z_j\le j$. Switching between the two mean phases costs at most $4qD/m$ after integration by (1) and its weighted first moments. In the variance bound, $V_z\le\sum_i z_i^2/(j+1)$ has integrated weight at most $3.5mD$ against $e^{-hV_1}$.

Cap the skeleton at $K=2\sqrt{m\log m}$. Under either surviving fair walk of length $i=j,M$, first reaching $\lceil\sqrt i/2\rceil$ before absorption costs at most $1/(1+\lceil\sqrt i/2\rceil)$. An additional climb of $a\sqrt i$ by time $i$ costs at most $e^{-a^2/2}$ by the exponential maximal inequality. Dividing by $p_i$ and using association, the probability under the surviving law tilted by left area of exceeding $K$ at length $j$, or $2K$ at length $M$, is at most
$$ 4\exp[-(1.99\sqrt{\log m}-.51)^2/2]\le m^{-1.4}. $$
Whenever the skeleton exceeds $K$ the fine walk exceeds $2K$, since its heights at pair endpoints are $2z_i+1$. This inclusion estimates the fine contribution even though $J$ depends on the fine walk. The total unnormalized fine real mass is at most $1.39(2p_M)L(h)$ by the real comparison already proved. Together with (1), this bounds the discarded weighted contributions of $V$ and $V_1$ by $3D/m$.

For each retained capped path put $d=j+1$, $v=2m-j$, $\mu=v/d$. The numbers $g_i$ of flat pairs at the successive slots form a uniform weak composition of $v$. Equivalently these are independent geometric variables of mean $\mu$ conditioned on their sum being $v$. The conditioning event has probability at least $1/(20\sqrt m)$. Indeed the sum has variance $d\mu(1+\mu)<2.01m$. Chebyshev puts at least one half of its mass within $2.1\sqrt m$ of $v$. Its negative-binomial mass at $k+1$ divided by that at $k$ is $(k+d)\mu/[(k+1)(1+\mu)]$, so a mode is within two of $v$ and the adjacent ratios there exceed $.99$ in either direction toward $v$. For $|u|\le.01$ the centered geometric log moment generating function is bounded by $1.2u^2$. Its second derivative is $\mu(1+\mu)e^u/(1+\mu-\mu e^u)^2<2.4$ on this interval.

Set $X=1.17r^2+4\log m+30$. Except on a conditional event of probability at most $42\sqrt m\,e^{-X}$, we have
$$
 \left|\sum_i(g_i-\mu)z_i\right|\le2.3K\sqrt{mX},
 \qquad |B-v/2|\le2\sqrt{mX},
$$
where $B\sim\mathrm{Bin}(v,1/2)$ is the independent color count. For the first inequality apply the geometric exponential bound with parameter $2.3K\sqrt{mX}/(2.4dK^2)$ to either sign, using $\sum z_i^2\le dK^2$, then divide by the conditioning probability. The largest single argument is below $.01$. Hoeffding gives the second inequality. The random part of $2M^{3/2}V$ is $4\sum_i g_i z_i+2B$. Hence on the good event
$$ |V-V_0|\le1.17\sqrt{X\log m/m},\qquad h|V-V_0|<1.57. $$
Taylor expansion at $V_0$ now costs at most $\tfrac12 q^2 e^{1.57-hV_0}(V-V_0)^2$ beyond the linear term. Use the variance above and $e^{-hV_0}\le e^{.02-hV_1}$ to get an integrated cost $\le1.12q^2D/m$. The full conditional linear term has expectation zero. On the exceptional event bound the two exponentials by one and $|V-V_0|\le10\sqrt{\log m}$ by the cap. Multiplying $2+10q\sqrt{\log m}$ by $42\sqrt m\,e^{-X}$ costs at most $D/m$ even before imposing skeleton survival. All endpoint bounds decrease with $m$ after the indicated powers of $m$ are divided out. In particular $(1.17r^2+4\log m+30)\log m/m$ decreases once $\log m>30$.

## A relative transform bound and the adjacent-coefficient sign

The survival mass after the first up-step is $p^*=2p_M=\mathbb E p_J$ and $|p^*/p_m-1|<1/m$ by Wallis. The real upper bound $1.39 L(h)$ for the normalized fine transform allows a cost of $2D/m$ before normalizing. The surviving transform of $V_1$ at fixed $j$, before division by survival probability, is exactly $e^{\alpha m}G_j(c\alpha)$. Combining the preceding bounds, the difference of the two conditional transforms of $Z_M,Z_m$, in units $L(h)/m$, is at most
$$
\begin{split}
 &3(q+4.5r^2)+\frac{.51}{8}\,[15r^2+(3r^2(r+2)+2)q+4q^2]\\
 &\hspace{12mm}+\tfrac12[(2.1+2.1r^2)q+1.4q^2]+4q+1.12q^2+10.
\end{split}
$$
The constant ten covers the cap, the exceptional conditional event, the two discarded binomial tails and normalization. Iterate along $m\mapsto4m+1$ at the same $h,t$. The sum of reciprocal lengths is at most $4/(3m)$. The [conditioned meander limit](peak-window.md#differentiable-local-limits) applies to the bounded continuous function $e^{-wz}$ on $z\ge0$. With $c_m=(m+\lceil m/2\rceil)/2$ put $X_m=(K_m+c_m)/s=Z_m+H_m/(2s)$. Changing $Z_m$ to $X_m$ costs at most $qL(h)/m$ by the weighted first height moment. Collecting terms gives
$$
 \frac{|\mathbb E[e^{-wX_m}\mid A_m]-\mathbb E e^{-wY}|}{L(h)}
 \le \frac{70(1+r^2)+(30+5r^2+r^3)q+5q^2}{m}. \tag{7}
$$
At $t=0$ the right side is below $.001$. Consequently the real mass of the centered lattice law divided by $p_m L(h)$ is within $.001$ of one when computed before conditioning on survival. The uncentered real mass differs by the factor $e^{hc_m/s}<1.006$, and $p_m L(h)/[m^{-1/2}I_h(0)]$ differs from one by at most $2/m$. These bounds justify using the earlier Fourier tail estimates in their stated mass range $(.7,1.4)$.

Take $s/35<k<\lceil .18s\rceil$, $z=(k+c_m)/s$ and $h=(\log f)'(z)$. Then $1/35<z<.181$ and the mode of $f$ exceeds $.19$, so $h>0$. For $h\le13$ the [fair derivative test](centered-displacement.md#which-tilts-need-a-comparison) applies with tilt chosen at $z$ itself. Indeed $f(z)\ge e^{-13/2}\sqrt{6/\pi}>.002$ by Jensen and the height of the tilted mode. If $f(z)\ge.15$, strong log-concavity gives $f'(z)\ge.15\cdot12(.19-.181)>.015$. Otherwise the secant to the mode gives $f'(z)\ge f(z)\log(1.78/f(z))/.65>.015$. The fair first-difference error is smaller. For $h>13$ one has $r<31$ because the [upper bound on the tilted mode](variation-overlap.md#normalization-at-all-positive-tilts-and-location-of-the-tilted-mode) gives $z<a/(3r)+2.7/r^2$ at $r\ge7$.

The tilted probability density $f_h=e^{-h\,\cdot}f/L(h)$ has $f_h'(z)=0$. Denote its maximum by $H_*=f_h(z)$. Strong log-concavity gives $H_*\ge\sqrt{6/\pi}$. Also $\mathbb E_hY\le-\log L(h)/h\le1.17/r$ by convexity of $\log L$. Any density on the positive half-line bounded by $H_*$ has mean at least $1/(2H_*)$, by integrating the survival probability above $1-H_*x$ up to $1/H_*$. Hence $H_*\ge r/2.34$. At $r\ge7$ use also the established bound $H_*\ge.21r^2$ from the [real tilted concentration estimate](variation-overlap.md#normalization-at-all-positive-tilts-and-location-of-the-tilted-mode).

Write $F(k)=e^{-hz}\Pr(K_m=k\mid A_m)/L(h)$ and $A=[s(1-e^{-h/s})]^{-1}\le1.001/h$. Positivity of $sF(k)+As^2(F(k+1)-F(k))$ is equivalent to strict growth of the original counts. The continuum counterpart is $f_h(z)+Af_h'(z)=H_*$. For $|t|\le T$ use Fourier inversion and (7) directly. The multiplier has modulus at most $1+A|t|$, and replacing its difference part by the differential multiplier costs at most $At^2/(2s)$. The relative error over this interval, apart from the latter cost, is bounded by
$$
 \frac1{\pi m H_*}\int_0^T(1+1.001t/h)
 \{70(1+r^2)+(30+5r^2+r^3)(h+t)+5(h^2+t^2)\}\,dt. \tag{8}
$$
The centering $c_m$ enters both the tilt and the inversion site. No estimate for a derivative of the error transform is needed.

For $r<7$ use $B=\min(h/2,1.17r^2)$ and $T=\max(yh,[(27+B)/c]^{3/2})$. Take $(y,c)=(60,.16)$ through $r=4$ and $(40,.15)$ thereafter. For $r\ge7$ use $T=yh$ with the following left endpoints.

| $r$ | 7 | 7.5 | 8 | 9 | 10.2 | 11.1 | 12 | 13.6 | 16.7 | 20.2 | 28.4 |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| $y$ | 35 | 30 | 25 | 20 | 15 | 12 | 10 | 8 | 6 | 4.5 | 3 |

The [rational verifier](verify_tilted_thinning.py) bounds (8) by $.91$ uniformly on these bands. It takes closed intervals of width $.01$ in $r$, increases $T$ and every nonnegative polynomial coefficient to its endpoint upper bound, and uses endpoint lower bounds on $h,H_*$. In particular $T<125000$ and the absolute multiplier error $AT^3/(6\pi s)$ is below $.001$ on every interval.

For clarity, the following bounds for the omitted frequencies include both laws and frequency signs.

* At $r<7$ the [first-hit table](prefix-clock.md#a-fourier-block-stopped-at-its-first-hit) gives the envelope $100e^{B-c|t|^{2/3}}$ through $|t|/s=10^{-9}$ for the normalized transforms. Its dependence on $B$ is only through $I_h(0)>.7e^{-B}$, which follows from Jensen and the Airy bound above. For its near-fair sign parameters one has $\beta\lceil9\theta^{-2/3}\rceil<.0001$ for $\theta\ge T/s$, $\beta=h/s$. The centered real lattice normalization costs at most $1.001$. In the tail integral substitute $u=c t^{2/3}$ and use $U=27+B\le85$. The two polynomial factors at $U$ are bounded by $(U+1)/\sqrt U$ and $U^2+2U+2$ after extracting $e^{-U}$. This gives an absolute cost below $.003$. Beyond $|t|/s=10^{-9}$ the [full-period positive-tilt bound](mode-comparison.md#fourier-tails-for-the-two-signs-of-tilt) has prefactor $16e^{16r^2}$ and exponent at most $-|t|^{2/3}/150$. Even using $1/4000$ in this exponent, half gives at least $m/(8000\cdot10^6)\ge2500$ in magnitude. Integrating the remainder costs below $.001$.
* For $r\ge7$ the [intermediate-frequency bands](variation-overlap.md#bandwidth-and-error-bounds-outside-the-central-interval) apply with height scale $H=\sqrt m/r>140000$ and $N=\lfloor m/2\rfloor/H^2\ge.49r^2$. Harmonic spacing holds through $|t|/h=150$ since $100\cdot150/H<\pi$. For the real-energy loss with conjugate Hölder exponent $1<b\le2$, use the [fourth-order grid estimate](airy-grid.md) at scales $H,H/b^{1/3}$. In $H^2(p(b\beta)/b-p(\beta))$ the linear corrections cancel, the quadratic correction is nonpositive, and the remainders sum to at most $2000(1+b)/H^4<.00001$. This verifies the energy allowance in the [block calculation](power-overlap.md). The ground-mass comparison, the real spectral gap and the same two end blocks therefore give relative cost less than $.022$ through 150. The verifier sums the band bounds at each new left endpoint. Beyond 150 the two [integrated estimates](variation-overlap.md#bandwidth-and-error-bounds-outside-the-central-interval) each cost less than $.001H_*$, using $N\ge.49\cdot49$.

These estimates leave the signed adjacent functional positive, since the relative central error is below $.91$, the multiplier costs below $.001H_*$ and the combined tails below $.026H_*$. This proves the stated strict growth and the theorem. The outstanding sizes for the original conjecture are $2049\le n<10^{13}$ after the [finite certificate for both families](certified-window.md).

## Reproducing the checks

The first command checks (3) at every growth choice from every tree with at most seven internal vertices, as well as the rational inequalities in the proof. The second compares exact pair-deletion polynomials and moments with direct enumeration for both families through twelve rows. The third independently compares the ballot recurrence and Catalan recurrences with the partitions themselves. These finite enumerations check the combinatorial inputs. Uniformity in $n$ in the theorem comes from the inequalities above.

~~~sh
python3 -B verify_tilted_thinning.py
python3 -B verify_thinning.py
python3 -B verify.py --max-n 64 --direct-n 12 --upper-curvature
python3 -B verify_prefix_clock.py
python3 -B verify_variation.py
~~~
