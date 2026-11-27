# Inverting the last return with explicit errors

**Theorem.** For both central staircases the corank sequence is unimodal for every $n\ge5\cdot10^{11}$. At $n\ge2\cdot10^{10}$ the portion from $\lceil .18m^{3/2}\rceil$ onward is unimodal, contains every global maximum and has at most two consecutive global maximizers. Here $m=2n$ for the odd-part shape and $m=2n+1$ for the even-part shape. The [finite certificate](certified-window.md) covers $1\le n\le2048$. A [subsequent estimate](cubic-tilt.md) lowers the whole-row threshold to $10^{10}$ and the peak threshold to $10^6$.

The argument for the peak uses the real Fourier transform of a signed walk. A convolution inverse of norm at most two transfers an explicit input error to the surviving walks. Farther toward the full shape the sign requires a relative estimate. The [all-size growth theorem](moderate-saddle.md) brings the required range of positive tilts down to $h<16^3$, where a lower bound on the tilted density and the pair-deletion comparison suffice.

## A bound for the signed transform

Write $m+1=2N+\delta$ with $\delta=0,1$, $s_0=(2N)^{3/2}$ and $d=(m+1+\lceil m/2\rceil)/2$. For frequency $\theta=\xi/s_0$ set $u=|\xi|^{2/3}$, $\tau=u/N$. In the notation of the [last-return identity](return-expansion.md#splitting-at-zero), the signed transform $\Phi_N^\delta$ is the transform of the equally weighted values $\pm(k+d)$ for a random corank $k$. The free and bridge transforms satisfy $P^\delta=R*U^\delta$, $U_j^\delta=r_j\Phi_j^\delta$, $r_j=4^{-j}\binom{2j}{j}$. At every real frequency the inverse of $R$ is the unit mass at zero minus the first-return transform. Its absolute sum is at most two.

In variable $v=j\tau$ set $p=e^{-v^3/24}$, $\rho=e^{-v^3/96}$, $f(v)=\mathbb E\cos(v^{3/2}Y)$, $e(v)=\mathbb E\cos(v^{3/2}Y_E)$, where $Y,Y_E$ are half the Brownian meander and excursion areas. Write $[g]_{j,c}=\mathbb E g(\tau T)$ for $T$ of gamma shape $j+c$ and rate one. Put
$$
 V_\delta=-\tfrac8{15}(vf''+f'/2)
 +(\delta/2-3/20)\left(f'+(e-f)/(2v)\right).
$$
The quotient extends by continuity at zero. If $N\ge2\cdot10^{10}$ and $0\le u\le120$, then
$$
 \left|\Phi_N^\delta(\theta)-[f+\tau V_\delta]_{N,1/2}\right|
 \le 4\cdot822\,u^2/N^{3/2}. \tag{1}
$$

To bound the two inputs, use $g=p$ or $\rho$, with $c=1$ or $1/2$, respectively. Define
$$
 \ell_p=(2\delta+1)v^2/32+v^5/1920,\qquad
 \ell_\rho=v^2/192+v^5/30720,\qquad
 D_g=-g\ell_g-cg'-vg''/2 .
$$
For either input $W_j=P^\delta_j$ or $R_j/r_j$ we bound $|W_j-[g+\tau D_g]_{j,c}|\le A_g\tau^2$ for every $0\le j\le N$. Here are details for reproducing the constants.

* In the cosine or sinc products for $W_j$ the largest argument is $(2j+\delta)\tau^{3/2}/\sqrt{32}<.01$ and $\tau\le10^{-6}$. In $-\log\cos x$ and $-\log\operatorname{sinc}x$ the quadratic and quartic coefficients are $(1/2,1/12)$ and $(1/6,1/180)$. On this interval the omitted series have positive coefficients and are bounded by $x^6$. This follows by expanding the logarithms of the Euler products, bounding the sum of the sixth and higher terms by a geometric multiple of the quartic coefficient times $x^6$ (the smallest positive product zero is at least $\pi/2$). Thus $-\log W_j+\log g(v)-\tau\ell_g(v)$ is nonnegative and at most $\tau^2 L(v)$, where
$$
 L(v)=1+v+(1+v)^4/384+(1+v)^7/256 .
$$
  For the quadratic terms sum the squares exactly. For the fourth and sixth powers use $L_0^{b+1}\le(b+1)\sum_{i=1}^{L_0}i^b\le(L_0+1)^{b+1}$. For the bridge quartic difference the exact sum before scaling is $6j^5+7j^4+2j^3$. Its positive sixth-order remainder is bounded by the free numerator power sum, by monotonicity term by term. Exponentiation costs at most $\tau^2 g(L+\ell_g^2/2)$.
* For $T$ of shape $j+c$, the moments of $T-j$ of orders one and two are $c,j+c+c^2$. The third is positive and at most $5j+6$, and the fourth at most $3j^2+26j+24$. Taylor expand $g(\tau T)$ through degree three at $v$ and $D_g(\tau T)$ through degree one. The second-order error for $g$ after subtracting $\tau(cg'+vg''/2)$, in units $\tau^2$, is at most
$$
 \|g''\|+\|(1+v)g'''\|+\|(1+v)^2 g^{(4)}\| .
$$
  Here and for the correction this bound first charges the remainder on $T\ge j/2$, where intermediate times are at least $v/2$. For the fourth-order term the factor after taking the weighted norm is at most $4(3+26\tau+24\tau^2)/24<1$. The cost of $\tau([D_g]-D_g(v))$ in the same units is at most $\|D_g'\|+2\|(1+v)D_g''\|$. On $T<j/2$ one has $|T-j|\le j$ and probability at most $e^{-.19j}$ by the gamma transform at $-1$. Add the unweighted fourth and second norms times $\tau^2\sup j^4 e^{-.19j}/24$ and $\tau\sup j^2 e^{-.19j}/2$, respectively. These two exceptional costs sum to less than $.001$.
* All norms in these two steps are of polynomials times $e^{-v^3/b}$, $b=24,96$. The rational verifier bounds each monomial $v^l e^{-v^3/b}$ by $(lb/(3\mathrm e))^{l/3}$ for $l>0$ and uses one for $l=0$. This gives the stated $A_g$ by addition. It also gives $\|D_\rho\|$.

By the [gamma convolution and correction identities](return-expansion.md#gamma-averaging-and-the-first-correction), $[\rho]$ convolved with $[f]$ under weights $r_i r_{j-i}$ gives $[p]_{j,1}$. The two linear terms with $V_\delta,D_\rho$ give $[D_p]_{j,1}$. These are exact identities at step $\tau$. The weights sum to one. Consequently the residual in $P^\delta-R*U^a$ for $U^a_j=r_j[f+\tau V_\delta]_{j,1/2}$ is bounded by
$$
 \tau^2\{A_p+A_\rho(1+205\tau)+205\|D_\rho\|\}<822\tau^2 .
$$
The bound $\|V_\delta\|<205$ is proved below. Applying the inverse and $1/r_N\le2\sqrt N$ proves (1). The latter inequality also follows by induction from $r_1=1/2$ and $r_{N+1}/r_N=(2N+1)/(2N+2)$.

## Bounds from the Brownian area transforms

Let $a_j$ be the increasing Dirichlet eigenvalues of $-\partial_x^2+x$ on $x>0$, and $c_j$ the integral of its real eigenfunction normalized to derivative one at zero. In the principal branch the Laplace transforms of the half-areas are
$$
 L_Y(t)=\sqrt{\pi/2}\,t^{1/3}\sum_j c_j e^{-a_jt^{2/3}/2},\qquad
 L_E(t)=\sqrt{\pi/2}\,t\sum_j e^{-a_jt^{2/3}/2}.
$$
These follow from the classical area transforms with argument $t/2$. The series continue to $t=i v^{3/2}$ for $v>0$ by absolute convergence there. Their real parts are $f,e$. [Takács, meander area](https://www.cambridge.org/core/journals/journal-of-applied-probability/article/abs/limit-distributions-for-the-bernoulli-meander/D396ABE2C18FDCB75D12F270EED6FFEC) · [Majumdar and Comtet, excursion area, §II](https://arxiv.org/pdf/cond-mat/0409566#page=3) · [Janson, formulas for both transforms](https://arxiv.org/pdf/0704.2289)

Every eigenfunction with this normalization has squared norm one by integrating $((x-a_j)F^2-(F')^2)'=F^2$. Two integrations by parts as in the [real moment recurrence](moderate-saddle.md#height-moments-for-the-airy-trial-function) give $\int xF^2=2a_j/3$, $\int x^2F^2=8a_j^2/15$. Cauchy–Schwarz against $(1+x)^{-1}$ implies $|c_j|\le1+a_j$. Nodal intervals between successive zeros below the turning point have length at least $\pi/\sqrt{a_j}$ by the Dirichlet Poincaré inequality. There are $j-1$ such intervals from the wall to the last zero by Sturm oscillation, and no zeros in the decaying region. Thus $\#\{j:a_j\le x\}\le1+x^{3/2}/\pi$. The [real-energy bracket](variation-overlap.md#a-uniform-interval-in-corank) gives $2.337<a_1<2.339$. Integrating the count against $-[(1+x)^3e^{-x}]'$ gives $\sum_j(1+a_j)^3e^{-a_j}\le\int_0^\infty(1+x)^5e^{-x}dx<327$ (the count vanishes through $x=2$). It follows that for $v\ge8$,
$$
 D(v)=\sum_j(1+a_j)^3e^{-a_jv/4}\le3600e^{-.58v}.
$$

Write $Q=(e-f)/(2v)$. Differentiating the two absolutely convergent series gives, for $v\ge8$,
$$
 |f'|\le1.26(1+\sqrt v)D(v)/2,\quad
 |f''|\le1.26(3/4+\sqrt v/4)D(v),\quad
 |Q|\le .63\sqrt v(1+1/v)D(v).
$$
At every $v$ the [second moments](return-expansion.md#an-exact-check-on-the-correction) $\mathbb EY^2=59/240$ and $\mathbb E Y_E^2=5/48$ give
$$
 |f'|\le .75\sqrt v,\qquad |f''|\le .75v,\qquad
 |Q|\le\min(1/2,v^2/8,1/v).
$$
Indeed $|1-\cos x|\le x^2/2$ and $|\sin x|\le\min(1,|x|)$. Use the moment bounds through 22. Beyond 22 the spectral bounds give $|V_\delta|\le5\cdot3600v^{3/2}e^{-.58v}$, decreasing there. These estimates yield $\|V_\delta\|<205$.

## Inversion and the peak

Write $P_m(k)$ for the probability of corank $k$, and $F$ for the density of $Y$. For $N\ge2\cdot10^{10}$ and $z_0=(k+d)/s_0$, the absolute errors in $s_0P_m(k)$, $s_0^2\Delta P_m(k)$ and $s_0^3\delta^2P_m(k)$ compared with $F(z_0),F'(z_0),F''(z_0)$ are bounded respectively by
$$
 .000010,\qquad .008,\qquad 9 . \tag{2}
$$
Use the forward first and centered second differences. The comparison at integer $k\ge1$ only uses the positive branch of the signed lattice law, so the inversion integrals acquire the factor two. The density and forward difference bounds hold also at $k=0$.

Here are the integrals in the certificate. Cut at $|\xi|=T_0=120^{3/2}$. In the integral against $\xi^i d\xi$ over $[0,T_0]$, (1) costs at most $4\cdot822\,(3/(3i+7))T_0^{i+1}120^2/N^{3/2}$. For the difference between $[f+\tau V_\delta]_{N,1/2}$ and $f(u)$, Taylor expand about $u$. On each interval $a\le u\le b=a+1$ use $M_1,M_2,M_V$ given by the preceding derivative bounds on $[.99a,1.01b]$. The error is bounded by
$$
 \frac bN\left(M_1/2+(1+1/N)bM_2/2+M_V\right)+N^{-2}.
$$
Indeed the gamma mean displacement is $\tau/2$, and its mean square displacement at most $\tau^2(N+1)$. Outside $|T-N|\le.01N$ the gamma probability is below $3e^{-N/40000}$ by the exponential moment at $\pm.005$. Charge both bounded values of $f$, the linear term using Cauchy–Schwarz, and $\tau\|V_\delta\|$ on that event. The cost is below $2\cdot10^6e^{-N/80000}<N^{-2}$ using $u\le120$. Multiply each interval bound by $\tfrac32\sqrt b\,(b^{3/2})^i$ and sum.

Above $T_0$ both absolute transforms are bounded by $100e^{-.189u}$ through $|\theta|=10^{-9}$, and the continuum on the entire line. This uses the [fair first-hit bound](prefix-clock.md#a-fourier-block-stopped-at-its-first-hit) at the ballot scale, with $.19m/(2N)>.189$. Beyond that lattice frequency use the [full-period bound](peak-rate.md#fourier-inversion-for-lattice-differences) $8e^{-u/101}$. Half its exponent already has magnitude at least $2N\cdot10^{-6}/202$. For the multiplier errors integrate $\xi^2/(2s_0)$ and $\xi^4/(12s_0^2)$ against the continuum bound $100e^{-.19u}$, after first subtracting the transforms with the lattice multipliers. The extra lattice tail and multiplier errors combined are below $10^{-7}$ per order. In the main tail integral use $\int_A^\infty v^p e^{-cv}dv\le A^p e^{-cA}/(c-p/A)$ for $c>p/A$, $p\ge0$. Including the factor $2/\pi$ for reflection and the two frequencies proves (2).

For the sign use the [strip estimate and strong log-concavity argument](thinning.md#inversion-and-signs-around-the-maximum). For $g=\log F$ one has $g''\le-12$, and the unique mode $x_*$ satisfies $.19<x_*\le .65$ and $F(x_*)\ge1.78$. Throughout $[.18,x_*]$, wherever $g'\ge1$ one has $F'>.015$. Throughout $[x_*,.751]$, wherever $g'\le-1$ one has $F'<-.015$. In the intervening interval $|g'|<1$ one has $F''<-15.5$. Thus (2) fixes the signs on the flanks and makes successive forward differences strictly decrease across the middle. There can be only one turn, with at most two consecutive maximizers. For $.18\le k/m^{3/2}\le .75$ the site $z_0$ belongs to $[.18,.751]$, since $2N=m$ or $m+1$ and $d$ lies between $m/2$ and $m+1$. The [all-size first-passage and lower-half bounds](marked-hits.md) cover the rest from $.6m^{3/2}$ onward. All global maximizers are in the part just proved unimodal. Indeed $F(z)\le F(x_*)e^{-6(z-x_*)^2}$, so the density drops by more than twice the error in (2) at distance $.002$. Rounding the mode to a lattice site costs below $10^{-8}$ in density by the first-hit Fourier bound for $\|F'\|$. This proves the peak assertion.

## Height of a positively tilted meander density

Let $F_h(x)=e^{-hx}F(x)/L_Y(h)$, $h=r^3$. For every $r\ge4$,
$$
 \max F_h > .48r^2. \tag{3}
$$
For the first eigenfunction $\|F_1'\|_2^2=a_1/3$ by the real moment identity. At a maximum of $F_1^2$, integrate its derivative from both ends, then use Cauchy–Schwarz to get $\|F_1\|_\infty^2\le\|F_1\|_2\|F_1'\|_2<1$. Positivity and $\|F_1\|_2=1$ imply $c_1>1$. The second Airy eigenvalue exceeds $b=3.837$. If its interior node lies at or before $1.5$, its first nodal interval gives the lower energy bound $\pi^2/1.5^2$. Otherwise the remaining Dirichlet half-line has ground energy greater than $a_1+1.5$ by translation.

For $r' = r(1+w)^{1/3}$ at $w=0,\pm1/r$, put $t=(r')^2/2>6.60$. The excited-state sum in $L_Y((r')^3)$ has modulus less than $.003$ times its ground term. Indeed the bounds on $c_j$ and the counting function give, after integrating by parts starting just below $b$,
$$
 \sum_{j\ge2}(1+a_j)e^{-t(a_j-a_1)}
 \le \int_b^\infty 6.60(1+x)(1+x^2/3)e^{-6.60(x-2.339)}\,dx < .003 .
$$
Here first reduce $t$ term by term to $6.60$, use the upper count for $x\ge b$, and drop the derivative of $1+x$ in the resulting upper bound.

Under $F_h$ let $Z=r^2(Y-a_1/(3r))$. For each of the two signs its exponential moment is at most $(1.003/.997)(1+w)^{1/3}$ times the exponential of
$$
 \frac{a_1r^2}{2}\{1+2w/3-(1+w)^{2/3}\}
 \le \frac{2.339}{18}(1+.47/3).
$$
This follows from the transform ratio just proved. For the exponent use the second-order integral remainder and convexity to bound $(1+vw)^{-4/3}$ by $1+.47v$ at $0\le v\le1$, since $(3/4)^{-4/3}<1.47$. The mean of the two prefactors $(1+w)^{1/3}$ is at most one. Therefore $\operatorname{Var}(r^2Y)\le\mathbb E Z^2\le2(\mathbb E\cosh Z-1)$. A density of maximum $H$ has variance at least $1/(12H^2)$, since its probability within $v$ of its mean is at most $2vH$ and integration up to $1/(2H)$ bounds its second moment about that mean. Applying this to $r^2Y$ gives (3).

## Growth from the small-corank interval to the peak

Now let $m\ge10^{12}$ and $s=m^{3/2}$. It remains to prove $b_{k+1}>b_k$ for $s/16<k<\lceil .18s\rceil$. Write $z=(k+c_m)/s$ where $c_m=(m+\lceil m/2\rceil)/2$, and choose $h=(\log F)'(z)$. Then $1/16<z<.181$, so $h>0$ and $F_h$ has its maximum $H_*$ at $z$. If $h\le13$, the [fair derivative test](tilted-thinning.md#a-relative-transform-bound-and-the-adjacent-coefficient-sign) gives $F'(z)>.015$. The coordinate $z_0$ in (2) differs by at most $1/m$. The fair first-hit Fourier estimate gives $\|F''\|<4\cdot10^6$ by integrating $100t^2e^{-.19t^{2/3}}/\pi$. Thus (2) gives the strict sign here. For $h>13$, write $r=h^{1/3}$. At $r\ge7$ the [tilted-mode location estimate](variation-overlap.md#normalization-at-all-positive-tilts-and-location-of-the-tilted-mode) gives $z<a_1/(3r)+2.7/r^2$. Its upper bound at $r=16$ is less than $1/16$, so $r<16$.

We give the changes in the [tilted pair-deletion proof](tilted-thinning.md) to exhibit all length-dependent constants. With $X_m=(k+c_m)/s$ interpreted as a random variable under the uniform surviving law, $w=h-it$, $q=|w|$, for $13\le h\le16^3$ and $|t|\le500000$ we have
$$
 \frac{|\mathbb E e^{-wX_m}-\mathbb E e^{-wY}|}{L_Y(h)}
 \le\frac{70(1+r^2)+(30+5r^2+r^3)q+2q^2}{m}. \tag{4}
$$

1. In the deletion of flat pairs at length $4m+1$, retain the symmetric range $|J-m|\le .00003m$ for $J\sim\operatorname{Bin}(2m,1/2)$. Local lengths in the difference estimates then satisfy $|j/m-1|\le.000031$ and all intermediate dilation factors are within $.00004$ of one. Write $D=p_m L_Y(h)$ with $p_m$ the fair survival probability. For $j$ and $j-\lfloor m/(2r^2)\rfloor$ use the same Brownian clock upper comparison as in [(1) of the tilted proof](tilted-thinning.md#real-weights-and-the-absorbing-boundary). Both lengths $i$ are at least $.9m$ and the shifted tilt $u\le4100$. The logarithmic clock cost is at most
$$
 (4+1.26\cdot3(10+5/\sqrt i)+.5)4100/\sqrt i
       +3\max(2500,\log i)/\sqrt i.
$$
   Its upper bound decreases from the endpoint. The successful-clock fraction is at least $(1-4e^{-9/1.344})(1-5e^{-44})$. Including Wallis and the radial tail $i^{-4}$ gives the same mass bound $1.39p_i L_Y(u)$. For the ratio of Laplace masses the local exponent costs at most $1.17r^2(.00004+1.5\cdot .000031)$, plus $1.17\cdot .75$ at the shorter length. Hence the bounds $1.5D,3.8D$ still apply. The boundary estimate $9r^2D/m$ and the single, double and dilation differences [(4)–(6) there](tilted-thinning.md#cancellation-in-the-length-of-the-shorter-walk) follow with the same constants. In particular $|w|/(2s)<10^{-10}$. The omitted binomial probability is at most $2e^{-m(.00003)^2}\le D/m^2$.
2. In the [conditional variance comparison](tilted-thinning.md#the-average-over-placements-of-the-flat-pairs) use the same cap $2\sqrt{m\log m}$. The conditional geometric mean is at most $(1+.00003)/(1-.00003)$, so the log moment bound $1.2u^2$ remains valid at $|u|\le.01$. The exception bounds there still hold. For the cap use $(1.99-.51/\sqrt{\log m})^2/2>1.4+(\log4)/\log m$ from $\log m>27$. For the placement use $X=1.17r^2+4\log m+30$, obtaining $|V-V_0|\le1.17\sqrt{X\log m/m}$ on the retained event. With $h\le4096$ this gives $h|V-V_0|<.55$. At the lower length use $\log(10^{12})<28$ and note $X\log m/m$ decreases thereafter. The conditional mean comparison still gives $h|V_0-V_1|<.02$. The coefficient of $q^2D/m$ in the conditional Taylor cost is therefore at most
$$
 (33\cdot3.5+1.01\cdot1.5/m)e^{.57}/512<.41 .
$$
   All exceptional costs, including cancellation of the full linear term, are bounded as in the original proof. The endpoint inequalities for the change in the cap probability, the geometric concentration and the weighted exceptional terms are in the verifier.
3. Iterate at lengths $m,4m+1,\ldots$ as in the proof of the [relative transform estimate](tilted-thinning.md#a-relative-transform-bound-and-the-adjacent-coefficient-sign). The reciprocal lengths sum to at most $4/(3m)$. The coefficient of $q^2$ is at most $(4/3)(.51\cdot4/8+1.4/2+.41)<2$. The other coefficients retain their previous bounds, including the final $q/m$ cost for the endpoint height. This proves (4). In particular the centered real mass differs relatively from one by less than $.001$, and changing to the uncentered real tilt costs at most $e^{hc_m/s}<1.006$.

Invert the same adjacent-coefficient functional. If $G_k=e^{-hz}P_m(k)/L_Y(h)$ and $A=1/[s(1-e^{-h/s})]$, the lattice expression $sG_k+As^2(G_{k+1}-G_k)$ has the sign of $b_{k+1}-b_k$. The continuum expression at $z$ equals $H_*$ because $F_h'(z)=0$. Use $A\le1.001/h$. For $r<7$ take
$$
 T=\max\{yh,[(27+\min(h/2,1.17r^2))/c]^{3/2}\},
$$
with $(y,c)=(60,.16)$ through $r=4$ and $(40,.15)$ above four. For the bands with left endpoints $7,7.5,8,9,10.2,11.1,12,13.6$, take $T/h=35,30,25,20,15,12,10,8$, respectively. From (4) the central error relative to $H_*$ is bounded by
$$
 \frac{1}{\pi mH_*}\int_0^T(1+1.001t/h)
 \{70(1+r^2)+(30+5r^2+r^3)(h+t)+2(h^2+t^2)\}\,dt
 < .836 .
$$
The verifier subdivides $r$ at multiples of $.01$ and integrates each polynomial exactly using upper endpoints in the numerator and lower endpoints in the denominator. For the height use $H_*\ge\max(\sqrt{6/\pi},r/2.34)$ from the earlier tilted proof, and (3) from $r=4$. The lattice multiplier replacement costs less than $.001$ in absolute units.

For $r<7$ the two [first-hit tails](prefix-clock.md#a-fourier-block-stopped-at-its-first-hit) together cost less than $.003$ through $|t|/s=10^{-9}$ and for the full continuum tail. Their frequency and near-fair probability conditions hold since $T/h\ge40$, $T^{2/3}>100$ and $9h/(100\sqrt m)+h/s<.0001$. Beyond that lattice frequency split the [full-period exponent](mode-comparison.md#fourier-tails-for-the-two-signs-of-tilt) $-|t|^{2/3}/150$ in half. The first half has magnitude at least $m/(300\cdot10^6)>2500$, covering the prefactor $16e^{16r^2}$ and the remaining integrated tail with cost less than $.001$. For $r\ge7$ use the [block estimates through and beyond $|t|/h=150$](variation-overlap.md#bandwidth-and-error-bounds-outside-the-central-interval). Here $H=\sqrt m/r\ge62500$ and the number of blocks on the real height scale is at least $.49r^2$. The spacing condition $100\cdot150<\pi H$ and the real-energy allowance $2000(1+b)/H^4<.00001$ for $1<b\le2$ hold. At $|t|/s>1/64$ one has $|t|/h>H^3/64>10^4$. The integrated intermediate bands cost less than $.022H_*$, and the two outer estimates less than $.001H_*$ each, using the original weaker height bound $.21r^2$. In either range $H_*>1$, and the sum of all costs is strictly below $H_*$. This proves strict growth over the missing coranks and completes the theorem.

## Reproduction and remaining sizes

The first two commands verify the real Fourier error estimates and both parameter ranges for the positive-tilt comparison. All assertions use rational enclosures. The other commands independently check the signed return identity by enumerating sign words through length 18, the parity corrections by exact moments, and the ballot coefficients against direct enumeration of strict partitions through twelve rows.

~~~sh
python3 -B verify_return_bounds.py
python3 -B verify_tilted_thinning.py
python3 -B verify_return_expansion.py
python3 -B verify.py --max-n 64 --direct-n 12 --upper-curvature
~~~

Equation (2) also covers the peak below this note's whole-row threshold. For the current outstanding coranks and sizes see the [research summary](README.md#asymptotic-result-and-finite-size-gap).
