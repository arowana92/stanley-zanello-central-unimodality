# A lower bound for the corank difference at small Brownian area

**Theorem.** In each of the odd- and even-part staircases of Conjecture 3.4, the rank sequence is unimodal whenever $n\ge10^{10}$. Its corank counts $b_k$ increase strictly from $k=0$ through the step into the peak interval $k\ge\lceil .145m^{3/2}\rceil$. Already at $n\ge10^6$ that interval is unimodal and contains every global maximum, with at most two consecutive maximizers. Here $m=2n$ for the odd-part shape and $m=2n+1$ for the even-part shape.

The main estimate below is a positive lower bound for an adjacent difference after tilting. We choose the tilt explicitly from the corank. This permits a direct bound on the continuum derivative and reduces the frequency range needed for its lattice counterpart. The [finite certificate](certified-window.md) covers both rows through $n=2048$. The two all-size conjectures remain unresolved in this draft.

## A cubic contour for the derivative

Let $Y$ be half the unit Brownian meander area, $F$ its density, $L$ its Laplace transform, and $F_h(x)=e^{-hx}F(x)/L(h)$. For complex $w$ in the right half-plane the classical Airy expansion is
$$
 L(w)=\sqrt{\pi/2}\,w^{1/3}\sum_i c_i e^{-a_iw^{2/3}/2}.
$$
Here $a_i$ are the Dirichlet eigenvalues of $-\partial_t^2+t$ on the positive half-line and $c_i$ is the integral of the eigenfunction normalized to have derivative one at zero. We use $2.337<a=a_1<2.339$, $c_1>1$, $a_2>b=3.837$, $|c_i|\le1+a_i$, and $\#\{a_i\le t\}\le1+t^{3/2}/\pi$. [Area transform, derivation and spectral bounds](return-bounds.md#bounds-from-the-brownian-area-transforms) · [Takács](https://doi.org/10.2307/3215294) · [Janson, §22 and Appendix C.3](https://arxiv.org/pdf/0704.2289)

For $x>0$ put $r_i=a_i/(3x)$, $A_i=a_i r_i^2/2$. Laplace inversion of $w^jL(w)$ gives the following real Gaussian integral for $j=0,1$:
$$
 F^{(j)}(x)=\frac{3}{2\sqrt2}\sum_i
    \frac{c_i r_i^{4+3j}}{\sqrt{A_i}}e^{-A_i/3} I_{3+3j}(A_i),
 \qquad I_p(A)=\Re\,\mathbb E[(1+iV)^p e^{-2iAV^3/3}],
 \quad V\sim{\cal N}(0,1/(2A)).
 \tag{1}
$$
Indeed on any fixed vertical inversion line in the right half-plane, $\Re(w^{2/3})\ge |w|^{2/3}/2$. This permits summation and differentiation under the integral and moving the line to $\Re w=r_i^3$ separately for each summand. With $\zeta=(w/r_i^3)^{1/3}$ the integrand is a polynomial times $\exp[A_i(2\zeta^3/3-\zeta^2)]$. Move the image contour to $\Re\zeta=1$. On the horizontal connecting segment at imaginary part $v$, the real exponent divided by $A_i$ is $2t^3/3-2tv^2-t^2+v^2$, $t=\Re\zeta\ge1$. It has no interior maximum. Its endpoint values are $-1/3-v^2$ and $-2v^2+O(1)$, since the initial endpoint has $t^3-3tv^2=1$. The horizontal integrals therefore vanish. At $\zeta=1+iv$ the exponent is $A_i(-1/3-v^2-2iv^3/3)$. The polynomial and Jacobian give (1).

The following enclosures use only Gaussian moments. Replace the phase by $1-2iAV^3/3$, expand, and take the real expectation. In this polynomial in $A^{-1}$ keep the constant and the negative coefficients evaluated at a lower bound for $A$. Subtract
$$
 \frac{2A^2}{9}\mathbb E[V^6(1+V^2)^{\lceil p/2\rceil}],
 \qquad
 \mathbb E V^{2l}=\frac{(2l)!}{4^l l! A^l}.
$$
This bounds $I_p$ from below by Taylor's inequality. For $p=3,6$ the common upper bound for $|I_p|$ is $\mathbb E(1+V^2)^3$.

For $0<x\le1/4$ take $A_{\min}=2.337^3/(18(1/4)^2)$ and let $U$ be the last upper bound there. Divide the terms $i\ge2$ in (1) by the first term's prefactor, excluding $I_p$. The residual power of $a_i/a$ is $4+3j-3/2\le6$. Also $3b^2/(54(1/4)^2)>13$. After extracting the leading exponential, bound the remaining sum by integration by parts against the eigenvalue count, starting just below $b$. The function $(1+y)y^6e^{-13(y-b)}$ decreases for $y\ge b$ and its negative derivative is at most 13 times itself. With $y=b+t/13$, an upper bound on the total absolute remainder in these units is
$$
 U\,\frac{\exp[-(b^3-2.339^3)/(54(1/4)^2)]}{2.337^6}
 \int_0^\infty (1+y)y^6(1+y^2/3)e^{-t}\,dt < .01 .
$$
The [rational certificate](verify_cubic_tilt.py) integrates the polynomial using factorials. Writing $r=a/(3x)$, (1) gives
$$
 F'(x)>.4 r^6 e^{-ar^2/6}\quad(0<x\le1/4),\qquad F(1/4)>.30.
 \tag{2}
$$
For example, the coefficient of $r^6 e^{-ar^2/6}$ is bounded below using $3c_1/(2\sqrt a)$ times the lower Gaussian bound minus the excited-state error in those units. The right side of the derivative bound decreases in $r$ here, since $ar^2>18$. It exceeds $.105$ over $.145\le x\le.25$, and $.0001$ when $r\le7.001$ and $x\le.25$.

For $r\ge7$ choose $h=r^3$, $x=a/(3r)$. The real transform divided by $\sqrt{\pi/2}\,r c_1e^{-ar^2/2}$ is between $.997$ and $1.003$ by the [real Airy sum bound](return-bounds.md#height-of-a-positively-tilted-meander-density). In $e^{-hx}F'(x)/(hL(h))$ the three exponential factors cancel. Equation (1) leaves $3r^2/\sqrt{2\pi a}$ times the Gaussian factor including its remainder, divided by the real transform ratio. At $A_1\ge2.337\cdot49/2$ the certified bounds are
$$
 \frac{e^{-hx}F'(x)}{h L(h)}>.701r^2,\qquad F_h(x)<2r^2 . \tag{3}
$$
The second bound uses $p=3$ in the same calculation.

## The peak interval

Write $s=m^{3/2}$ and $g=\log F$. The [localized last-return estimates](localized-returns.md) compare the density and the first and centered second differences, in lattice units, with $F,F',F''$ at $z_0=(k+d)/(2N)^{3/2}$, where $2N=m$ or $m+1$ and $d=(m+1+\lceil m/2\rceil)/2$. For $n\ge10^6$ the three errors are below $.0033,.101,6.1$. At $.145s\le k\le.6s$, both parities give $.145\le z_0<.601$ by substitution.

By (2) the unique mode $x_*$ is greater than $.25$. Up to $.25$ the forward difference is positive by (2). From $.25$ to $x_*$, if $g'\ge1$ then $F'\ge F(.25)>.30$. From $x_*$ through $.601$, if $g'\le-1$ then $-F'\ge F\ge1.78e^{-6(.601)^2}>.20$ by Gaussian regression. Wherever $|g'|<1$ one has $F''<-15.5$ by $g''\le-12$ and the peak height bound. Thus the forward differences have strict flank signs and decrease strictly in the intervening interval. They turn at most once. The [all-size rising-side estimate](marked-hits.md) and [lower-half inequality](monotonicity.md#1-lower-half-for-all-sizes) give the rest of the row from $.6s$. [Mode height and curvature](thinning.md#inversion-and-signs-around-the-maximum) · [Gaussian regression](airy-overlap.md#the-decreasing-side-in-corank)

Every global maximum lies in this interval. For $k<.145s$ one has $z_0<.147$. The inequality $F(z_0)\le F(x_*)e^{-6(z_0-x_*)^2}$ loses more than $.10$ in density from the peak since $F(x_*)\ge1.78$. Rounding $x_*$ to the nearest corank site loses less than $.001$, by integrating $100t e^{-.19t^{2/3}}/\pi$ and dividing by $(2N)^{3/2}$. This difference exceeds twice the density error. The [all-size location bound](marked-hits.md#the-maximum-at-finite-size) excludes maximizers at and past $.6s$. The strict flank and second-difference signs now give the assertion about ties.

## Positive-tilt comparison for the intermediate coranks

Take $m\ge M=2\cdot10^{10}$, $s/16<k<\lceil.145s\rceil$, $c_m=(m+\lceil m/2\rceil)/2$, $z=(k+c_m)/s$. Choose $r=a/(3z)$, so $r<16a/3<12.5$ and $z<.146$. In this interval $|z-z_0|\le1/m$ by the parity formulas. If $r<7$, then $a/(3z_0)<7.001$, $z_0<.25$, and (2) beats the $.00002$ fair difference error at $N\ge10^{10}$.

It remains to consider $7\le r\le12.5$. Under the surviving walk law set $X_m=(K_m+c_m)/s$ for random corank $K_m$. With $h=r^3$, $w=h-it$ and $q=|w|$, the following bound holds for $|t|\le500000$:
$$
 \frac{|\mathbb E e^{-wX_m}-\mathbb E e^{-wY}|}{L(h)}
 \le \frac{70(1+r^2)+(30+5r^2+r^3)q+2.7q^2}{m}. \tag{4}
$$
We give the length-dependent checks for the [tilted pair-deletion argument](tilted-thinning.md). Let $p_j$ denote survival probability, $D=p_mL(h)$ and $S_j$ the left-endpoint walk area.

1. Retain $|J-m|\le.00015m$ when deleting flat pairs of a length-$4m+1$ walk. The relevant local $j/m$ differ from one by at most $.000151$, and the real dilations $b'$ by at most $.00016$. To bound the mass at $i=j$ and $i=j-\lfloor m/(2r^2)\rfloor$, put $u=b'h(i/m)^{3/2}$. At either length $i\ge.9m$, $6.6<u^{1/3}$ and $u<1960$. The following real estimate also applies to the fine length $4m+1$ with $u=h$.
2. At height $H=\sqrt i/u^{1/3}>10000$, set $l=\lfloor i/2\rfloor$. The [real transfer energy and amplitude estimates](moderate-saddle.md) give $p=\log\lambda\le-a/H^2+1.5/H^3+65/H^6$, principal amplitude at most $1.05c_1/H$, and relative remainder at most $1270\exp[-1.48(l/H^2-2.01)]<.001$. Here $l/H^2\ge.499(6.6)^2$. This is the two-boundary-vector estimate after $\lceil H^2\rceil$ pairs at either end. By Wallis and the real Airy estimate, $p_iL(u)\ge .997c_1e^{-ai/(2H^2)}/(H\sqrt{1+2/i})$. Changing from $K_i$ to $S_i/2$ costs at most $e^{u/(2\sqrt i)}$. Thus the unconditioned surviving real mass weighted by $e^{-u S_i/(2i^{3/2})}$ divided by $p_i L(u)$ is below
$$
 \frac{1.05\cdot1.001}{.997}\sqrt{1+2/i}
   \exp\left(1.25u/\sqrt i+2.339/(2H^2)+33u^2/i^2\right)<1.11.
$$
   This also bounds the uncentered corank mass by the same upper estimate. The [Laplace ratio estimate](tilted-thinning.md#real-weights-and-the-absorbing-boundary) now gives the local and shorter mass bounds $1.5D,3.8D$. The real ratio cost in its exponent is $1.17r^2(.00016+1.5\cdot .000151)$, with an additional $1.17\cdot.75$ at the shorter length.
3. The edge and dilation estimates (2)–(6) of that proof apply. In particular $q/(2s)<10^{-10}$. The omitted binomial probability is at most $2e^{-m(.00015)^2}\le D/m^2$. Use the same height cap $2\sqrt{m\log m}$, and $X=1.17r^2+4\log m+30$ for the exceptional placements of flat pairs. The retained conditional mean costs $h|V_0-V_1|<.02$ and the fluctuation costs $h|V-V_0|\le1.17h\sqrt{X\log m/m}<1.44$, using $23<\log M<24$. The logarithmic factors times the negative powers of $m$ decrease thereafter. The coefficient of $q^2D/m$ in the conditional variance cost is at most $(33\cdot3.5+1.01\cdot1.5/m)e^{1.46}/512<1$. The cap, conditional-geometric and binomial-tail inequalities for this window are checked in the reused length and exception functions. Summing over $m,4m+1,\ldots$ gives coefficient at most $(4/3)(.51\cdot4/8+1.4/2+1)<2.7$ for $q^2$. The other coefficients in (4) follow as in the [comparison at the earlier threshold](return-bounds.md#growth-from-the-small-corank-interval-to-the-peak). At $t=0$ the right side of (4) is below $.001$.

## Inversion of the adjacent difference

Set $C=s(1-e^{-h/s})/h$ and $G_k=e^{-hz}\Pr(K_m=k)/L(h)$. Then $CsG_k+(s^2/h)(G_{k+1}-G_k)$ has the sign of $b_{k+1}-b_k$. At the same site $z$, its continuum counterpart is
$$
 CF_h(z)+F_h'(z)/h
 =e^{-hz}F'(z)/(hL(h))-(1-C)F_h(z)>.70r^2
$$
by (3) and $0\le1-C<h/s<.0001$. The lattice Fourier multiplier has modulus at most $1+|t|/h$ after removing its common translation. Through a bandwidth $T$, the cost of replacing its difference part by the derivative is at most $T^3/(6\pi h s)$. For the central transform error use (4), with $q\le h+|t|$ in the linear term and $q^2=h^2+t^2$ in the quadratic.

For the tail set $H=\sqrt m/r$, $N_b=n/H^2\ge.4999r^2$, $y=|t|/h$. At each left endpoint $y_0$ of the frequency table in the verifier, use blocks of $\lfloor vH^2\rfloor$ pairs and Hölder exponent $p$ as specified there. For $y_0\le y\le150$ the norm relative to the ground transfer power is bounded by $e^{-vB}$ for the tabulated rate $B$. Indeed the binomial moment before taking its $p$th root is at most
$$
 2^{-4p}\sum_{j=-2p}^{2p}\binom{4p}{2p+j}
 \exp[-j^2(.999v)^3y_0^2/16].
$$
Multiply the root by $\exp[v(a(1-(p/(p-1))^{-1/3})+.00001)]$. The [block moment and spacing conditions](power-overlap.md#tilted-fourier-blocks-at-intermediate-frequencies) hold since $H>11000$, $2pv\cdot150/H<\pi$, $vH^2>10000$ and the scaled real energy error is below $2000(1+p/(p-1))/H^4<.00001$. The table tests the resulting bound by rational upper and lower enclosures.

The initial and terminal real norm ratios after $\lceil H^2\rceil$ pairs are bounded by 8 and 158 respectively. With $d\ge1.25$, take $\lceil dH^2\rceil$ pairs instead. The squared norm is the ground component squared plus its orthogonal remainder, which decays with the real spectral gap. For either initial ratio bound $b$ use
$$
 A_b(B)=\min_{d=1.25,1.5,\ldots,7}
       e^{Bd}\sqrt{1+(b^2-1)e^{-2(1.48)(d-1.0001)}}.
$$
Complex end vectors are dominated entrywise by the real ones. The two end lengths can be selected separately. Since $N_b>24$ even at $r=7$, both fit, with room for interior blocks. Discard at most one interior block and account for both ceilings by $2/H^2<.001$. In ground units the envelope is
$$
 A_8(B) A_{158}(B)e^{-B(N_b-v-.001)} .
$$
For the centered lattice transform in units $L(h)$ the extra mass ratio is below $1.003$, by (4) at zero and the real remainder in step 2. The continuum bound follows by sending the walk length to infinity at fixed $h,t$. Integrating over both laws and both frequency signs thus costs less than $.65h$ times the integral of $(1+1.001y)$ times this envelope, since $2.01/\pi<.65$. From $y=150$ use the [two outer Fourier estimates](variation-overlap.md#bandwidth-and-error-bounds-outside-the-central-interval). Each costs less than $.001$ in units $.21r^2$. Their conditions use $N_b\ge.49r^2$, real normalization in $(.7,1.4)$, and $H^3/64>10^4$. The uncentered real mass correction is at most $\exp(hc_m/s)<1.02$.

For each closed $r$-interval of width $.01$ in $[7,12.5]$ the verifier tries $T=y_0h$ at all tabulated endpoints. For each choice it integrates the polynomial from (4) up to $T$, bounds the multiplier error, sums the tail envelope by frequency bands through 150, and adds $.003$ in relative units for the outer frequencies. All integrands are bounded using the least denominators and greatest numerators on the whole $r$-interval. Taking the smallest valid error bound on each interval and the greatest over the intervals costs less than $.80$ of the lower bound $.70r^2$. This proves strict increase at every remaining intermediate corank. The [all-size small-corank result](moderate-saddle.md) supplies $0\le k\le s/16$. Together with the peak interval, this proves the theorem for both word lengths.

## Reproduction

~~~sh
python3 -B verify_cubic_tilt.py
python3 -B verify_local_returns.py
python3 -B verify_tilted_thinning.py
python3 -B verify_moderate_saddle.py
python3 -B verify_variation.py
python3 -B verify.py --max-n 96 --direct-n 12 --upper-curvature
~~~

The first two commands check numerical inequalities in proofs uniform in the row count. The last compares actual integer coefficient lists with independent enumeration of distinct parts for both families through twelve rows.
