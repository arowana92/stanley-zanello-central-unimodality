# Marked returns and strict growth in corank

For the odd-part and even-part central staircases put $m=2n+\delta$, with $\delta=0,1$ respectively, $s=m^{3/2}$, and $\ell=n+\delta$. Let $b_k$ count shifted subdiagrams missing $k$ cells. For **both families and every $n\ge2$**,
$$ b_{k+1}>b_k\qquad (0\le k\le s/35). \tag{1} $$
There is also an integer bound which can be stronger at moderate sizes. Let $L(\ell)$ be the sum of the $\ell$ cheapest entries in the multiset
$$ \{4h+a+b:\ h,a,b\in\mathbb Z_{\ge0}\}. $$
Then
$$ b_i<b_j\qquad (0\le i<j,\quad i+j\le L(\ell),\quad n\ge2). \tag{2} $$
For example, (2) gives strict growth through coranks 25,143 and 25,160 at $n=2049$ for the odd- and even-part shapes. The earlier [unmatched-step comparison](excursion-centers.md) gives 20,284 and 20,290. The proof of (1) uses (2) at small corank and a Fourier estimate for the [ballot transfer](effective-small-area.md#real-transfer-operator) at larger corank. The [verifier](verify_folded_saddle.py) checks the overlaps and numerical inequalities using rational bounds.

## Folding unmatched steps into returns

For an ordinary Dyck path $P$ of semilength $\ell$, write $R(P)$ for the set of its positive return times in single-step units, including the terminal return. Write $A(P)=\sum_t\lfloor H_t/2\rfloor$ for its area. For the corank polynomials one has
$$
 \begin{aligned}
 B_n(q)&=\sum_{P:\ell=n} q^{A(P)}
       \prod_{r\in R(P)}(1+q^{2\ell-r+1}),\\
 O_n(q)&=\sum_{P:\ell=n+1}q^{A(P)}
       \prod_{r\in R(P),\,r<2\ell}(1+q^{2\ell-r}).
 \end{aligned} \tag{3}
$$
Indeed, in an even-length meander match each down-step to the last available up-step. An even number of unmatched up-steps remain. Change the second, fourth, and subsequent even-indexed ones into down-steps. The intervening matched subwords are excursions. The resulting word is Dyck, and the changed steps mark returns to zero. Conversely, flipping the down-step at every marked return to an up-step recovers the meander. After flipping at time $r$, the height at each time from $r$ to the end increases by two. This gives the first weight in (3). For odd length, append an up-step before folding. The terminal return is now always marked. With $u$ other marks the appended step contributes $u+1$ to corank. Subtracting this from the even-length formula cancels the terminal mark and subtracts one from each other mark. This gives the second weight. The rank-to-walk area identification is the [ballot bijection](README.md#exact-coefficient-checks).

For $B_n$, splitting at the first proper mark in (3) recovers Stump's type $B$ area recurrence. If that mark leaves $h$ semilength units, the contribution is $q^{2h+1}C_{n-h}B_h$. With no proper mark it is $(1+q)C_n$. [Stump, Theorem 3.1](https://arxiv.org/abs/0808.2822)

Fix a subset of proper marked times $2t_1<\cdots<2t_u$. The successive gaps in semilength, including both ends, are positive integers $l_0,\ldots,l_u$ summing to $\ell$. Unmarked returns are allowed anywhere within a gap. Summing over paths with these marks gives
$$ q^J\prod_{h=0}^u C_{l_h}(q),\qquad
 J=2\sum_{h=0}^u h l_h+(1-\delta)u+\varepsilon . $$
Here $C_l$ is the ordinary Dyck area polynomial and $\varepsilon=0$ except for the optional final mark in $B_n$, which contributes one. Let $E(l)$ be the sum of the $l$ cheapest $a+b$ for nonnegative lattice pairs. The type-A diagonal coinvariant theorem gives an interval decomposition of $C_l$ with sums of interval endpoints at least $E(l)$. Products of intervals split into intervals with additive centers. Thus all intervals in the marked summand have endpoint sum at least $\sum_h(4hl_h+E(l_h))\ge L(\ell)$. The last comparison selects $l_h$ distinct pairs in each layer $h$. This proves the weak inequality in (2), separately on each summand. [Interval argument and attribution to Haiman and Garsia–Haiman](excursion-centers.md#ordinary-excursions-and-two-variable-characters)

For strictness it suffices to exhibit one summand that gains between $i$ and $j$. In $B_n$ the possible initial exponents $J$ are the subset sums of $1,3,\ldots,2n-1$. For $n\ge4$ these cover $[0,n^2]$ except $2,n^2-2$. This follows by checking $n=4$ and taking the union of the previous set with its translate by $2n+1$. The old gap $n^2-2$ is filled by adding $2n+1$ to $(n-3)(n+1)$, and the translated gap $2n+3$ belongs to the old set. Since $L(\ell)\le\binom{\ell}{2}$ by choosing $(0,a,0)$, the upper gap is irrelevant. At $j=2$ the unmarked $C_n$ alone is strict for $n\ge5$. Its coefficients at $0,1,2$ are $1,n-1,\binom{n-1}{2}$ by the Dyck area vector. In $O_n$, disallow proper marks at times 2 and 4. The remaining even mark weights realize every even $J$ from zero to $(n-2)(n-1)$, which exceeds or equals $\binom{n+1}{2}$ at $n\ge7$. For odd $j$, choose $J=j-1$. The first gap has length at least three and its Dyck polynomial has coefficient at one at least two. This summand therefore gains even when $i=j-1$. For both families $2\le n<7$ the verifier tests (2) directly.

The number of entries of cost at most $t$ is $\sum_{h=0}^{\lfloor t/4\rfloor}\binom{t-4h+2}{2}\le (t+6)^3/24$. Bound each term by $(t-4h+2)^2/2$ and then by the average of $x^2/2$ on the next interval of width four starting at $t-4h+2$. The leading asymptotic count is $t^3/24+O(t^2)$. Summing the lower bounds $(24j)^{1/3}-6$ on the $j$th cost gives
$$ L(\ell)/2\ge \tfrac38 24^{1/3}\ell^{4/3}-3\ell>1.081\ell^{4/3}-3\ell. \tag{4} $$

## Which endpoints can contribute a decrease

Let $b_k^{(u)}$ count only the walks ending at height $2u+\delta$. A strict decrease $b_{k+1}^{(u)}<b_k^{(u)}$ requires **both**
$$
 (u+1)(2k+1+3\ell/2)^2>8\ell^3/9,\qquad
 (2n+\delta+1)u+(\delta-1)n<2k+1. \tag{3a}
$$
The first bound uses the marked-return comparison before minimizing over endpoints. There are $u$ marks in (3) at this endpoint, so at most $u+1$ gaps. The number of planar lattice pairs of degree at most $t$ is $\binom{t+2}{2}\le(t+3/2)^2/2$. Summation gives $E(l)\ge(2\sqrt2/3)l^{3/2}-3l/2$. Convexity applied to the gap lengths bounds the endpoint sum of each interval below by $(2\sqrt2/3)\ell^{3/2}/\sqrt{u+1}-3\ell/2$. If this reaches $2k+1$, the contribution from each interval increases weakly.

For the second bound use $d=n-u$ down-steps and drop the ballot constraint temporarily. The $d$ down positions index the standard basis of $\bigwedge^d\operatorname{Sym}^{m-1}(\mathbb C^2)$. The raising operator in $\mathfrak{sl}_2$ acts by moving one position one place later, with zero for a repeated position. Each move increases the corank by one and preserves every ballot prefix inequality. The span of the ballot subsets is therefore stable under raising. The middle corank of the full exterior power is $c=D-d(m+1)/2$, where $D=n(n+\delta)$, since the sum of the $d$ down labels has middle value $d(m+1)/2$. In each irreducible $\mathfrak{sl}_2$ string the weights in corank units are an interval centered at $c$, with raising nonzero between successive weights. Thus the $(j-i)$th power of raising is injective from corank $i$ to $j$ whenever $i<j$ and $i+j\le 2c$. It is still injective on the ballot subspace. Substituting $i=k,j=k+1$ gives the second restriction in (3a). This locates the endpoint classes that could contribute a negative adjacent difference, while the sign of their sum remains to be controlled inside the gap.

## A second-moment test at the saddle

Let $\lambda=e^{p(\beta)}$ be the leading eigenvalue of the two-step transfer at real tilt $\beta>0$, $H=\beta^{-1/3}$, $N=n/H^2$. We prove strict growth at the integer saddle $k=-np'(\beta)$ for **$H\ge114$, $N\ge360$**. Under the probability proportional to $b_j e^{-\beta j}$, with random corank $K$, put $Z=\beta(K-k)$ and $J(y)=\mathbb E e^{-iyZ}$. These definitions of $J$ and $Z$ apply in the Fourier argument below.

The full tilted walk satisfies $\mathbb E Z^2<.714N$. To see this write $F_n(\beta)=2^{-m}\sum b_j e^{-\beta j}$ and $c(\beta)$ for its principal amplitude. The [real boundary estimate](excursion-centers.md#the-lattice-saddle-at-height-220) gives $.99 I/H<c(\beta)<1.01 I/H$ down to $H=110$. In that argument the squared sample norm has error $7d^2$, where $d=1/H$. Relative to the continuum terminal sum the error bound is
$$
 [2d^2(26/2+(21+106d)/4+12+70d)+7d^2]/(1-7d^2)+3200d^3 .
$$
At $d=1/110$ this is below $.00814$. The boundary and parity factors still give the displayed amplitude interval. The real projection remainder gives $F_n/(c\lambda^n)\in(.999,1.001)$ at $N>330$, using $20000e^{-1.48(N-2\lceil H^2\rceil/H^2)}$.

Put $w=1/\sqrt N$. These estimates apply at both tilts $\beta(1\pm w)$ since their height is above 110 and their number of height-scale blocks is above 330. On the real segment between them $p''\le .565H^4$. Indeed the [complex grid expansion](airy-grid.md) at each intermediate height $H'$ gives $p''/(H')^4\le2a/9+4000/(.12^2(H')^4)$, with $2.337<a<2.339$ the first Airy energy. Apply Taylor's formula to $e^{\pm wZ}$ after subtracting the saddle's linear term. The average of the two amplitude scaling factors $(1\pm w)^{1/3}$ is at most one. Hence
$$
 1+\frac{\mathbb E Z^2}{2N}\le \mathbb E\cosh(wZ)
 \le\frac{1.001}{.999}\frac{1.01}{.99}\,e^{.565/2}.
$$

Set $z=\sqrt N\, y$, $a_0=2.1$. Inversion gives strict growth if the integral of $\Re J$ exceeds that of $1.001|yJ|$ on the fundamental period, with both integrated in $z$. Indeed the multiplier of a tilted adjacent difference has modulus at most $\beta |y|$, and $\beta/(1-e^{-\beta})<1.001$. On $|z|\le a_0$ use $\cos v\ge1-v^2/2$ and $|J|\le1$. The net lower bound there is
$$ 2a_0-.714 a_0^3/3-1.001a_0^2/\sqrt N. \tag{5} $$
This test uses the second moment about the integer saddle, including any displacement of the tilted mean.

## Fourier bounds outside the center

Peel $\lceil12H^2\rceil$ pairs at each boundary. Dividing by the full real mass, their norm product costs at most $1.003$ after the corresponding eigenvalue powers are removed. Indeed after $\lceil H^2\rceil$ pairs the product of the two ratios to the respective ground components is below 20000. Both ratios are at least one. Over at least $10H^2$ further pairs their perpendicular parts contract relative to their ground components by $e^{-1.48\cdot10}$. Pythagoras gives product at most $1+(20000e^{-14.8})^2$. Entrywise domination gives the same norm bound for the two complex ends. [Boundary block proof](airy-grid.md#boundary-factors-in-fourier-inversion)

For $|y|\le .08$ the spectral projection has norm at most $(1-5.52\cdot.08)^{-1}$. In the grid expansion, the real quadratic loss of the principal logarithm in units $H^{-2}$ is at least $.25 y^2$. Use $a\cdot.109 y^2$ for the leading power, subtract $(2/9)(.264) d^2 y^2$ for the fourth-order correction, and subtract $2000d^4y^2/(.12^2-.08^2)$ for the analytic remainder. The [complementary mass](two-harmonics.md#analytic-control-on-a-wider-disk) costs at most $e^{20-.16N}/.999$ at each frequency. Consequently the principal part of $|J|$ is at most $1.81e^{-.25(N-25)y^2}$.

For $.08\le |y|\le1.4$ we use the [power estimate from an approximate Airy eigenvector](airy-powers.md#a-power-bound-outside-the-perturbation-disk). The successive triples in the following table are the norm factor, rate in $y^2$, and frequency band for the middle transfer raised to $j$ pairs. Its norm divided by $\lambda^j$ is at most $B e^{-\gamma j d^2 y^2}$.

| $\lvert y\rvert$ | $B$ | $\gamma$ |
| --- | ---: | ---: |
| $.08$ to $.5$ | $1.63$ | $.23$ |
| $.5$ to $1$ | $4$ | $.14$ |
| $1$ to $1.4$ | $20$ | $.047$ |

Here are the modified bounds for that argument. With $t=1+iy$, the corrected Airy sample has approximate adjoint eigenvalue $\bar\nu$, where $\nu=\exp(3td^3/2-at^{2/3}d^2-a^2t^{4/3}d^4/30)/\lambda$. Its residual is at most $\Delta d^2$ for $\Delta=2100d^4$. In the [grid residual calculation](airy-grid.md#sampling-the-half-line-eigenfunction) take $|t|\le1.74$, $|at^{2/3}|\le3.4$, $\Re t=1$ in all moment recursions. Use $|t|/4$ for the antisymmetric first derivative of the correction and $|t|^2 e^{|t|d^3/4}/32$ for the hyperbolic remainders. The verifier evaluates all derivative norms, the scalar remainders and the normalization before squaring the transfer. Also $L=-d^{-2}\log|\nu|$ differs from $a(\Re t^{2/3}-1)$ by at most $.80d^2$, by the real grid estimate. The singular ground directions differ by at most $2.4d$ since $|y|\le1.4$ and $-p'(\beta)<1.8H$.

In the norm $\max(\|v\|,B|\langle v_*,v\rangle|)$ of the power argument, with $v_*$ the approximate left eigenvector, it suffices that
$$
 .74\left[1-\left(\sqrt{2(L+\Delta)/1.48}+2.4d+1/B\right)^2\right]\ge\gamma y^2,\qquad
 L(1-Ld^2/2)-B\Delta\ge\gamma y^2.
$$
Use $L\le2.339 y^2/9+.80d^2$. For the lower bound on $\Re t^{2/3}-1$ use $y^2/9-56y^4/(81\cdot24)$ through $.5$. In the other two rows integrate $(2/3)(1+y^2)^{-1/6}\sin(\arctan(y)/3)$, bounding $\arctan(y)/y$ below by its value at the right endpoint. This gives both inequalities with the indicated constants.

For $1.4\le |y|\le45$, use blocks of $l=\lfloor vH^2\rfloor$ pairs. For the absolute endpoint transform $\rho_j$ of an unrestricted fair block at the $j$th harmonic, pair the first and last step, the second and penultimate step, and so on. In a pair at separation $h$ the average modulus after fixing its sum is $(1+|\cos(jh\beta y/2)|)/2$. For $jv|y|/H\le\pi/2$ it is at most $e^{-j^2h^2\beta^2 y^2/16}$ since $\cos^2 x\le e^{-x^2}$ on this arc. Multiplying over odd separations gives
$$ \rho_j\le\exp[-j^2\beta^2y^2(4l^3-l)/48]. $$
The bound $\rho_j\le1$ suffices for other harmonics. The row-sum estimate also bounds the norm by symmetry. Apply the [Hölder block proof](holder-blocks.md#a-block-inequality) with integer $p$ and conjugate power $b=p/(p-1)$. The majorant for $(\cos x)_+^p$ is $\cos^{4p}(x/2)$. Thus a block has norm relative to $\lambda^l$ at most
$$
 e^{l(p(b\beta)/b-p(\beta))}
 \left(2^{-4p}\sum_{j=-2p}^{2p}\binom{4p}{2p+j}\rho_{|j|}\right)^{1/p},
$$
where $p(\cdot)$ in the exponent denotes the log eigenvalue. The scaled real energy difference is at most $2.339(1-b^{-1/3})+2000(1+b)/H^4$. The linear term cancels, the next correction is nonpositive, and $H/b^{1/3}\ge100$ in all the chosen blocks. The verifier gives $1.003 e^{-\gamma(N-26)}$ for the full $|J|$ on ten successive bands, starting with $\gamma=.013$ on $[1.4,1.5]$ and reaching $.24$ on $[12,45]$. The floor and both boundary blocks together discard fewer than $26H^2$ pairs.

Beyond 45 use the [full-period estimate](airy-grid.md#boundary-factors-in-fourier-inversion) on at least $1.85n$ remaining single steps. After restoring the real energy at cost $\exp(2.61N)$ and the boundary factor, this is at most $3e^{-N |y|^{2/3}/80}$. Indeed the rate per step before restoring the energy is $.124|\theta|^{2/3}$ through $|\theta|=1/64$, and $|\theta|^{2/3}/75$ thereafter with $|y|\ge H^3/64$.

To integrate, through $|y|=.5$ the principal absolute envelope is bounded by $B'e^{-c z^2}$ with $c=.23(1-25/N)$. Take $B'=1.64$ for $360\le N\le600$, since $2.1/\sqrt N>.08$ there, and $B'=1.81$ thereafter. The verifier integrates $(1+1.001|z|/\sqrt N)$ times this bound from $2.1$ on each side, using width $.01$ through 10 and the tangent bound for the exponential in the remaining Gaussian tail. It integrates the constant envelopes over their separate bands beyond $.5$. The complementary mass through $.08$ and the stretched exponential beyond 45 cost less than $.001$ each. In the latter integral extract $e^{-N45^{2/3}/160}$ and substitute $t=|y|^{2/3}$. Every bound improves with $N$ in its range, since $\sqrt N e^{-\gamma N}$ decreases for $2\gamma N>1$. Subtracting all outer costs from (5) leaves more than $.248$ at $N=360$ and $.550$ at $N=600$. This proves the saddle sign for both terminal parities.

## Strict log-concavity on a small-corank interval

For both families the same Fourier bounds give
$$
 b_k^2-b_{k-1}b_{k+1}>\frac{n^3}{2k^4}\, b_k^2
 \qquad (178n\le k\le s/85). \tag{6}
$$
The interval first becomes nonempty at row counts of order $10^7$. The proof uses a second-difference multiplier and controls its sign throughout a range of sizes and coranks.

First assume $H\ge114$ and $N\ge2100$ at the integer saddle. Put $b=\lceil200H^2\rceil$ and $v^2=\beta^2(n-b)p''(\beta)$. The grid expansion gives $.515(N-201)<v^2<.523N$, and $|p'''(t\beta)|<2.1H^7$ on $|t-1|\le.08$. For the last inequality the analytic remainder contributes at most $6\cdot2000H^{-4}/.04^3$ in the scaled units. In this argument normalize the centered transform by $c(\beta)\lambda^n$ and write it as $J_n$. Every outer Fourier envelope above still holds with this normalization, since the peeling argument costs at most $1.001$.

Use the [shorter-walk identity](airy-powers.md#inverting-at-the-integer-saddle) with $x=vy$. On $|y|\le.08$ its principal term equals
$$
 (S(iy)-R_b)e^{(n-b)P(iy)},\qquad
 P(w)=p((1+w)\beta)-p(\beta)-w\beta p'(\beta).
$$
Here $S$ is the transform of the shorter walk centered at $-bp'(\beta)$ and normalized by its principal real mass. The complementary terms satisfy $|R_j|\le e^{20-.16j/H^2}$ at $j=b,n$. Under the normalized shorter law let $Z_b=\beta(K+bp'(\beta))$. Then $.999<S(0)<1.001$ and $\mathbb E Z_b^2<205$. For the latter, apply the same two-real-tilt calculation as above at $\pm.08$. The shifted heights exceed 110, $p''\le.68H^4$ between them, and both shorter transforms are below $1.001\cdot1.06\exp(.34\cdot201\cdot.08^2)<1.65$. Use $\cosh u\ge 1+u^2/2$.

The complete Gaussian integral with weight $x^2$ has the lower bound
$$
 \int_{\mathbb R} x^2 e^{-x^2/2} S(ix/v)\,dx
 \ \ge\ \sqrt{2\pi}\,.999\left(1-\frac{3\cdot205}{2v^2}\right).
$$
Indeed the Fourier integral at a given $Z_b$ contributes $\sqrt{2\pi}(1-w)e^{-w/2}$ with $w=Z_b^2/v^2$. For all $w\ge0$, $(1-w)e^{-w/2}\ge1-3w/2$ by $e^{-w/2}\ge1-w/2$ and $-w e^{-w/2}\ge-w$. Removing $|x|>u=.08v$ costs at most $2.002(u+1/u)e^{-u^2/2}$. On the retained interval $\Re((n-b)P(iy))\le-.47x^2$, by the $.25$ energy loss. The cubic remainder in replacing the exponential by the Gaussian costs at most
$$ \frac{2.1\cdot 1.001}{6\cdot.515\,v}\int_{\mathbb R}|x|^5e^{-.47x^2}dx
 =\frac{2.1\cdot2.002}{6\cdot.515\,v\cdot.47^3}. $$
The two complementary terms cost below $.001$ for either the mass or the $x^2$ integral, by integrating the Gaussian bound on the shorter term. For the actual nonnegative multiplier $G=4(v/\beta)^2\sin^2(\beta x/(2v))$, replacing $x^2$ on the retained interval costs below $.0003$ since $|G-x^2|\le .0001 x^2$ there.

Outside the retained interval $G\le x^2$. In units $dx$ the cost through $|y|=.5$ is at most
$$
 2\cdot1.64\,v^3 e^{-c a_1^2}
 \left(\frac{a_1}{2c}+\frac1{4c^2a_1}\right),
 \quad c=.23(N-25),\quad a_1=.08 .
$$
This follows by integrating the Gaussian tail by parts. In each subsequent band $[l,r]$ use its constant envelope times $2v^3(r^3-l^3)/3$. Beyond 45 substitution of $t=|y|^{2/3}$ gives an outer cost below $.001$. These bounds decrease with $N$ after substituting $v\le\sqrt{.523N}$ in the costs. For the displayed Gaussian tail this follows from the decrease of $N^{3/2}e^{-c a_1^2}$ already at $N=2100$. The verifier gives $\int G\Re J_n\,dx>.491$ and $\int |J_n|\,dx<3$. The last estimate uses the Gaussian modulus on the core and the weighted outer cost divided by $u^2$.

Let $g_k$ be the tilted mass at $k$. Inversion gives $-(g_{k-1}+g_{k+1}-2g_k)/g_k>.40\beta^2/(3v^2)$. If $r=(g_{k-1}+g_{k+1})/(2g_k)$, then $0\le r<1$ and the relative log-concavity determinant is at least $1-r^2\ge1-r$. Removing the exponential tilt preserves that relative determinant. Since $v^2/\beta^2<.523nH^4$ and $k/n>(2a/3-.016)H$, the result exceeds $n^3/(2k^4)$. Finally $k\ge178n$ puts $H>114$ by the slope bound below. If the interval in (6) is nonempty then $n>1000$ (use $m\le3n$), so $m/n\le2.001$ and $N>85^2(2\cdot2.337/3-.016)^2/(2.001)^3>2100$. This proves (6).

## Overlap for all sizes

At $2\le n<64$, (2) covers all $k\le s/35$, checked with exact integer costs. For $64\le n\le4{,}750{,}000$, (4) gives $L(\ell)/2>s/35+1$. Divide by $n$ and use $m/n\le2.016$. The lower bound $1.081 n^{1/3}-3-2.016^{3/2}\sqrt n/35$ is concave as a function of $n^{1/3}$, and exceeds $1/64$ at both endpoints.

At larger $n$ use (2) until $2k+1>L(\ell)$. Then $k\ge L(\ell)/2$ and $k/n>1.081\cdot168-3$. At $H=114$ the slope $-p'(\beta)$ is at most $H(2a/3+4a^2/(90H^2)+2000/(.12H^4))$, which is smaller. The [existence and monotonicity of the saddle](effective-small-area.md#real-transfer-operator) and the real grid bound therefore give $H>114$ at the selected integer. There $k/n>(2a/3-.016)H$. For $k\le s/35$ it follows that
$$ N>35^2(2\cdot 2.337/3-.016)^2/(2.001)^3>360. $$
The second-moment saddle test now gives (1).

The checks below compare the marked-path formula with direct strict-partition enumeration through $n=9$, verify 1,207,539 pairwise comparisons from (2) through $n=64$, and independently compare every rank coefficient with direct enumeration through $n=12$. The all-size statements use the inequalities above. Conjecture 3.4 still requires control of intermediate coranks in both staircases.

~~~sh
python3 -B verify_folded_saddle.py
python3 -B verify_excursion_centers.py
python3 -B verify_airy_grid.py
python3 -B verify.py --max-n 64 --direct-n 12 --upper-curvature
~~~
