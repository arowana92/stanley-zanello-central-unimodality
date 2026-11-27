# The phase of the leading ballot-transfer eigenvalue

Let $m=2n$ for $(2n-1,2n-3,\ldots,1)$ and $m=2n+1$ for $(2n,2n-2,\ldots,2)$. Write $s=m^{3/2}$ and let $b_k$ be the number of strict subpartitions missing $k$ cells. The following statements hold for both families.

1. For **every $n\ge2$**, $b_{k+1}>b_k$ at each integer $0\le k\le s/34$.
2. For **$2\le n\le80000$ and $n\ge4500000$**, the strict growth extends through $k\le s/18$. At any size it also holds for $177n\le k\le s/18$.
3. For **every $n$** and every integer $177n\le k\le s/26$,
   $$ b_k^2-b_{k-1}b_{k+1}>\frac{n^3}{2k^4}\,b_k^2. $$

The [previous saddle proof](folded-saddle.md) gave growth through $s/35$ and the quantitative curvature bound for $178n\le k\le s/85$. The new estimates retain the complex phase of the principal power through scaled frequency $.4$, and use the contraction of *both* successive half-steps to bound the remaining powers out to frequency 3.

## A wider interval for the phase

Use the symmetric two-step ballot transfer $K_z$, its leading real eigenvalue $\lambda=\exp p(\beta)$, the height scale $H=\beta^{-1/3}$ and $N=n/H^2$. The different staircase parities change only the terminal vector. We prove strict growth at the integer saddle $k=-np'(\beta)$ whenever $H\ge114$, $N\ge96$, and a quantitative curvature estimate there when $N\ge190$. The earlier proof handles growth at $N\ge360$ and curvature at $N\ge2100$. We use the [real spectral gap and grid energy estimate](airy-grid.md) and the [Airy sample and boundary estimates](folded-saddle.md#fourier-bounds-outside-the-center). All finite constant bounds below are reproduced by the [rational verifier](verify_saddle_phase.py).

Put $d=1/H$, $t=1+iy$, $\theta=\beta y$, and $A=K_{t\beta}/\lambda$. Then $A$ is a complex symmetric contraction. Let $a\in(2.337,2.339)$ be the first Airy energy and put
$$
 \nu=\lambda^{-1}\exp\{3td^3/2-a t^{2/3}d^2-a^2t^{4/3}d^4/30\},
 \qquad L=-d^{-2}\log|\nu|.
$$
For $|y|\le.4$ there is a unit vector $v$ with $\|(A-\nu)v\|\le\Delta d^2$, $\Delta=2100d^4$, by the earlier corrected-sample bound. The adjoint has the conjugate bound for $u=\bar v$. With $g$ the phase-shifted even-height real ground vector, the [single half-step inequality](airy-powers.md#a-power-bound-outside-the-perturbation-disk) is
$$ \|Az\|^2\le\|z\|^2-1.48d^2(\|z\|^2-|\langle g,z\rangle|^2). \tag{1} $$
The adjoint has direction $\bar g$ and $\|g-\bar g\|\le2.4d$ here. Use $L\le a y^2/9+.8d^2$. The sine of the angle of $v$ with $g$, or of $u$ with $\bar g$, is at most $\sigma=\sqrt{2(L_{\rm up}+\Delta)/1.48}$, using $L_{\rm up}=2.339(.4)^2/9+.8d^2$ in (1). The sine between $u,v$ is at most $2\sigma+2.4d$ by the triangle inequality for orthogonal line projections (for unit vectors their projection distance is the sine). In particular $|\langle u,v\rangle|>.81$. On $u^\perp$ the overlap with $g$ is at most $q_0=\sigma+2.4d$.

**Eigenvalue and complement.** There is a simple eigenvalue $\eta$ of $A$ with $|\eta-\nu|\le1.3\Delta d^2$. Its projection $\Pi$ satisfies
$$ \|A^j-\eta^j\Pi\|\le1.25e^{-.67jd^2}\qquad(j\ge0). \tag{2} $$

To prove this, project onto $v$ along $u^\perp$ by $Pz=v\langle u,z\rangle/\langle u,v\rangle$ (inner product linear in its second entry), and put $Q=I-P$. Both projectors have norm at most $1/.8$, by the formula for oblique projection onto a line. In the coordinates $\mathbb C v\oplus u^\perp$, write the four blocks of $A$ as $\alpha,\ell,b,D_0$. The two residuals give $|\alpha-\nu|,\|\ell\|,\|b\|\le\Delta d^2/.8$. For $z\perp u$, (1) and $\|PAz\|\le\Delta d^2\|z\|/.8$ give $\|D_0\|\le1-.67d^2$. On the closed disk $|\zeta-\nu|\le1.3\Delta d^2$ we have $|\zeta|-\|D_0\|>.60d^2$. Hence $\|(\zeta-D_0)^{-1}\|\le1/(.60d^2)$. On the circle the difference between $\zeta-\nu$ and $\zeta-\alpha-\ell(\zeta-D_0)^{-1}b$ has magnitude strictly below $1.3\Delta d^2$. Rouché's theorem gives a single simple root. The block equations give its right eigenvector $v+(\eta-D_0)^{-1}b$. Its normalization differs from $v$ by at most $4.3\Delta$. By transpose symmetry the conjugate normalized vector is an adjoint eigenvector within $4.3\Delta$ of $u$. Their inner product still exceeds $.8$ in modulus. The new oblique complement is invariant and by (1) its contraction is at most $1-.67d^2$, since its overlap with $g$ is at most $q_0+8.6\Delta$. This proves (2).

Choose the logarithm of $\eta$ close to the displayed logarithm of $\nu$. Set
$$
 \phi(y)=-a(t^{2/3}-1)+(3d/2)iy-(a^2d^2/30)(t^{4/3}-1).
$$
By (2) and the real grid estimate at $t=1$,
$$ |d^{-2}\log\eta-\phi(y)|\le4800d^4. \tag{3} $$
Indeed changing $\nu$ to $\eta$ costs at most $1.3\Delta/[1-(L_{\rm up}+1.3\Delta)d^2]$ in scaled log units. The remaining real normalization error is at most $2000d^4$. The analytic grid estimate on $|t-1|\le.12$ and Cauchy's inequality bound the difference between $\phi'(0)$ and $i\beta p'(\beta)/d^2$ by $17000d^4$. Define
$$ V=2a/9-(4/9)(a^2/30)d^2,\qquad .518<V<.520 . $$
This is $-\phi''(0)$. On the imaginary-frequency segment $|\phi'''(y)|\le(8/27)(a+a^2d^2/30)<.7$ by direct differentiation. Also $\Re\phi(y)\le-.24y^2$ there. For the leading term use $\Re t^{2/3}-1\ge y^2/9-56y^4/(81\cdot24)$ by Taylor expansion through degree three. The fourth-order energy correction costs at most $(2/9)(a^2d^2/30)y^2$ by its second derivative.

## Contraction at both parity changes

Let $B$ be the real even-to-odd single step normalized by $\sqrt\lambda$, with real unit ground vectors $u_e,u_o$ such that $Bu_e=u_o$, $B^*u_o=u_e$. Let $U_e,U_o$ multiply height $j$ by $e^{-i\theta j/4}$ on their parity spaces. The complex single step from even to odd is $U_o B U_e$ up to an overall phase. With $G=1.48d^2$, $g=U_e^*u_e$, and $g_2=U_e^*B^*U_o^{-2}u_o$, applying the singular gap on *both* steps gives
$$
 \|Az\|^2\le(1-G)^2\|z\|^2+G(1-G)|\langle g,z\rangle|^2
                         +G|\langle g_2,z\rangle|^2. \tag{4}
$$
Indeed the squared norm after the second step is bounded by $1-G$ times the first squared norm plus $G$ times its squared component along $U_o^*u_o$. Pull that component back through the first step. For the adjoint conjugate the two directions. The edge-law mean bound for either real ground parity is $\mathbb E j\le 2(-p'(\beta)+1/2)\le 3.6H+1$. Therefore both $\|g_2-g\|$ and $\|g-\bar g\|$ are at most $\epsilon_y=d\sqrt{|y|(3.6+d)}$, using $\|B^*\|\le1$ and $2(1-\cos(\theta j/2))\le|\theta|j$. [Real ground edge law and singular directions](airy-powers.md#a-power-bound-outside-the-perturbation-disk)

For $|y|\le3$ the corrected Airy sample has adjoint residual at most $\Delta_3d^2$ with $\Delta_3=25200d^4$. To reproduce this step use the [sample-norm recursion](airy-grid.md#sampling-the-half-line-eigenfunction) with $\Re t=1$, $|t|\le3.17$, $|at^{2/3}|\le5.06$, and the [two-step residual calculation](verify_folded_saddle.py). The fourth-order cancellations are polynomial identities in the potential. The exponential Taylor remainders are valid since $\Re(tx)\ge0$ and $\Re(at^{2/3}+a^2t^{4/3}d^2/30)>3d/2$, the latter following from $\Re t^{2/3}\ge1$. In particular the single-step trial scalar has modulus at most one. Here $|L-a(\Re t^{2/3}-1)|\le1.26d^2$ by the real grid energy.

Put $D_g=1.48(2-G)$. For $u$ the unit approximate adjoint direction and $L\le L_1$ on a band, (4) for the adjoint gives
$$ |\langle \bar g,u\rangle|\ \ge\
 c_0=\sqrt{1-2(L_1+\Delta_3)/D_g}-\epsilon_y . $$
In fact $\|A^*u\|\ge1-(L_1+\Delta_3)d^2$ while the last two terms of the adjoint bound are at most $G(2-G)(|\langle\bar g,u\rangle|+\epsilon_y)^2$. On the unit ball of $\max(\|z\|,B_0|\langle u,z\rangle|)$, both overlaps on the right of (4) are then at most $q_1=\sqrt{1-c_0^2}+2\epsilon_y+1/B_0$. For $g_2$ one may decompose $z$ orthogonally along $u$ first, using $\|g_2\|\le1$. The ordinary seminorm of $Az$ is bounded by $1-d^2D_g(1-q_1^2)/2$. Its other seminorm is bounded by $e^{-Ld^2}+B_0\Delta_3 d^2$. Iterating gives the following upper bounds $B_0 e^{-Cjd^2}$ for $\|A^j\|$.

| $\lvert y\rvert$ | $B_0$ | $C$ |
| --- | ---: | ---: |
| $.4$ to $.6$ | $1.6$ | $.235 y^2$ |
| $.6$ to $1$ | $2.5$ | $.21 y^2$ |
| $1$ to $1.4$ | $4$ | $.185 y^2$ |
| $1.4$ to $3$ | $35$ | $.14$ |

For the endpoint checks, $R(y)=\Re(1+iy)^{2/3}$ is increasing at positive $y$ by differentiation, and $(R(y)-1)/y^2$ is decreasing. Indeed the integral for $w^{2/3}$ is a positive constant times $\int_0^\infty [w/(u+w)]u^{-1/3}\,du$, by substitution at real $w>0$ and analytic continuation to $\Re w>0$. Subtract the integral at 1, take the real part and divide by $y^2$. The new factor is $u/[(u+1)((u+1)^2+y^2)]$. To enclose $R$ use $4R^3-3(1+y^2)^{2/3}R=1-y^2$ on its increasing branch. The verifier bounds the two seminorms separately at the endpoints, allowing the floor of the block length below.

## Inverting the short-walk comparison

Let $b=\lceil32H^2\rceil$, $N_0=(n-b)d^2$, $v=\sqrt{VN_0}$ and $x=vy$. Write $F_n(\beta)=2^{-m}\sum_k b_ke^{-\beta k}$, $c$ for the real principal amplitude of the chosen parity, and $J_n(y)=e^{-in\beta p'(\beta)y}F_n(t\beta)/(c\lambda^n)$. Define $S(y)$ by the same formula as $J_n$ at length $b$ in pairs, keeping the terminal parity fixed. On $|y|\le.4$, (2) gives the exact decomposition
$$ J_n(y)=(S(y)-R_b)e^{E(y)}+R_n,\qquad
 E(y)=(n-b)(\log\eta-i\beta p'(\beta)y),\qquad
 |R_j|\le1.26e^{-.67(jd^2-25)}. \tag{5} $$
Peel $\lceil12H^2\rceil$ pairs at each boundary before applying (2). The real boundary norm product in ground units with the removed powers divided out is at most $1.003$ [by the two end-block estimate](folded-saddle.md#fourier-bounds-outside-the-center). Entrywise domination allows the same cost at complex tilt. The principal amplitude in this decomposition is common to the two lengths, since the end vectors and projection are the same. By (3),
$$
 \Re E\le P-.46x^2,\qquad
 |E+x^2/2|\le P+17000d^4N_0|x|/v+.7|x|^3/(6Vv),
 \qquad P=4800d^4N_0 . \tag{6}
$$

In the real tilted shorter walk put $Z=\beta(K+bp'(\beta))$. We have $.999<S(0)<1.001$, $S(y)=S(0)\mathbb E e^{-iyZ}$, and $\mathbb E Z^2<26$. For the latter use the [two-real-tilt estimate](folded-saddle.md#a-second-moment-test-at-the-saddle) at $w=\pm .1$. At these real shifts the height exceeds 110, the principal amplitude is within factors $.99,1.01$ of its continuum approximation proportional to the reciprocal height, and the real complementary-to-ground ratio is less than $.001$ by $20000e^{-1.48(32\cdot.9-2.01)}$. The real grid gives $p''\le .61H^4$ on the segment. In averaging the two exponential moments, the mean of $(1\pm.1)^{1/3}$ is at most one. Consequently
$$ 1+\mathbb E Z^2/200\le\mathbb E\cosh(.1Z)
 \le (1.001/.999)(1.01/.99)\exp[.61(32+d^2)/200] . $$

For growth the desired signed integral is bounded below by $\int\Re J_n\,dx-(1.001/v)\int |xJ_n|\,dx$. This is sufficient since $\beta/(1-e^{-\beta})<1.001$ and the tilted forward-difference multiplier costs at most $\beta|y|$. For curvature integrate $G(x)\Re J_n(x/v)$ with $G(x)=4(v/\beta)^2\sin^2(\beta x/(2v))$. The integrals are over the lattice period in scaled coordinates. For the main term first integrate $x^j e^{-x^2/2}S(x/v)$ over the full line, $j=0$ or $2$. Fourier inversion of the Gaussian gives lower bounds
$$
 \sqrt{2\pi}\,.999\big(1-26/(2v^2)\big),\qquad
 \sqrt{2\pi}\,.999\big(1-3\cdot26/(2v^2)\big),
$$
respectively. Under the short-walk law the two integrands after inversion are $e^{-z/2}$ and $(1-z)e^{-z/2}$ at $z=Z^2/v^2$. These exceed $1-z/2$ and $1-3z/2$.

For explicit error bounds put $U=.4v$ and $M_j=\int_{\mathbb R}|x|^je^{-.46x^2}\,dx$. Truncating the Gaussian to $|x|\le U$ costs at most $2.002e^{-U^2/2}$ times $1/U$ or $U+1/U$, respectively. By (6) and the integral interpolation of the two exponentials, the change from the Gaussian to $e^{E}$ costs at most
$$
 1.001e^P[P M_j+17000d^4(N_0/v)M_{j+1}+.7M_{j+3}/(6Vv)].
$$
The two remainders in (5) cost at most $\sup|R_b|e^P M_j+2\sup|R_n|U^{j+1}/(j+1)$. The core absolute integral with weight $|x|^j$ is at most $(1.001+\sup|R_b|)e^P M_j+2\sup|R_n|U^{j+1}/(j+1)$. Use this with $j=1$ for the first difference. For the second, changing $x^2$ to $G(x)$ on the core costs at most $.0001$ times the absolute integral with $j=2$, since $(.4\beta)^2/12<.0001$.

Outside the core, apply the four power bounds above with the warm end blocks. Above $|y|=3$ use the [mirrored-label Hölder calculation](folded-saddle.md#fourier-bounds-outside-the-center). With block length $\lfloor lH^2\rfloor$ pairs, Hölder exponent $p$ and rate $C$, the following parameters give the envelope $1.003e^{-C(N-26)}$ in the indicated successive bands.

| Left endpoint | 3 | 3.25 | 3.5 | 4 | 4.5 | 5 | 6 | 8 | 12 |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| $l$ | 1.10 | 1.05 | 1.05 | 1 | .95 | .9 | .8 | .65 | .4 |
| $p$ | 8 | 7 | 6 | 5 | 5 | 4 | 4 | 4 | 4 |
| $C$ | .059 | .068 | .078 | .099 | .121 | .145 | .19 | .27 | .24 |

The last band ends at 45. The verifier bounds each binomial harmonic sum, checks its arc restriction and includes both the floor cost and the real energy at conjugate exponent $p/(p-1)$. Beyond 45 peel only $\lceil H^2\rceil$ pairs at each end. Their product costs at most 20000 in ground units and the remaining length exceeds $1.95n$ single steps for $N\ge96$. The [full-period block estimate](airy-grid.md#boundary-factors-in-fourier-inversion), restoring the real energy at cost $e^{2.61N}$, gives $60000e^{-N|y|^{2/3}/30}$ through $|\theta|=1/64$, and $60000e^{-N|y|^{2/3}/80}$ above it. In the second arc $|y|\ge H^3/64$. Substitute $t=|y|^{2/3}$ in the two integrals. For weights through $|x|^2$ the polynomial is bounded by $t^4$ there. Extend the integrals down to 12 and 700, respectively, and bound $t^4\le t_0^4 e^{4(t-t_0)/t_0}$ on each tail. Each costs below $.0005$ even at $N=96$, and the estimates decrease thereafter.

The verifier integrates the outer bands against $|x|^j$, using nonnegative upper bounds on intervals of width $.01$ in $|y|$ through $1.4$, and the displayed constant envelopes thereafter. It uses intervals of width at most five in the real variable $N$, rounding each term in the indicated direction. For $96\le N\le360$ the first-difference margin exceeds $.103$. For $190\le N\le2100$, $\int G\Re J_n\,dx>.356$ and $\int |J_n|\,dx<2.82$. Thus at the saddle the tilted mass $g_k$ satisfies $-(g_{k-1}+g_{k+1}-2g_k)/g_k>.35\beta^2/(2.82v^2)$. Its relative log-concavity determinant is at least half that value by the arithmetic-geometric mean inequality. Untwisting the real tilt preserves the relative determinant. Since $v^2/\beta^2<.520nH^4$ and $k/n>(2a/3-.016)H$, this proves the lower bound $n^3/(2k^4)$. The [previous bounds](folded-saddle.md#strict-log-concavity-on-a-small-corank-interval) apply beyond the two upper endpoints.

## Joining the integer corank ranges

The [marked-return comparison](folded-saddle.md#folding-unmatched-steps-into-returns) gives strict growth if $2k+1\le L(\ell)$, where $\ell=n+(m\bmod2)$ and $L(\ell)$ is the sum of the $\ell$ least costs $4h+i+j$ for nonnegative integer triples. If $M(t)$ counts costs at most $t$, then $24M(t)<(t+7/2)^3$. Indeed for $t=4a_0+r$, $0\le r<4$, the difference is $19a_0+(r+7/2)^3-24\binom{r+2}{2}>0$ by summing the triangular numbers $\binom{t-4h+2}{2}$. Summing the resulting individual cost bounds yields
$$ L(\ell)/2\ge(3/8)24^{1/3}\ell^{4/3}-7\ell/4. $$
Here the sum of $j^{1/3}$ from one to $\ell$ bounds the integral from zero to $\ell$ below it. In particular $L(\ell)\ge L(n)$. The verifier checks $2k+1\le L(\ell)$ through $s/18$ directly for $2\le n<4096$. From 4096 use $m/n\le2.00025$. After division by $n$ the required lower margin for $s/u$ is $1.0816n^{1/3}-1.75-2.00025^{3/2}\sqrt n/u$, which is concave as a function of $n^{1/3}$. It exceeds $1/4096$ at both endpoints of $[4096,80000]$ for $u=18$ and of $[4096,4500000]$ for $u=34$.

At $H=114$ the grid bound on $-p'$ is
$$ 114(2a/3)-3/2+4a^2/(90\cdot114)+2000/(.12\cdot114^3)<176.3. $$
By monotonicity and existence of the real saddle, $k/n\ge176.3$ therefore gives $H>114$. For $n\ge4500000$, any $k$ beyond the combinatorial comparison has $k\ge L(n)/2>176.3n$. Throughout the saddle range $k/n>(2a/3-.016)H$. Hence for $k\le s/u$, $N>u^2(2a/3-.016)^2/(m/n)^3$. In each nonempty interval with $k\ge177n$ and $u=18$ or $26$ one has $n>1000$ (otherwise use $m/n\le3$), so $m/n\le2.001$. The lower bound for $N$ exceeds 96 at $u=18$, and 190 at $u=26$. This proves all three assertions.

### A bounded parameter range for the intermediate sizes

One can further locate the comparisons needed to extend $s/18$ to the omitted sizes. Any such step beyond the marked-return range needs only the real saddle parameters
$$ 28<H<114,\qquad 87<N<365, $$
unless its sign already follows from the theorem above.

For detail, set $\bar p(\beta)=-a\beta^{2/3}+3\beta/2-a^2\beta^{4/3}/30$. The real bound
$$ |p(\beta)-\bar p(\beta)|\le260H^{-6}\quad(H\ge26) $$
also holds below the height range of the complex grid estimate. Use the same corrected-sample calculation at $t=1$, $|E|<2.34$, $d\le1/26$. The residual for the real matrix $K_\beta$ at the trial eigenvalue $e^{\bar p}$ is less than $252d^6$ (the normalized-matrix bound also suffices since $\lambda\le1$). The spectral theorem puts a spectral point within that distance. The [real nodal cut](flat-pairs.md#estimates-down-to-height-scale-four) and the [real upper energy bound](mode-bounds.md#upper-bound-for-a-single-small-corank) show that the second eigenvalue is at most $e^{-2.60d^2}$. Indeed the initial segment in the short-cut case has two-step bound $(1-4d^2)^2$, and in the long-cut case use $\lambda e^{-(1-d)d^2}\le e^{-(2.65-d)d^2}$. Meanwhile $\bar p\ge-2.339d^2$. The separation exceeds $252d^6$, so the nearby spectral point must be the top one. Taking its logarithm gives the claimed error.

For $H\ge28$ use the secants of the convex function $p$ at $\beta(1\pm.05)$. Both shifted heights exceed 26. In units $H^2$, the second derivative of $\bar p((1+w)\beta)$ with respect to $w$ has modulus below $.61$ on this interval. Thus $-p'(\beta)/H$ differs from $2a/3-1.5d+4a^2d^2/90$ by at most $.61(.05)/2+260[1+1.05^2]d^4/.05$. The result lies between $1.47$ and $1.575$. For the upper inequality the bound is convex in $d$ and it suffices to test $0,1/28$.

Now $80000<n<4500000$ and $k\ge L(n)/2$ force $k/n\ge1.0816n^{1/3}-1.75>28\cdot1.575$, hence $H>28$ by slope monotonicity. At $H\ge114$ the new saddle test covers the step. Otherwise the lower slope bound and $k\le s/18$ give $N>87$. The upper slope bound gives $N\le H[(1.575+1.75/H)/1.0816]^3<365$, since the displayed upper bound increases from $H=28$ to 114. This reduction is for the small-corank growth assertion. Even its full resolution would leave the peak comparisons.

The remaining all-size problem includes the peak where the adjacent differences change sign. For example, at $4500000\le n<10^{13}$ the outstanding comparisons in corank now lie between $s/18$ and $3s/5$, allowing adjacent boundary indices, by the [upper-corank first-passage bound](marked-hits.md). The finite certificate and the large-size theorem still leave $2049\le n<10^{13}$ for full unimodality.

~~~sh
python3 -B verify_saddle_phase.py
python3 -B verify_folded_saddle.py
python3 -B verify_airy_grid.py
python3 -B verify.py --max-n 64 --direct-n 12 --upper-curvature
~~~

The first three commands certify uniform inequalities from the transfer argument and its inputs. The final command independently compares the integer coefficients with strict-partition enumeration in both families through twelve rows.
