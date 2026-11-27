# Strict growth through one sixteenth of the ballot area scale

Let $m=2n$ for $(2n-1,2n-3,\ldots,1)$ and $m=2n+1$ for $(2n,2n-2,\ldots,2)$. Write $s=m^{3/2}$ and $b_k$ for the number of strict subpartitions missing $k$ cells from the full shape.

**Theorem.** For both staircases and every $n\ge2$, $b_{k+1}>b_k$ at each integer $0\le k\le s/16$. For every $n$ there is strict log-concavity at every integer $35n\le k\le s/25$. In the range $35n\le k\le s/26$ it satisfies
$$
 b_k^2-b_{k-1}b_{k+1}>\frac{n^3}{2k^4}\,b_k^2.
$$

The previous uniform growth range was $s/34$, and its curvature estimate began at $177n$. The proof below covers the previously omitted intermediate sizes by lowering the admissible height scale to 23. It controls the error of the complex eigenvalue to second order at the true saddle. This makes the estimates valid for arbitrarily many blocks at each admissible height. [Previous phase comparison](saddle-phase.md) · [Rational verifier for this proof](verify_moderate_saddle.py)

## Height moments for the Airy trial function

Use the [symmetric ballot transfer](effective-small-area.md#real-transfer-operator) $K_z=(T_z/2)^2$ on even heights, where the edge $(j,j+1)$ of $T_z$ has weight $e^{-jz/2}$. Write $p(\beta)=\log\lambda$ for the real top eigenvalue in logarithmic units, $H=\beta^{-1/3}$, $d=1/H$, $N=n/H^2$, $t=1+iy$ and $\theta=\beta y$. The real first Airy energy is $2.337<a<2.339$. Set
$$
 \bar p(z)=-az^{2/3}+3z/2-a^2z^{4/3}/30 .
$$
All powers use the branch positive on the real axis.

Let $f$ be the unit $L^2$ Dirichlet solution of $f''=(tx-E)f$ with $E=at^{2/3}$ and put $R=\Re E$, $B=\Im E$. Define $M_j=\int x^j|f|^2$, $D_j=\int x^j|f'|^2$, and $J=\Im(f'\bar f)$. Integrals here are on the positive half-line. Testing the equation against $x^j\bar f$ and integrating by parts gives
$$
 D_j=RM_j-M_{j+1}+\tfrac12 j(j-1)M_{j-2},\qquad
 J'=(yx-B)|f|^2 .
$$
Terms with a zero coefficient are omitted. Since $J$ vanishes at both ends, $M_1=B/y$ when $y\ne0$, hence $M_1\le2a/3$ by integrating the derivative of $(1+iy)^{2/3}$. Testing instead against $x^j\bar f'$ and taking real parts gives for $j\ge1$
$$
 (2j+1)M_j=2jRM_{j-1}+\tfrac12j(j-1)(j-2)M_{j-3}
                  +2\int x^j(yx-B)J .
$$
These integrations are justified by the decay of the [Airy solution on these rays](airy-grid.md#sampling-the-half-line-eigenfunction).

At $y=0$ this is an exact positive recurrence in $a$, including $M_1=2a/3$ and $D_0=a/3$. For $y\ne0$, integrate $J'$ against $x^{j+1}$ and $x^{j+2}$. With $\mu=B/y$, the last integral before its factor two equals $y^2$ times the integral of $x^{j+1}|f|^2$ times
$$
 -\frac{x^2}{j+2}+\mu x\left(\frac1{j+1}+\frac1{j+2}\right)-\frac{\mu^2}{j+1}.
$$
Completing the square bounds this quadratic by $\mu^2/[4(j+1)^2(j+2)]$. Put $\epsilon=B^2/[2(j+1)^2(j+2)]$. Using $D_j\ge0$ gives
$$
 (2j+1-\epsilon R)M_j
 \le 2jRM_{j-1}+\tfrac12 j(j-1)(j-2)M_{j-3}
                 +\tfrac12\epsilon j(j-1)M_{j-2}.
$$
The verifier checks positivity of every denominator. It applies this recurrence to upper bounds for $R,|B|$ over each frequency interval, using $|B|\le\min(|E|,2a|y|/3)$. Substituting $\sqrt{M_{2j}},\sqrt{D_{2j}}$ in the [corrected Airy sample's Taylor bounds](airy-grid.md#sampling-the-half-line-eigenfunction) controls the grid residual. The sampled function there is $f+d^2F$, where $F=2txf/15+(tx^2-2Ex)f'/30$, with trial eigenvalue $\exp\bar p(t\beta)$ for two steps.

## Real energy and the two boundary vectors

The [nodal cut](effective-small-area.md#real-transfer-operator) gives $\lambda-\lambda_2\ge1.48d^2$ for $H\ge20$. A cut after at most $1.5H$ vertices has squared norm at most $\cos^2(\pi/(1.5H+1))\le1-4.08d^2$, and the sine trial gives $\lambda\ge1-2.60d^2$. Farther out the tail has squared norm at most $\lambda e^{-1.5d^2}$. The real sample residual is below $64d^6$. Only the top eigenvalue can be this close to $\exp\bar p(\beta)\ge e^{-2.339d^2}$, since $\lambda\le e^{-1.65d^2}$ and the gap give $\lambda_2\le e^{-2.60d^2}$. Taking logarithms yields $|p-\bar p|\le65d^6$ and $-p<2.34d^2$. [Real sine trial](flat-pairs.md#estimates-down-to-height-scale-four) · [Upper energy bound](mode-bounds.md#upper-bound-for-a-single-small-corank)

Write $u$ for the positive unit ground vector of $T_\beta$, $\rho=2\sqrt\lambda$, and $h$ for the height coordinate. The [ground-state quadratic form](effective-small-area.md#real-transfer-operator) at $(h-\mathbb E h)u$ is $\rho/2$, with the expectation under $u_h^2$. Since $\rho-\rho_2\ge1.48d^2$, the variance of $h$ is at most $H^2/1.48$. Also $\mathbb E h=-p'(\beta)+1/2$ by the edge law. Convexity gives $-p'(\beta)\le-p(\beta)/\beta<2.34H$. On either parity the second moment is at most twice the full second moment. Therefore the change of the parity ground vector on multiplying by $e^{i\theta h/2}$ has norm at most $1.8|y|d^2$. This follows from $|e^{iv}-1|\le |v|$.

For $H\ge21$, put $I=\int f$ at real tilt, and let $c$ be the principal amplitude of the chosen parity in $2^{-m}\sum b_k e^{-\beta k}$. Then
$$ .94 I/H<c<1.05 I/H,\qquad I>1. $$
Indeed $\|f\|_\infty^2\le\|f\|_2\|f'\|_2$ by integrating $(f^2)'$ from both ends and averaging the two bounds. Now $D_0=a/3<1$ and $1=\int f^2\le I\|f\|_\infty$. For the amplitude use the [real boundary identity and quadratures](excursion-centers.md#the-lattice-saddle-at-height-220). Here the norm $s_U$ of the full corrected grid sample differs from one by at most $2.5d^2$. The trapezoidal error for $f^2$ costs at most $d^2(2a/3+2\|f''\|_2)/8$ in squared norm, and $\|F\|_d<.68$. The unnormalized single-step residual is below $23d^6$ from the same Taylor calculation, before multiplying by at least $2\sqrt2$ for the normalized two-step bound. Its trial scalar is within $64d^6$ of $\sqrt\lambda$ by the real energy comparison before taking logs. The rest of the spectrum is at distance above $.73d^2$, giving distance at most $46d^4$ from the normalized corrected sample to $u$. The sign is fixed by the positive uncorrected sample and the norm bound on $F$.

In the parity terminal sum $S=\sum_{h\equiv m\bmod2}u_h e^{-\beta\lfloor h/2\rfloor/2}$ the unnormalized quadrature error for the continuous profile is at most
$$
 A_d=d^2\big[6+(5.6+16d)/4+2.1+18d\big].
$$
The terms respectively use $\|f''\|_1<12$ on a mesh of width $2d$, $\|xf\|_1<5.6$ and $\|(xf)'\|_1<8$ for the terminal weight, and $\|F\|_1<2.1$, $\|F'\|_1<9$ for the correction. Each $L^1$ bound follows from $\|g\|_1\le\|(1+x)g\|_2$ and the real moments. Thus $|2\sqrt d S/I-1|\le(A_d+2.5d^2)/(1-2.5d^2)+184d^3$. The last term uses terminal norm at most $2d^{-3/2}$. Multiply by the [boundary factor](two-harmonics.md#a-boundary-identity-for-the-real-eigenvector) in $c=2u_0(\sqrt\lambda)^{m\bmod2}S$, where $2(1-e^{-\beta/2})\lambda\le u_0^2\le\beta$. This proves the amplitude bounds.

After $\lceil H^2\rceil$ pairs the [real end-vector norms](effective-small-area.md#complex-tilts-near-the-saddle) divided by their respective ground components, with powers of $\lambda$ removed, are at most 8 and 158. At the initial end use $H^{-3/2}/(\sqrt2 u_0)$, at the terminal end use $10\sqrt H\,\sqrt2 u_0/c$, and multiply each by $\lambda^{-\lceil H^2\rceil}$. After $\lceil5.5H^2\rceil$ pairs their product in ground units is at most 1.022, by the gap and Pythagoras applied separately to the two vectors. Entrywise domination gives the same product bound for complex end vectors. The shorter cuts cost at most 1270 in product.

## The analytic remainder at the saddle

Write $A=K_{t\beta}/\lambda$, $\nu=\exp(\bar p(t\beta))/\lambda$. At $H\ge20$, $|y|\le.4$, the new moments give residual $\Delta d^2$ with $\Delta=104d^4$ on the unit even-height trial vector and the conjugate adjoint vector. The single-step trial scalar has modulus at most one on every band used below since $\Re(at^{2/3})\ge a$ and $|at^{2/3}|<5.5$. Apply the [oblique projection and simple-root argument](saddle-phase.md#a-wider-interval-for-the-phase) with the real singular gap $1.48d^2$ and the improved direction shift $1.8|y|d^2$. For the trial modulus use
$$
 \big|-d^{-2}\log|\nu|-a(\Re t^{2/3}-1)\big|
 \le 65d^4+(.184)(2/9)d^2y^2
$$
from the real energy and the second derivative of $t^{4/3}$. In the cited argument the sine bound is $\sqrt{2(L+\Delta)/1.48}$ with $L$ an upper bound on $-d^{-2}\log|\nu|$. The verifier checks the projection denominator $>.8$, separation $>.60d^2$ in the scalar resolvent, and the contraction on the invariant complement. It gives a simple eigenvalue $\eta$ with $|\eta-\nu|\le1.3\Delta d^2$, and
$$
 \|A^j-\eta^j\Pi\|\le1.25e^{-.67jd^2},\qquad
 |\log(\lambda\eta)-\bar p(t\beta)|\le136d^6 .
$$

For $H\ge23$ this proves analyticity and the uniform estimate
$$
 |r(w)|\le256d^4,\qquad
 r(w)=d^{-2}\{p(\beta(1+w))-\bar p(\beta(1+w))\},\qquad |w|\le.37 .
$$
At each point apply the preceding vertical-segment result based at its real part. The height there exceeds 20, and the ratio of imaginary to real part is at most $.37/\sqrt{1-.37^2}<.4$. The distinguished eigenvalue is simple and has strictly larger modulus than the complementary spectrum. Its local analytic branches therefore agree, and its logarithm is fixed by its proximity to $\bar p$. The error increases by at most the factor $1.37^2$.

Set $V=2a/9-(4/9)(a^2/30)d^2\in(.518,.520)$ and
$$ P(y)=d^{-2}\{p(t\beta)-p(\beta)-iy\beta p'(\beta)\}. $$
With $\phi(y)=d^{-2}(\bar p(t\beta)-\bar p(\beta))$, the previous [phase derivative estimates](saddle-phase.md#a-wider-interval-for-the-phase) give $\phi''(0)=-V$, $|\phi'''|\le.70$ and $\Re\phi\le-.24y^2$ throughout the core. Cauchy's coefficient bounds give
$$
 |r(iy)-r(0)-iyr'(0)|\le\frac{256d^4y^2}{.37(.37-|y|)}\quad(|y|<.37).
$$
On the rest of $|y|\le.4$ the vertical estimate and the real estimate instead give $(136+65)d^4+|y|256d^4/.37$. For the real part the derivative term vanishes. Splitting the bounds at $.245$ for absolute error and $.20$ for real error proves
$$
 |P(y)+Vy^2/2|\le .024y^2+.70|y|^3/6,\qquad \Re P(y)\le-(.24-.019)y^2 .
$$
In particular the normalized phase error starts at order $y^2$ even for very large $N$. The same disk bounds $-p'(\beta)/H$ within $256d^4/.37$ of $2a/3-3d/2+4a^2d^2/90$. The upper bound $1.57$ improves the ground-direction shift to $1.3|y|d^2$ at $H\ge23$.

## Exterior frequencies

On the following bands the norm of $A^j$ is bounded by $B_0 e^{-Cjd^2}$.

| $\lvert y\rvert$ | $B_0$ | $C$ |
| --- | ---: | ---: |
| $.4$–$.6$ | 1.6 | $.23y^2$ |
| $.6$–$1$ | 2.5 | $.20y^2$ |
| $1$–$1.4$ | 4 | $.18y^2$ |
| $1.4$–$2$ | 7 | $.24$ |
| $2$–$2.5$ | 12 | $.24$ |
| $2.5$–$3$ | 26 | $.24$ |
| $3$–$3.25$ | 43 | $.17$ |

Use the [two half-step singular inequalities](saddle-phase.md#contraction-at-both-parity-changes). Given the normalized adjoint residual $\Delta d^2$ from the moment recurrence and upper loss $L$, define $G=1.48(2-1.48d^2)$, $\epsilon=1.3|y|d^2$ and $c_0=\sqrt{1-2(L+\Delta)/G}-\epsilon$. In the norm with second seminorm $B_0|\langle u,z\rangle|$ for adjoint sample $u$, the ordinary norm loses at least $d^2G[1-(\sqrt{1-c_0^2}+2\epsilon+1/B_0)^2]/2$. For the other seminorm the loss is at least $1-|\nu|-B_0\Delta d^2$. The verifier checks both losses at the bounding endpoints using the increase of $\Re t^{2/3}$ and decrease of $(\Re t^{2/3}-1)/y^2$ established in the cited proof. Remove the long end blocks to obtain a transform envelope $1.022 B_0 e^{-C(N-11.01)}$.

From $3.25$ through 45 use the [Hölder bands and block lengths](saddle-phase.md#inverting-the-short-walk-comparison) beginning at $3.25$. Keep their rates except for $.144$ on $[5,6]$. In a block of $\lfloor vH^2\rfloor$ pairs, retain the mirrored label pairs with the shortest odd separations at harmonic $j$. On $l\le |y|\le r$, their number divided by $H^2$ is at least $h_0=\min(v,\pi/(2jr d))-d^2$. They alone bound the harmonic by $\exp[-j^2 l^2(4h_0^3-vd^4)/48]$, since each of these pairs meets the [cosine arc condition](folded-saddle.md#fourier-bounds-outside-the-center) and every other factor is at most one. At conjugate exponent $b=p/(p-1)$ both real heights exceed 20. The scaled energy cost is at most $a(1-b^{-1/3})+65d^4(1+b)$. The verifier checks each binomial moment of order $4p$. The floor and both end blocks give the envelope $1.022e^{-C(N-13)}$.

Above 45 use the shorter end blocks and at least $1.94n$ remaining single steps for $N\ge70$. For $|\theta|\le.08$ the [two-harmonic fair bound](centered-clock.md#fourier-inversion-and-the-peak) still applies with pair separation $l=\lceil3.25|\theta|^{-2/3}\rceil$, since $2l|\theta|<\pi$ and $.83/(2l)>.12|\theta|^{2/3}$. On $.08\le|\theta|\le.5$ use $l=\lceil2|\theta|^{-2/3}\rceil$. Here $l|\theta|<\pi$, the unrestricted harmonic is at most $e^{-1/2}$, and the weighted retained row bound $(1+e^{-1/2})/2$ loses more than $.21$ in logarithmic units. This gives a rate above $.039|\theta|^{2/3}$ per step. Beyond $.5$ the [full-period bound](harmonic-small-area.md#comparing-two-frequencies) gives $|\theta|^{2/3}/75$. Restoring the real energy at cost $e^{2.34N}$ gives $3810e^{-N|y|^{2/3}/25}$ on the first arc and $3810e^{-N|y|^{2/3}/80}$ on the latter two. The verifier integrates these bounds with weights up to order two by putting $z=|y|^{2/3}$ and majorizing $z^4$ by $z_0^4e^{4(z-z_0)/z_0}$ above $z_0=12$ or 95.

## The signed coefficient comparison

Choose the unique real saddle $k=-np'(\beta)$ for a positive integer corank in the range below. Write $b=\lceil19H^2\rceil$, $N_0=(n-b)d^2$, $v^2=VN_0$, $x=vy$. Under the real tilt at the shorter length of $b$ pairs and the same terminal parity, let $Z=\beta(K+bp'(\beta))$ for its corank $K$. Write $S(y)=S(0)\mathbb E e^{-iyZ}$ for its transform divided by the real principal mass and centered as indicated. The real gap and shorter boundary blocks give $|S(0)-1|<.001$, also for the corresponding real mass ratios at the two shifted tilts $\beta(1\pm w)$, $w=.24$. Indeed their heights exceed 21 and their length in squared-height units exceeds 15.

We have $\mathbb E Z^2<21$. For the two real exponential moments apply the energy approximation at both tilts and the disk derivative error at the central tilt. The scaled quadratic Taylor remainder for $\bar p$ is at most $.600w^2/2$. Its second derivative along the segment, in scaled units, is bounded above by $.520(1\pm uw)^{-4/3}$ at fraction $u$ of the displacement. Bound the convex power by its endpoint chord and integrate against $1-u$, giving at most $.520[2+(1-w)^{-4/3}]/3<.600$ for the averaged second derivative. Average the two moment bounds. The mean of the amplitude scale factors $(1\pm w)^{1/3}$ is at most one, so
$$
 1+w^2\mathbb E Z^2/2\le\mathbb E\cosh(wZ)
 \le \frac{1.001}{.999}\frac{1.05}{.94}
 \exp\!\left[(19+d^2)\left(.600w^2/2+65d^4[1+(1+w)^2]+256d^4w/.37\right)\right].
$$

Let $J_n(y)$ be the analogously centered and normalized full transform. Its leading amplitude is common to both lengths, so the core projection identity gives
$$
 J_n=(S-R_b)e^{N_0P}+R_n,\qquad
 |R_j|\le1.28 e^{-.67(jd^2-11.01)} .
$$
For gain from $k$ to $k+1$, integrate the real part of $J_n$ times $M=1+(e^{i\theta}-1)/(1-e^{-\beta})$. This is the Fourier inversion of the original forward difference after multiplication by a positive constant. Exactly $|M|^2=1+\sin^2(\theta/2)/\sinh^2(\beta/2)\le1+y^2$.

Keep $M$ when integrating the shorter Gaussian over the full line. At $z=Z/v$ this gives $\sqrt{2\pi}$ times
$$
 g(z)+[g(z-\beta/v)-g(z)]/(1-e^{-\beta}),\qquad g(z)=e^{-z^2/2}.
$$
Since $\sup|g'|=e^{-1/2}$ and $\beta/(1-e^{-\beta})<1.001$, Jensen's inequality gives the normalized lower bound $\sqrt{2\pi}\,.999(\exp[-21/(2v^2)]-.608/v)$. For curvature use the multiplier $G=4(v/\beta)^2\sin^2(\theta/2)$. Its quadratic approximation $x^2$ gives the full-line lower bound $\sqrt{2\pi}\,.999(1-63/(2v^2))$, by the Gaussian transform $(1-z^2)e^{-z^2/2}\ge1-3z^2/2$.

For reproducibility, in the growth comparison put $W=1+x^2/(2v^2)$ and in the curvature comparison put $W=x^2$. Both dominate the respective multiplier moduli. On $|x|\le U=.4v$, replacing $e^{-x^2/2}$ by $e^{N_0P}$ in the shorter transform costs at most
$$
 1.001\int_{\mathbb R} W e^{-.424 x^2}
 \left(\frac{.024x^2}{.518}+\frac{.70|x|^3}{6\cdot.518 v}\right)dx
$$
by interpolating the exponents along their straight segment. The $R_b$ term costs $\sup|R_b|\int W e^{-.424x^2}dx$ and $R_n$ costs at most $3\sup|R_n|U^{j+1}$ for order $j=0,2$. Truncating the shorter Gaussian costs at most $2.002e^{-U^2/2}$ times $1/U+(U+1/U)/(2v^2)$ or $U+1/U$. In the curvature comparison replacing $x^2$ by $G$ on the core costs at most $.0001$ times the absolute second-moment integral there. Outside the core integrate the envelopes above with $\sqrt{1+y^2}$ for growth and $v^2 y^2$ for curvature, in units $dx=v\,dy$.

The verifier bounds the resulting signed integral below by $.06$ for growth at $N=71$, by $.03$ for curvature at $N=168$, and by $.30$ for curvature at $N=185$. In the last case $\int |J_n|\,dx<2.75$. Each stated bound holds above its threshold. The Gaussian lower bounds increase with $v$, the error moments have constant or decreasing coefficients, and the Gaussian tails decrease there. In the exterior bands every cost before rational rounding is bounded by a constant times $(N-19)^{(j+1)/2}e^{-cN}$ with $c\ge.23(.4)^2$ for $j\le2$. This expression decreases already at 71. The far-tail bounds with polynomial factor $N^{3/2}$ decrease from 70. These comparisons use the exact exponential before evaluating its rational majorant at the threshold.

## Returning to integer coranks

For strict growth use the [marked-return cost $L(\ell)$](folded-saddle.md#folding-unmatched-steps-into-returns), where $\ell=n+(m\bmod2)$. It proves the desired sign whenever $2k+1\le L(\ell)$. The verifier checks this condition through $s/16$ for $2\le n<4096$ by integer arithmetic. For $4096\le n\le38000$ use $L(\ell)/(2n)\ge1.0816 n^{1/3}-1.75$. Subtract $2.00025^{3/2}\sqrt n/16$ from the right side. The result is concave in $n^{1/3}$ and exceeds $1/4096$ at both endpoints, covering these sizes as well. [Lower bound for the cost](saddle-phase.md#joining-the-integer-corank-ranges)

Thereafter any step beyond the combinatorial bound has $k/n\ge L(\ell)/(2n)>34.6$, while the disk derivative estimate gives $-p'(\beta)<34.44$ at $H=23$. Thus the [real saddle and monotonicity of its slope](effective-small-area.md#real-transfer-operator) give $H>23$. At any such saddle the lower slope bound is
$$
 k/(nH) \ge c_* = 2(2.337)/3-1.5/23-256/(.37\cdot23^4)>1.4903 .
$$
If $k\le s/u$, then $N\ge u^2 c_*^2/(m/n)^3$. For $u=16$ and $m/n\le2.00025$ this exceeds 71. This proves the strict growth statement at all sizes.

For curvature $k\ge35n$ directly implies $H>23$. Either claimed interval, if nonempty, has $n>1000$ by $m\le3n$, so $m/n\le2.001$. With $u=25$ the lower bound on $N$ exceeds 168. The strict positive integral for $G$ gives a strictly negative centered second difference of the tilted probabilities at $k$, hence strict log-concavity on removing the tilt. With $u=26$ the lower bound exceeds 185. The relative negative second difference then exceeds $.30\beta^2/(2.75v^2)$. The relative log-concavity determinant is at least half that quantity by the arithmetic-geometric mean inequality, and is invariant under exponential tilting. Since $v^2/\beta^2<.520nH^4$ and $.30c_*^4/(2\cdot2.75\cdot.520)>1/2$, this proves the quantitative assertion.

## Direct checks and the open interval

The new verifier independently compares all coefficients from the ballot recurrence to direct enumeration of the strict partitions in 24 shapes through $n=12$. It checks 92 strict forward inequalities from the new growth range there. The rational bounds above prove the all-size result. Global unimodality still has a size gap $2049\le n<10^{13}$. Within those sizes the two all-size monotonicity results now leave only the interval between $s/16$ and $3s/5$ for the change of direction, allowing for adjacent boundary indices. [Large-size theorem](tilted-thinning.md) · [Finite certificate](certified-window.md) · [Opposite-side monotonicity](marked-hits.md)

~~~sh
python3 -B verify_moderate_saddle.py
python3 -B verify_saddle_phase.py
python3 -B verify_airy_grid.py
python3 -B verify.py --max-n 64 --direct-n 12 --upper-curvature
~~~
