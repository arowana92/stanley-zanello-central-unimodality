# A fourth-order energy estimate at complex area weights

Let $p(\beta)$ be the logarithm of the leading eigenvalue of the [two-step ballot transfer](effective-small-area.md#real-transfer-operator), $H=\beta^{-1/3}$, $d=1/H$, and $a$ the first Dirichlet eigenvalue of $-\partial_x^2+x$ on the half-line. For $H\ge100$ and complex $|t-1|\le.12$ the continuation of that eigenvalue satisfies
$$
 \left|H^2 p(t\beta)+a t^{2/3}-\frac{3t}{2H}
                      +\frac{a^2 t^{4/3}}{30H^2}\right|\le\frac{2000}{H^4}. \tag{1}
$$
The powers use their branch positive at $t=1$. The estimate applies to both staircase polynomials because their transfers differ only in the terminal vector. In particular **the corank coefficients satisfy $b_{k+1}>b_k$ at every integer saddle $k=-np'(\beta)$ with $H\ge110$ and $n/H^2\ge100000$**. The proof of the sign averages a translated Gaussian against an actual shorter walk.

## Sampling the half-line eigenfunction

On the grid $x=(j+1)d$, $j\ge0$, impose the boundary value zero at $x=0$. Write $V=tx$, $E=at^{2/3}$ and $L=E^2/30$. Removing the factor $e^{3td^3/4}$ from $T_{t\beta}/2$ gives the single-step operator
$$ B u(x)=e^{-Vd^2/2}\{e^{td^3/4}u(x-d)+e^{-td^3/4}u(x+d)\}/2.$$
Thus the location of the Dirichlet wall accounts for the term $3t/(2H)$ after two steps. Let $f$ be a unit $L^2$ multiple of $\mathrm{Ai}(t^{1/3}x-a)$. Then $f(0)=0$ and $f''=(V-E)f$. This choice follows by solving the real Dirichlet eigenvalue equation and then substituting the complex argument into the Airy equation. The decaying Airy solution and its derivatives decay exponentially along these rays. This justifies the integrations by parts below. [Airy asymptotics](https://dlmf.nist.gov/9.7#ii) · [Real zeros](https://dlmf.nist.gov/9.9#i)

Set
$$ F=\frac{2tx}{15} f+\frac{t x^2-2Ex}{30} f',\qquad
 U=f+d^2 F,\qquad \zeta=e^{3td^3/4-(E+Ld^2)d^2/2}.$$
In particular $F(0)=0$. The fourth-order term in the single-step Taylor expansion of $B$ is
$$ J u=u^{(4)}/24-Vu''/4+V^2u/8-tu'/4.$$
Differentiation gives
$$(-\partial_x^2+V-E)F=(L-(V-E)^2/6)f-t f'/3
                         =2J f+(L-E^2/4)f.$$
Indeed, for $F=A f+C f'$ the two coefficients on the left are $-A''-2C'(V-E)-t C$ and $-2A'-C''$. This identity cancels the terms of degree four in $BU-e^{-(E+Ld^2)d^2/2}U$. The choice of $L$ also makes the corrected eigenfunction satisfy the boundary condition.

Here are quantitative remainder details. Write $\|u\|_d^2=d\sum_{j\ge0}|u((j+1)d)|^2$. Comparing samples to $u$ on the preceding cells gives $|\|u\|_d-\|u\|_2|\le d\|u'\|_2$. On the even-height subgrid the analogous bound with cells of width $2d$ centered at the sample points gives $\sqrt2\|u_{\rm even}\|_d\ge\|u\|_2-2d\|u'\|_2$.

For a unit-normalized $f$ put $A_i=\int(1+x)^i|f|^2$. For $w=(1+x)^{i/2}$ the real part of the weighted equation gives
$$\|(wf)'\|^2+\Re t\int x w^2 |f|^2=\Re E\|wf\|^2+\|w'f\|^2.$$
With $T=1.12$ and $E_0=2.81$ we have $|t|\le T$, $|E|<E_0$, $\Re t\ge.88$. Starting at $A_0=1$, bound $A_{i+1}$ above by $(1+E_0/.88)A_i+i^2 A_{\max(i-2,0)}/(4\cdot.88)$. Also $\|(1+x)^j f'\|\le\sqrt{E_0 A_{2j}+j^2 A_{\max(2j-2,0)}}+j\sqrt{A_{\max(2j-2,0)}}$. To bound a derivative of $P f+Q f'$ update the polynomial pair to $(P'+(V-E)Q,P+Q')$. These formulas give all norms in the following error estimates. Unsubscripted norms denote continuous $L^2$ norms.

For the average of the shifts of $f$ through degree four the error in grid norm is at most $d^6\|f^{(6)}\|/120$. For each one-sided Taylor formula, Cauchy–Schwarz on each adjacent cell bounds the integral remainder in grid norm by $d^k\|f^{(k)}\|/(k-1)!$ after degree $k-1$. Average the two formulas through degree five. Similarly the antisymmetric difference divided by two has error at most $d^3\|f'''\|/2$ after its linear term. Write $c=td^3/4$. The factors $\cosh c-1$ and $\sinh c-c$ cost together less than $.07d^6$ times the sample norm, since either one-sided shift is contractive on sampled functions vanishing at the boundary. Expand $e^{-Vd^2/2}$ using integral remainders bounded by the corresponding powers divided by factorials, since $\Re V\ge0$. In units of $d^6$ the error for $Bf$ through degree four is bounded by
$$
 \|f^{(6)}\|/120+\|V^3 f\|_d/48+\|V^2 f''\|_d/16+
 \|V f^{(4)}\|_d/48+T\|Vf'\|_d/8+T\|f'''\|/8+.07\|f\|_d <29.
$$
For $BF$ through degree two, in units of $d^4$, the bound is
$$\|F^{(4)}\|/6+\|V^2 F\|_d/8+\|VF''\|_d/4+.30\|F'\|+.07d^2\|F\|_d<150.$$
Here the antisymmetric difference costs at most $d\|F'\|$. The scalar exponential through degree four costs less than $d^6$ on $f$, and through degree two less than $1.3d^4$ on $d^2F$ before multiplying by $d^2$. We have $\|F\|_d<4$. Altogether the error is below $200d^6$. The [rational checker](verify_airy_grid.py) evaluates the norm recursions above, including the derivative in passing to the grid.

The even-height sample of $U$ has norm greater than $.68$ by the subgrid bound and $\|f'\|\le\sqrt{E_0}$. Squaring the one-step operator costs at most two since $\|T_{t\beta}/2\|\le1$ by entrywise domination and $|\zeta|\le1$. Thus for the normalized even sample $v$,
$$ \|(K_{t\beta}-\zeta^2)v\|\le600d^6. \tag{2}$$

## Identifying the eigenvalue for complex $t$

At $t=1$ the residual puts a real spectral point within $600d^6$ of $\zeta^2$. Only the top eigenvalue qualifies. Indeed the [nodal cut at $1.5H$](two-harmonics.md#analytic-control-on-a-wider-disk) gives $\lambda_2\le\max(1-4.30d^2,\lambda e^{-1.5d^2})$ and the [real upper bound](mode-bounds.md#upper-bound-for-a-single-small-corank) gives $\lambda\le e^{-1.65d^2}$. The resulting separation from $\zeta^2(1)\ge e^{-2.60d^2}$ exceeds $.54d^2$. The sine trial and the same cut give $\lambda-\lambda_2\ge1.48d^2$ at $H\ge100$.

On the circle of radius $.74d^2$ about $\lambda$, the [factored resolvent](harmonic-small-area.md#real-and-complex-estimates-near-the-saddle) has $M\le5.52$ and form perturbation at most $|t-1|$. Consequently the complex resolvent norm is at most $2.97/(.74d^2)$ and its rank-one projection $\Pi$ has norm below $2.97$. The target $\zeta^2(t)$ stays within $.24d^2$ of $\lambda$ by differentiating its explicit exponential along the segment from 1 and using (2) at 1. Integrating $(u-K_{t\beta})^{-1}(K_{t\beta}-\zeta^2)v/(u-\zeta^2)$ around the circle gives $(\Pi-I)v$ after division by $2\pi i$. Hence $\|(I-\Pi)v\|\le 2.97\cdot600d^4/(.74-.24)$. Applying $\Pi$ to (2) bounds $|\lambda_{t\beta}-\zeta^2|$ by $2.97\cdot600d^6/\|\Pi v\|$. The logarithm costs at most a factor $1/.99$ since the segment stays in $|z-1|<.01$. This proves (1) without using a self-adjoint spectral-distance estimate at nonreal tilt.

By Cauchy's inequalities and $1.65\le a<2.60$, the consequences needed below are
$$
 -p'(\beta)/H>2a/3-.016,\quad .35<p''(\beta)/H^4<.60,\quad
 |p'''(t\beta)|/H^7<\begin{cases}1&|t-1|\le.01,\\3&|t-1|\le.08.\end{cases}
$$
Also $H^2\Re(p((1+iy)\beta)-p(\beta))\le-.17 y^2$ for $|y|\le.08$. For this last assertion the analytic remainder in (1) is real on the real axis. Its even Taylor terms cost at most $(2000/H^4)y^2/(.12^2-.08^2)$. The main energy uses $\Re(1+iy)^{2/3}\ge1+.109y^2$. The correction in $t^{4/3}$ costs at most $(2/9)(a^2/30)d^2 y^2$ by its second derivative.

## Boundary factors in Fourier inversion

Write $N=n/H^2$, $\lambda=e^{p(\beta)}$, $c=c(\beta)=e_0\Pi_\beta W_\delta(\beta)$, and $y=\theta/\beta$. Peel $l=\lceil20H^2\rceil$ pairs at each end of the transfer. Their real norm product is at most $1.001 c\lambda^{2l}$. In fact after $l_0=\lceil H^2\rceil$ pairs the two norms, divided separately by their ground-state components, have product below $20000$. Use the [boundary estimates](harmonic-small-area.md#real-and-complex-estimates-near-the-saddle) giving product $10/H$, $c>.1/H$ and $-H^2p<2.61$ by (1). Each ratio is at least one. Over the remaining $l-l_0\ge18 H^2$ pairs the component perpendicular to the ground state loses a factor at most $e^{-1.48\cdot18}$ relative to it. Pythagoras gives the asserted product bound. The same norm product dominates the complex boundary factors by entrywise comparison. Similarly the real full transform divided by $c\lambda^n$ differs from one by at most $20000 e^{-1.48(n-2l_0)/H^2}$ whenever $n\ge2l_0$.

Suppose now $H\ge110$ and $N\ge100000$. For $4.5\le|y|\le9$ the [Hölder block](holder-blocks.md#a-block-inequality) of $\lfloor H^2\rfloor$ pairs has relative norm less than $.924$. The twelfth harmonic meets the spacing condition $12|y|/H\le\pi$. In the real energy comparison at $b=6/5$ both height scales exceed 100. The linear correction in (1) cancels from $H^2(p(b\beta)/b-p(\beta))$, the quadratic correction is nonpositive and the two remainders cost less than $.00005$. Thus the earlier block estimate applies with this error. After the two boundary factors there are at least $.996(N-42)$ blocks. The integer-multiple comparison in that proof gives relative damping $\exp[-(N-42)B(y)]$, with $B=.0034y^2$ through $.2$, $.00249y^2$ from $.2$ to 1, $.00093y^2$ from 1 to $4.5$, and $.075$ from $4.5$ to 9. These bounds allow a prefactor $1.01$ for either the transform normalized by its ground component or by its actual real mass. For $9\le |y|\le45$ use the [block of $\lfloor H^2/4\rfloor$ pairs](two-harmonics.md#a-bound-for-arbitrary-retained-paths) at a multiple with absolute scaled frequency in $[45,90]$. Its spacing condition holds since $45/H<\pi$. There are at least $3.99(N-42)$ blocks, giving $B=.005$ even with only $.996(N-42)$ of them.

For $45\le |y|$ and $|\theta|\le1/64$ the [retained fair two-frequency estimate](centered-clock.md#fourier-inversion-and-the-peak) gives a row bound $e^{.83-.124s_0|\theta|^{2/3}}$ over $s_0=2(n-2l)\ge1.99n$ single steps. Here one uses the per-step rate without the surviving prefix. The block estimate allows every real weight in $[0,1]$. Symmetry bounds the norm by the same expression. Dividing by the real middle eigenvalue costs at most $e^{2.61N}$. The result including the boundary factors is at most $3e^{-.04N |y|^{2/3}}$. For $|\theta|>1/64$ we have $|y|>10^4$ and the [full-period bound](harmonic-small-area.md#comparing-two-frequencies) similarly gives $3e^{-N |y|^{2/3}/80}$. All lattice estimates are restricted to one Fourier period.

## Integrating the shorter walk at the saddle

Let $k=-np'(\beta)$ be integral, $b=\lceil400H^2\rceil$, $d_0=\beta\sqrt{(n-b)p''(\beta)}$, and $x=d_0 y$. Use the [shorter centered transform](holder-blocks.md#signed-inversion-at-the-small-area-saddle) $S(w)$ and centered log eigenvalue $P(w)=p(\beta(1+w))-p(\beta)-\beta p'(\beta)w$. For $|y|\le.08$ the centered full transform in units $c\lambda^n$ is
$$ J=(S(iy)-R_b(iy))e^{(n-b)P(iy)}+R_n(iy),\qquad
       |R_j|\le e^{20-.16 j/H^2}.$$
The [complement bound](two-harmonics.md#analytic-control-on-a-wider-disk) uses the nodal gap and real energy established above. The short-walk real moment bounds $S(\pm.08)<e^{11}$ hold by the [boundary-block proof](two-harmonics.md#signed-inversion-after-twenty-million-blocks-on-the-height-scale) with $p''<.68H^4$ along the shifted segment. Indeed the shifted heights exceed 100 and (1) gives $.60(.92)^{-4/3}<.68$. The real prefactor bound $103e^{5.23}$ also holds here using $l_0/(H')^2\le1+10^{-4}$ at the shifted height $H'$. Thus $.999<S(0)<1.001$ and $S(iy)/S(0)=\mathbb E e^{-iy Z}$ for the shorter tilted walk's real centered area $Z$. Integrating $\Pr(|Z|>u)\le\min(1,2e^{11-.08u}/.999)$ gives $\mathbb E Z^2<26000$.

In particular the Gaussian Fourier integral on the entire real line satisfies
$$ \int e^{-x^2/2} S(ix/d_0)\,dx
 =\sqrt{2\pi} S(0)\mathbb E e^{-Z^2/(2d_0^2)}>1.55.$$
Use $e^{-v}\ge1-v$ and $d_0^2>.35(N-401)$. Its tail beyond $|y|=.08$ costs less than $.001$, since $.08 d_0>14$. On the local interval the error in replacing the full exponent by the Gaussian one is bounded by
$$ \left|e^{(n-b)P(iy)}-e^{-x^2/2}\right|
 \le\frac{3 |x|^3}{6\cdot.35d_0}\,e^{-.28x^2}.$$
This uses (1)'s cubic estimate, the real-part bound, and the integral of the exponential derivative along the segment between exponents. Its integral times $|S(iy)|$ costs less than $.10$. The complementary errors have integrated cost less than $.001$ on this interval (also with weight $1+1.001|y|$). The local principal term integrated against $1.001|y|$ costs less than $.020$, using its majorant $1.002 e^{-.28x^2}$.

To undo the tilt it suffices that $\int \Re J\,dx>\int 1.001|yJ|\,dx$. Indeed the ratio of the adjacent tilted mass change to the tilted mass at $k$ is bounded in modulus by $\int |\theta J|/\int\Re J$, and $\beta/(1-e^{-\beta})<1.001$. Outside the local interval pay the single absolute integral with weight $1+1.001|y|$. In the intervals $[u,v]=[.08,.2],[.2,1]$ (including negative frequencies), the two costs are below $1.27$ and $.002$ respectively. The bound in each case is $1.01(1+1.001 v)d_0 e^{-C u^2}/(Cu)$ with $C=.0034(N-42)$ or $.00249(N-42)$. From 1 through 45 the costs are below $.002$ by the constant lower bounds on $B$. Beyond 45 the stretched exponential costs less than $.001$ using $d_0<\sqrt{.60N}$ and the weaker rate $1/80$ throughout. For instance split off $e^{-N45^{2/3}/160}$ and integrate $6 d_0(1+1.001y)e^{-y^{2/3}}$. All bounds improve beyond $N=100000$. Subtraction leaves a positive margin, proving the corank sign.

## Independent finite-matrix check of the correction

The verifier also brackets the top eigenvalue of the infinite **real** single-step matrix $T_\beta$ at $H=8,16,32$. Cut after $16H$ vertices. Deleting the last edge gives a lower bound by restriction. To obtain an upper bound, replace that edge by its weight on both incident diagonal entries, using $2uv\le u^2+v^2$. The tail norm is at most twice the cut-edge weight, below the computed lower bound. Dyadic enclosures of the finite nonnegative matrices give bounds by entrywise monotonicity. The program bisects their top eigenvalues by testing positivity of all leading principal minors of $xI-T$ in integer arithmetic. The bracket widths are below $4096\cdot2^{-64}$.

Using the bracket midpoint for display, solve $a_H+a_H^2/(30H^2)=-H^2p+3/(2H)$ for its positive root. This gives $2.3381137674$, $2.3381078088$, $2.3381074354$ respectively, approaching the first Airy zero in absolute value ($2.3381074105$ to ten decimal places). These three finite samples check the sign and scaling of the correction independently of the residual argument. [Tabulated Airy zeros](https://dlmf.nist.gov/9.9#v)

~~~sh
python3 -B verify_airy_grid.py
~~~
