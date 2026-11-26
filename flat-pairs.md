# Fourier damping from flat pairs

For both central staircases and every $n\ge100$ the corank coefficients increase strictly through $\lfloor10^{-11}n^{3/2}\rfloor$. At $n\ge10^{61}$ they increase strictly through $\lfloor10^{-5}n^{3/2}\rfloor$. In each interval the coefficients are also strictly log-concave at every integer $k\ge9n$. The estimates concern the end near the full diagram. The [mode comparison using concentration](tilt-concentration.md) covers the part near the peak at larger sizes.

## A norm bound on odd heights

Use the [symmetric transfer matrix](effective-small-area.md#real-transfer-operator). Thus $T_z$ has weights $e^{-jz/2}$ on the edges $(j,j+1)$, $K_z=(T_z/2)^2$ on even heights, $q=e^{-\beta}$ and $\lambda=\|T_\beta/2\|^2$. On **odd** heights put $A=(T_\beta/2)^2$ and write $A=D+E$ with $D$ diagonal and $E$ off-diagonal. Returning in two steps to height $2i+1$ has two possibilities, including at height one. Their real weights are proportional to $1,q$. This is the [flat pair in the exact recurrence](paired-steps.md#an-exact-stabilization-identity).

At $z=\beta+i\theta$ the absolute value of each diagonal entry is multiplied by $t=|1+q e^{i\theta}|/(1+q)$, while each off-diagonal entry comes from just one path. Thus the matrix of entrywise moduli on odd heights is $A-(1-t)D$. Conjugating $A$ by alternating signs shows $D-E\ge0$ as a quadratic form. Hence $D\ge A/2$. The norm of an entrywise nonnegative symmetric matrix is its largest Rayleigh quotient, so this modulus matrix has norm at most $(1-(1-t)/2)\lambda$. Each of the two single steps switching between parity spaces has norm at most $\sqrt\lambda$ by entrywise domination. For $b\ge1$ and $|\theta|\le\pi$ this gives the all-size inequality
$$
\|K_{\beta+i\theta}^{b}\|\le\lambda^b
 \exp\left(-\frac{(b-1)q}{2(1+q)^2}(1-\cos\theta)\right). \tag{1}
$$
Indeed $t^2=1-2q(1-\cos\theta)/(1+q)^2$ and $1-\sqrt{1-v}\ge v/2$. The bound also holds for the norm of the entrywise moduli of the entire power, by multiplying the bounds for its factors.

## Estimates down to height scale four

Put $H=\beta^{-1/3}\ge4$, $p=\log\lambda$, and $\rho=2\sqrt\lambda$. We use the following bounds in place of the ones at $H\ge20$ in the [harmonic proof](harmonic-small-area.md#real-and-complex-estimates-near-the-saddle).
$$
 2-\rho\le 2.60/H^2,\quad -p\le2.72/H^2,\quad
 \lambda-\lambda_2\ge .60/H^2,\quad p''(\beta)>.0084H^4. \tag{2}
$$
For the first bound use the sine vector on $L=\lfloor3H\rfloor$ vertices. In the products of successive coordinates the mean lower edge index is $(L-2)/2$ by symmetry. Since $e^{-j/(2H^3)}\ge1-j/(2H^3)$, the Rayleigh quotient is at least $2\cos(\pi/(L+1))(1-(L-2)/(4H^3))$. The scaled energy is at most $\pi^2/9+3/2<2.60$. In particular $\lambda>.844$, and $-2H^2\log(1-1.30/H^2)<2.72$. In the [nodal cut proof](effective-small-area.md#real-transfer-operator), a cut after $l\le H-1$ vertices bounds the second positive eigenvalue of $T_\beta$ by $2\cos(\pi/H)\le2-8/H^2$. A cut after $l>H-1$ gives $\lambda_2\le\lambda e^{-(1-1/H)/H^2}$. Each gives the asserted gap. The [lattice uncertainty and reduced-resolvent bounds](harmonic-small-area.md#real-and-complex-estimates-near-the-saddle) give edge variance at least $H^2/(4\cdot2.60)-1/2$, and $p''$ is at least twice its square. This proves (2).

Write $z=\beta(1+w)$. On $|w|\le.08$ the resolvent circle of radius $.30/H^2$ around $\lambda$ has $M=\|(I-K_\beta)(u-K_\beta)^{-1}\|\le2+2.60/.30$. The same form perturbation bound as in the harmonic proof applies here since $|w|<1/2$. It gives $\|\Pi_z\|\le(1-.08M)^{-1}<7$ and $H^2|p(z)-p(\beta)|<.37$, the latter by taking the logarithm inside the spectral circle. Cauchy's estimates give
$$p''(\beta)<116H^4,\qquad |p'''(z)|<4600H^7\quad(|w|\le.001).$$

For the principal amplitude $c(\beta)=e_0\Pi_\beta W_\delta(\beta)$ we have $c(\beta)>.05/H$. Indeed the real ground-state potential at $j>12H$ is greater than $9/H^2$ by $1-e^{-v}\ge v-v^2/2$ applied at $(12H-1)/(2H^3)$. Its mean is at most $2-\rho$. Each parity has squared mass at least $1/2-2.60/9$ below or at $12H$. Its coordinate sum there is at least $(1/2-2.60/9)\sqrt{H/3.23}$ since $\max u_j^2\le2\sqrt{2-\rho}$. In $c(\beta)$ multiply this sum by at least $2u_0(\rho/2)^\delta e^{-3/H^2}$ and use $u_0^2\ge H^{-3}/8$ from the boundary equation. The two usual [boundary blocks](effective-small-area.md#complex-tilts-near-the-saddle) of $L_0=\lceil H^2\rceil$ pairs have norm product at most $10/H$. Peeling them around the projection shows
$$ |c(z)/c(\beta)|\le 1400 e^{2(2.72+.37)L_0/H^2}<1.1\cdot10^6,\qquad
 \beta |c'(z)/c(\beta)|<1.6\cdot10^7\quad (|w|\le.001),$$
where the first estimate holds on the entire disk of radius $.08$.

## Inversion with a uniform number of blocks

Put $N=n/H^2$, $y=\theta/\beta$, $y_0=1.5\cdot10^{-6}$, $Y=10^4$. Suppose $N\ge10^{21}$. Define $\Psi=F_n(\beta+i\theta)/(c(\beta)\lambda^n)$ as in the [earlier inversion](harmonic-small-area.md#inversion-for-hge20). At $|y|\le y_0$ the part complementary to the principal projection is bounded by $e^{20-.4N}$. In detail the projection displacement is at most $y_0M/(1-y_0M)<2\cdot10^{-5}$. For a unit vector in its kernel compare $\|K_zv\|^2$ with the real polynomial $K_\beta^2+3y_0(I-K_\beta)$. On $[0,\lambda-.60/H^2]$ the polynomial is bounded above by $\lambda^2-.96/H^2$ by its endpoint values, and at $\lambda$ it is at most $\lambda^2+3y_0(2.60)/H^2$. The real top overlap is below $2\cdot10^{-5}$, so the restricted norm is at most $\lambda e^{-.4/H^2}$. Removing the two boundary blocks costs less than $e^{20}$ in the normalized remainder.

For $|y|\le Y$ the full transform satisfies
$$|\Psi|\le e^{20}\exp[-N\min(1.4\cdot10^{-7}y^2,3\cdot10^{-8})]. \tag{3}$$
All frequency bounds here are restricted to the lattice period. On the middle $b=n-2L_0$ pairs, (1) gives a loss at least $.023n\theta^2$ in the exponent, using $q/(1+q)^2>.24$, $1-\cos\theta\ge2\theta^2/\pi^2$ and $b-1>.99n$. This proves (3) if $H\le20$, and also if $20\le H\le400$ and $|y|\ge200$. In the latter case $.023 y^2/H^4>3\cdot10^{-8}$.

For $H\ge20$ take $l=\lfloor H^2/10\rfloor\ge .0975H^2$. The [paired-label block estimate](linear-potential.md#a-shorter-block-for-intermediate-frequencies) applies whenever $l|\theta|\le\pi$. At $200\le|y|\le400$ this condition holds for all $H\ge20$. For $H\ge400$ it holds through $Y$. Over these ranges the modulus norm of one $l$-pair block, divided by $\lambda^l$, is at most $e^{.272}(1+\exp(-(.0975)^3\,200^2/16))/2<.8$. For smaller $|y|$ the [integer-multiple comparison](harmonic-small-area.md#comparing-two-frequencies) gives relative norm at most $1-.2 y^2/(200+|y|)^2$. Taking at least $9N$ blocks proves (3) on the remaining frequencies. Beyond $Y$, the full middle portion of $2n-4L_0\ge1.99n$ steps gives $|\Psi|\le e^{20-N|y|^{2/3}/80}$, since $(1.99/75-1/80)Y^{2/3}>2.72$ in the paired-label bound.

At an integer saddle $k=-np'(\beta)$, set $\sigma^2=np''(\beta)$, $d=\beta\sigma$, $x=\sigma\theta=dy$. Then $\sqrt{.0084N}<d<\sqrt{116N}$. The centered principal exponent is $-x^2/2$ up to $4600N|y|^3/6$ on $|y|\le y_0$. On $|x|\le6$ this error is below $.007$, and the relative amplitude differs from one by at most $1.6\cdot10^7(6/d)<.034$. The real centered principal term therefore exceeds $.95e^{-x^2/2}$. For $|x|>6$ and $|y|\le y_0$ its modulus is at most $25 e^{-.36x^2}$ by the same two estimates. Its integral with weight $1+x^2$ is below $.01$ over those tails, using $x^2\ge36+12(|x|-6)$.

The low-frequency remainder and the range $y_0\le |y|\le Y$ in (3) together cost less than
$$2e^{20}(1+Y\sqrt{116N})^3(e^{-.4N}+e^{-1.4\cdot10^{-7} y_0^2 N})<.01.$$
The smaller exponent is $315$ at the lower endpoint and grows linearly. Beyond $Y$ extract $e^{-NY^{2/3}/160}$ and integrate the remaining tail as in the earlier inversion. It too costs less than $.01$. Thus the integrals of the real centered transform, both unweighted and with the factor $4\sigma^2\sin^2(x/(2\sigma))$, exceed one. On $[-6,6]$ this factor is at least $.99x^2$, and outside it is at most $x^2$. The integral of $|x\Psi|$ is less than ten. Fourier inversion gives a strictly negative tilted centered second difference and a relative change in the adjacent tilted mass of at most $10/\sigma<\beta/4$. As $0<\beta\le1/64$, undoing the tilt gives both strict growth and strict log-concavity at $k$.

## From the saddle to integer coranks

For $k\ge9n$ the saddle has $H>4$. By convexity and $p(0)=0$, it suffices to show $-64p(1/64)<9$. At $H=4$ the 12-vertex sine trial above gives $\rho/2\ge(1-10/(2\cdot13^2))(1-5/128)>e^{-9/128}$, using $\pi^2<10$ and $e^v\ge1+v+v^2/2$. Existence of the saddle follows from the continuous real slope range. When $H\ge20$, the [secant bound](harmonic-small-area.md#real-and-complex-estimates-near-the-saddle) gives $H<3k/n$. At $4<H<20$ the same inequality follows from $k/n\ge9$. Therefore $k\le10^{-11}n^{3/2}$ implies $N>10^{21}$. This proves both signs throughout the indicated range. The [linear tail theorem](finite-tail.md) gives the claimed strict growth below $9n$.

For $n\ge10^{61}$ and $9n\le k\le10^{-5}n^{3/2}$, if $H<10^{20}$ we already have $N>10^{21}$. For $H\ge10^{20}$ the [linear-potential derivative bound](linear-potential.md#analytic-estimates-for-the-eigenvalue-and-amplitude) gives $H<k/n$, so $N>10^{10}$. The sharper inversion in that result gives both signs. This proves the second bound.
