# An effective small-area window on the peak scale

For word length $m=2n+\delta$, $\delta\in\{0,1\}$, let $b_k$ count the surviving walks of corank $k$. Put
$$c_*=\exp(-10^{311}).$$

**Theorem.** For $2n\le k\le c_* n^{3/2}$ one has $b_{k+1}>b_k$ and $b_k^2>b_{k-1}b_{k+1}$. Together with the [linear tail bound](finite-tail.md), this gives strict growth through $\lfloor c_*n^{3/2}\rfloor$ for both families at every $n\ge100$.

The size of the constant comes from a deliberately coarse estimate for a bridge constrained to a tube. The advantage of the bound is its exponent and its uniformity in $n$. In computations at the sizes checked in this repository the linear tail bound is much stronger.

## Real transfer operator

For $0<\beta\le1$ write $H=\beta^{-1/3}$. On the nonnegative heights take the symmetric nearest-neighbor matrix $T=T_\beta$ with edge $(h,h+1)$ of weight $t_h=e^{-\beta h/2}$. Use $T_z$ for the complex parameter. Let $K_z=(T_z/2)^2$ on even heights, $K=K_\beta$, and set
$$v_z(h)=e^{-z\lfloor h/2\rfloor/2},\qquad W_\delta(z)=((T_z/2)^\delta v_z)_{\rm even}.$$
The edge action $h/2$ is the average of $\lfloor h/2\rfloor$ and $\lfloor(h+1)/2\rfloor$. Thus
$$F(z)=2^{-m}\sum_k b_ke^{-zk}=e_0 K_z^n W_\delta(z).$$
Let $\rho$ be the top eigenvalue of $T$, $u$ its positive unit eigenvector, $\lambda=\rho^2/4$ and $p(\beta)=\log\lambda$. The restricted matrix $K$ is positive semidefinite with simple top eigenvalue $\lambda$. Its unit top eigenvector is $u_e=\sqrt2\,u|_{\rm even}$, by bipartiteness. These operators are compact for $\Re z>0$. Simplicity follows from positivity and the three-term recurrence with its left boundary condition.

We will use the following bounds, all with absolute constants:
$$\begin{aligned}
 1/4\le\lambda<1,\qquad &1-\lambda\le12/H^2,\qquad
 \lambda-\lambda_2(K)\ge G/H^2,\quad G=10^{-4},\\
 -p'(\beta)&\ge10^{-30}H,\qquad p''(\beta)\ge10^{-60}H^4. \tag{1}
\end{aligned}$$

For the energy estimate, use the first sine eigenvector of the path on vertices $0,\ldots,\lfloor H\rfloor$. Its Rayleigh quotient is at least $2e^{-1/(2H^2)}\cos(\pi/(\lfloor H\rfloor+2))$. Hence $2-\rho\le12/H^2$ and $1-\lambda\le2-\rho$. The three-vertex test gives $\rho^2\ge1+e^{-\beta}$. The bound $\rho<2$ follows from the strict Dirichlet energy of every nonzero vector on the half-line.

To bound the second positive eigenvalue $\nu$ of $T$, cut a corresponding eigenvector at its first sign change, between $l-1$ and $l$. If there is a zero, cut just before the zero. Both restrictions are nonzero and their Rayleigh quotients are at least $\nu$ because the omitted cross term has nonpositive sign in each restricted eigenvalue equation. On the first $l$ vertices the top eigenvalue is at most $2\cos(\pi/(l+1))$. The operator on the tail is a translated copy of $e^{-\beta l/2}T$. For $H\ge100$ and $l<H/10$, the first bound is at most $2-4/(l+1)^2\le2-100/H^2$. For $l\ge H/10$ the second bound is at most $\rho-1/(40H^2)$. For $1\le H<100$ the tail estimate with $l\ge1$ gives $\rho-\nu\ge\beta/4\ge1/(400H^2)$. Squaring and dividing by four proves the gap in (1), since the nonzero eigenvalues of $K$ are the squares of the positive eigenvalues of $T/2$.

We give the curvature bound in detail. The weights $w_h=2t_h u_hu_{h+1}/\rho$ are a probability law on edges. Under this law a uniformly selected endpoint has vertex law $u_h^2$. Differentiating the eigenvalue gives $-p'=\mathbb E_w h$. Put $v(h)=(h-\sum_j j u_j^2)u_h$, perpendicular to $u$. All polynomially weighted vectors here are square summable by the eigenvalue equation and exponential decay of the edge weights. Then
$$\langle v,T' u\rangle=-\tfrac{\rho}{2}\operatorname{Var}_w h,\qquad
 \langle v,(\rho-T)v\rangle=\rho/2.$$
The first identity averages the midpoint $h+1/2$ against $h$. The second uses the ground-state identity $\langle fu,(\rho-T)fu\rangle=\sum_h t_hu_hu_{h+1}(f(h+1)-f(h))^2$. Differentiating a second time with the reduced inverse $(\rho-T)^{-1}$ on $u^\perp$ gives
$$(\log\rho)''\ge \tfrac14\operatorname{Var}_w h+
  \frac{2|\langle v,T'u\rangle|^2}{\rho\langle v,(\rho-T)v\rangle}
 =\tfrac14\operatorname{Var}_w h+(\operatorname{Var}_w h)^2.$$
Indeed the inverse term in $\rho''$ is twice the inverse quadratic form of the perpendicular part of $T'u$, which bounds the displayed test-vector quotient by Cauchy–Schwarz.

Extending $u$ by $u_{-1}=0$, we have $\sum_{h\ge-1}(u_{h+1}-u_h)^2\le2-\rho$. Telescoping squares gives $\max u_h^2\le2\sqrt{2-\rho}\le7/H$, so $\max w_h\le14/H$. For $H\ge1000$ any interval of length $H/50$ has edge mass below $.3$. This gives $\operatorname{Var}_w h\ge10^{-5}H^2$ and $\mathbb E_w h\ge H/100$. For smaller $H$ drop vertex zero and apply the tail norm bound to $u|_{h\ge1}$. Since $u_1=\rho u_0$,
$$1-2u_0^2\le e^{-\beta/2}(1-u_0^2),\qquad u_0^2\ge\beta/8.$$
The boundary equations give $w_0=2u_0^2$ and $w_1=2(\rho^2-1)u_0^2$. Thus $\mathbb E_w h\ge w_1$, $\operatorname{Var}_w h\ge w_0w_1$, and (1) follows also on $1\le H<1000$.

## Complex tilts near the saddle

Put $A=I-K$ and $\eta=10^{-12}$. For $|z-\beta|\le\eta\beta$ the entrywise path formula gives
$$\|A^{-1/2}(K_z-K)A^{-1/2}\|\le2|z-\beta|/\beta.$$
In fact $|e^{-z d}-e^{-\beta d}|\le 2(|z-\beta|/\beta)(1-e^{-\beta d})$ for each two-step action $d\ge0$. Summing by row bounds the absolute row difference by $2(|z-\beta|/\beta)(1-\sum_jK_{ij})$. Symmetry, weighted Cauchy–Schwarz in the pair of indices, and the Dirichlet-form bound $\langle x,Ax\rangle\ge\sum_i(1-\sum_jK_{ij})|x_i|^2$ give the claim.

Take the circle about $\lambda$ of radius $r=G/(4H^2)$. There $\|A(w-K)^{-1}\|\le 2+(1-\lambda)/r<5\cdot10^5=:M_0$. The Neumann expansion for the factored resolvent gives an analytic rank-one projection $\Pi_z$ and a simple eigenvalue $\lambda_z$ inside the circle. Indeed $\|(w-K)^{-1}A^{1/2}\|^2\le M_0/r$ and integrating the resolvent difference gives $\|\Pi_z-\Pi_\beta\|\le 2\eta M_0/(1-2\eta M_0)<10^{-5}$. For $p(z)=\log\lambda_z$ with the real branch, $|p(z)-p(\beta)|\le 8r\le H^{-2}$. Cauchy's estimates on the half disk imply
$$p''(\beta)\le10^{25}H^4,\qquad |p'''(z)|\le10^{38}H^7.\tag{2}$$

On the complementary invariant space the powers contract uniformly. Write $K_z-K=A^{1/2}E A^{1/2}$ with $\|E\|\le2\eta$. Since $K$ commutes with $A$ and both are contractions,
$$\|K_z x\|^2\le\langle x,(K^2+5\eta(I-K))x\rangle.$$
On $[0,\lambda-g]$, $g=G/H^2$, the convex function $t^2+5\eta(1-t)$ is at most $\lambda^2-.45g$ by checking the endpoints and using (1). At $\lambda$ it is at most $\lambda^2+10^{-6}g$. A unit vector in $\ker\Pi_z$ has overlap at most $10^{-5}$ with $u_e$. Hence $\|K_z|_{\ker\Pi_z}\|\le\lambda e^{-10^{-5}/H^2}$.

Write $l=\lceil H^2\rceil$, $N=n/H^2$ and assume $N\ge100$. For every $\Re z\ge\beta/2$ we have the two boundary bounds
$$\|e_0 K_z^l\|_2\le H^{-3/2},\qquad \|K_z^l W_\delta(z)\|_2\le10\sqrt H.$$
For the first, dominate by unweighted surviving walks. Their squared row norm is the unweighted return probability after $4l$ steps, $4^{-2l}\binom{4l}{2l}/(2l+1)\le H^{-3}$. For the second, from height $i$ the probability of a drop to $i/2$ or below is at most $\exp(-i^2/(40H^2))$ by the fair-walk exponential maximal inequality in $2l+\delta\le5H^2$ steps. All other paths have total real weight at most $4e^{-i/(4H)}$, by the edge action and $2l\ge2H^2$. Summing squares over even $i$ gives the stated bound (one can cap each contribution at one).

The amplitude $c(z)=e_0\Pi_z W_\delta(z)$ satisfies
$$c(\beta)\ge10^{-8}/H,\qquad |c(z)|\le e^{210}/H.$$
For the lower bound at $H\ge1000$ take $I=[.001H,1000H]$. For $i\ge1000H$ the potential $2-t_i-t_{i-1}$ is at least $200/H^2$, and its mean under $u_i^2$ is at most $2-\rho$ by the Dirichlet form. At $i<.001H$ use $\max u_i^2\le7/H$. Thus each parity has at least $.4$ mass on $I$ and $\sum_{i\in I,\ i\equiv\delta\bmod2}u_i\ge .4\sqrt{H/7}$. On $I$ the terminal vector exceeds $.9$. For $\delta=1$ move $T/2$ onto the eigenvector, introducing $\rho/2\ge1/2$ and switching parity. The lower bound follows from $u_0^2\ge H^{-3}/8$. For $H<1000$ just the initial coordinate gives $c(\beta)\ge u_0^2\ge 1/(8\cdot10^6 H)$. For the upper bound insert $K_z^l$ on both sides of $\Pi_z$ and divide by $\lambda_z^{2l}$. The boundary estimates apply and $|\lambda_z|^{-2l}\le e^{196}$ by $-\log\lambda\le48/H^2$. On the half disk also $|c'(z)|\le 2e^{210}/(\eta\beta H)$ by Cauchy's estimate.

Peeling these same blocks before applying the complementary power bound gives, for $|z-\beta|\le\eta\beta$,
$$\left|\frac{F(z)-c(z)e^{np(z)}}{c(\beta)\lambda^n}\right|
 \le e^{240}e^{-10^{-5}N}.\tag{3}$$

## Frequencies outside the saddle

Write $\theta=\Im z$, $y=H^3\theta$, $y_0=10^{-130}$ and $Y=10^{10}$. For $y_0\le |y|\le Y$ within $|\theta|\le\pi$ we claim
$$\frac{|F(\beta+i\theta)|}{c(\beta)\lambda^n}
 \le e^{240}\exp(-N e^{-10^{305}}).\tag{4}$$

First let $H\ge H_*=10^{400}$. For $i,j$ even in $I=[.001H,1000H]$ we compare two sets of bridges in the block of $2l$ steps. In rescaled time $[0,1]$ and heights divided by $H$, take the linear path from $i/H$ to $j/H$. For the second path add a piecewise linear tent, zero at the two ends and of height $2\pi H^2/(l|y|)$ at time $1/2$. Both curves have slopes of magnitude below $10^{132}$. For any step word, its block action in the symmetric transfer matrix is one half the trapezoidal sum of its heights minus $2l/4$, since $\min(a,b)=(a+b-1)/2$ across an edge. The deterministic centers of the phases for these two curves differ by $\pi$ in absolute value. The tent apex is on the time grid. In tubes of radius $wH$, $w=10^{-13}$, the phase errors are at most $|\theta|l wH\le2Yw$.

Here is an elementary lower bound on each tube probability, with the final vertex prescribed. Split $l$ pairs of steps as evenly as possible into $J=10^{300}$ groups. Each duration $t$ lies between $H^2/J$ and $4H^2/J$. At interior cuts allow even heights within $H/(100\sqrt J)$ of the curve, giving at least $H/(200\sqrt J)$ choices. Every consecutive prescribed displacement has magnitude below $\sqrt t$, since the curve moves at most $2\cdot 10^{132}H/J$ during a group. An even fair walk of $t$ steps has mass at least $1/(100\sqrt t)$ at each even displacement $|d|\le\sqrt t$, and mass at most $2e^{-d^2/(4t)}/\sqrt t$ at any even displacement. For the upper bound multiply the central binomial bound by the ratios $(t/2-a+1)/(t/2+a)$ for $1\le a\le|d|/2$, using $\log(1-x)\le-x$. For the lower bound in this range, the same ratios and $\log(1-x)\ge-2x$ for $x\le1/2$ suffice with the central mass at least $1/(2\sqrt t)$ and $t\ge100$.

Exclude paths reaching absolute displacement $\lfloor wH/2\rfloor$ from the starting vertex during a group. Reflection at either boundary bounds the rejected endpoint mass by the sum of two binomial masses at distance at least $2\lfloor wH/2\rfloor-|d|$. Since $wH/\sqrt t\ge w\sqrt J/2$, this sum is less than $1/(200\sqrt t)$. The retained paths lie in the desired tube and stay positive. Multiplication over groups and summation over cut heights give probability at least $10^{-6J}/H$. The tilt on each path is at least $\exp(-2(1001+2\pi/y_0))$. Thus each of the two almost opposite phase arcs carries real transfer mass at least $\exp(-10^{302})/H$. Pair equal amounts from the arcs. The modulus lost relative to the real entry is at least $\exp(-10^{303})/H$.

The matrix $|K_{\beta+i\theta}^l|$ of entrywise moduli is symmetric, is dominated by $K^l$ and has the preceding deficit throughout $I\times I$ on even heights. To bound its norm it suffices to test nonnegative unit vectors $x$. If $\|x-u_e\|\ge.001$, the real Rayleigh quotient loses at least $(1-\langle x,u_e\rangle^2)(1-e^{-G})\lambda^l$, since $\lambda_2(K)^l\le e^{-G}\lambda^l$. Otherwise $\sum_{i\in I}x_i\ge .05\sqrt H$ on even heights by the mass bound for $u$ and Cauchy–Schwarz. The entrywise deficit now gives
$$\|K_{\beta+i\theta}^l\|\le\lambda^l(1-e^{-10^{304}}).$$

For $1\le H<H_*$ a two-step block suffices. In the diagonal entry of $K_{\beta+i\theta}$ at height two the two weights, of moduli $e^{-\beta}/4$ and $e^{-2\beta}/4$, differ in phase by $\theta$. The deficit is at least $.01\sin^2(\theta/2)$, by squaring their sum in modulus. Also $u_e(2)\ge .1 H^{-3/2}$ by the boundary equations above. A nonnegative unit vector at distance at least $.05H^{-3/2}$ from $u_e$ loses at least $10^{-7}H^{-5}$ in the real Rayleigh quotient by (1). Every closer vector pays the diagonal deficit times at least $.05^2 H^{-3}$. Hence the norm is at most $\lambda-10^{-7}H^{-5}\sin^2(\theta/2)$. For $|\theta|\ge y_0 H^{-3}$ this loss exceeds $e^{-10^{304}}$ throughout $[1,H_*)$.

For either argument, peel off the two boundary factors of length $2l$ first. Use the contracting bound on each full remaining block, and $\|K_{\beta+i\theta}^r\|\le\lambda^r$ on the remainder by entrywise domination. At least $N/2-4$ blocks of $2l$ steps fit in the middle, or more when using pairs. The two boundary norms, $\lambda^{-2l}\le e^{192}$ and $c(\beta)\ge10^{-8}/H$ give (4).

For $Y\le|y|\le\pi H^3$ we use
$$\frac{|F(\beta+i\theta)|}{c(\beta)\lambda^n}
 \le e^{240}\exp(-N|y|^{2/3}/20000).\tag{5}$$
Indeed on any even block, from a given start and up to a phase depending on the endpoint, the phase of the area equals the phase of the sum of down-step labels with sign reversed. This holds also for unrestricted heights, by summing prefix down counts. In the [paired-label estimate](effective-middle.md#restoring-the-wall-without-losing-a-lattice-difference), keep the real edge weights on surviving paths and give killed paths weight zero. If their total retained mass from one start is $v$, the unrestricted row estimate $\rho_0$ yields the bound $\min(v,\rho_0+1-v)$ on the absolute row sum. All weights retained from the unrestricted fair law lie in $[0,1]$. The pair spacing $\lceil2|\theta|^{-2/3}\rceil$ for $0<|\theta|\le1$, or one for $1<|\theta|\le\pi$, gives contraction $e^{-1/200}$ per complete paired block as in that estimate. Submultiplication gives absolute row sum at most $3\exp(-t|\theta|^{2/3}/4000)$ in $t$ even steps. Symmetry gives the same operator-norm bound. Use this in the middle $t=2n-4l\ge n$ steps after the two boundary cuts. Division by $\lambda^n$ costs at most $e^{48N}$, absorbed into the stated exponential since $Y^{2/3}/5000>48$.

## Sign of the adjacent differences

Let $k=-np'(\beta)$ and $N=n/H^2\ge N_*=\exp(10^{310})$. Put $\sigma^2=np''(\beta)$, $d=\beta\sigma$, so that $10^{-30}\sqrt N\le d\le10^{13}\sqrt N$. Normalize the transform by $c(\beta)\lambda^n$ and denote it by $\Psi(\theta)$. The following three inversion bounds suffice:
$$
\int_{-\pi}^{\pi}\Re(e^{ik\theta}\Psi(\theta))\,d\theta>1/\sigma,\quad
\int_{-\pi}^{\pi}|\theta\Psi(\theta)|\,d\theta<e^{250}/\sigma^2,\quad
\int_{-\pi}^{\pi}4\sin^2(\theta/2)\Re(e^{ik\theta}\Psi(\theta))\,d\theta>1/\sigma^3.
$$

For details scale $x=\sigma\theta=d y$. In $|y|\le y_0$, the main term of (3) after canceling the linear phase has exponent $-x^2/2$ with error at most $10^{38}N|y|^3$. By (1) and $y_0=10^{-130}$ the real part of the exponent is at most $-x^2/4$ throughout. In $|x|\le50$ the error is bounded by $10^{38}50^3\,10^{90}/\sqrt N<10^{-4}$, and the amplitude ratio differs from one by at most $10^{115}|y|<10^{-4}$. The real main term there is at least $.99e^{-x^2/2}$. For the third integral the scaled multiplier is $4\sigma^2\sin^2(x/(2\sigma))$, between $.99x^2$ and $x^2$ there because $\sigma\ge d$. The integrals of $e^{-x^2/2}$ and $x^2 e^{-x^2/2}$ over $[-50,50]$ both exceed two.

For $|x|>50$ still in the small neighborhood, the main term is at most $e^{235}e^{-x^2/4}$ in modulus. Its integral with weight $1+x^2$ there is below $.01$. The low-frequency remainder (3) contributes at most $2e^{240}(1+dY)^3 e^{-10^{-5}N}$ with the same weight. The intermediate region contributes at most $2e^{240}(1+dY)^3\exp(-Ne^{-10^{305}})$ by (4). Both are below $.01$ for $N\ge N_*$. For (5) the weighted integral is bounded by $2e^{240}(1+d)^3\int_Y^\infty(1+y^2)e^{-N y^{2/3}/20000}\,dy<.01$. For example, extract $e^{-N Y^{2/3}/40000}$ and integrate the remaining exponential with $N$ replaced by $40000$. These estimates prove the first and third inversion bounds. For the absolute first difference integrate the majorant $e^{235}|x|e^{-x^2/4}$ over the entire low neighborhood and use the same remainder estimates.

Fourier inversion now gives the tilted mass at $k$ a relative change of at most $e^{250}/\sigma\le\beta/4$ at $k+1$. Undoing the tilt gives $b_{k+1}/b_k\ge e^\beta(1-\beta/4)>1$. The third integral is the negative centered second difference of the tilted mass up to a positive factor, so that mass is strictly log-concave at $k$. The same holds for $b_k$ upon undoing the tilt.

Finally $p$ is strictly convex and $-p'(\beta)$ tends to infinity at zero by (1). At one, convexity gives $-p'(1)\le p(0)-p(1)\le\log4$, using $p(0)=0$ by the energy estimate and $\lambda(1)\ge1/4$. Thus $k/n\ge2$ gives a saddle with $0<\beta<1$. By (1), $H\le10^{30}k/n$, so $k\le c_* n^{3/2}$ implies $N\ge 10^{-60}/c_*^2>N_*$. This proves the theorem.
