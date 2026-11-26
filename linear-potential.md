# Quantitative comparison with the linear potential

For both central staircases write $b_k=a_{D-k}$. At every $n\ge10^{100}$ the two inequalities
$$ b_{k+1}>b_k,\qquad b_k^2>b_{k-1}b_{k+1} \tag{1}$$
hold for every integer $n/105\le k\le 10^{-5} n^{3/2}$. We compare the real transfer energy to the continuum Dirichlet operator with potential $x$ and transfer the error to nearby complex parameters. This allows a saddle estimate after $10^{10}$ blocks on the natural height scale.

Use the notation of the [harmonic comparison](harmonic-small-area.md), with $\beta=H^{-3}$, $K_z=(T_z/2)^2$ on even heights, $\lambda=\rho^2/4$, $p=\log\lambda$, $N=n/H^2$ and $y=\theta/\beta$. Write $c(z)=e_0\Pi_zW_\delta(z)$ and $F_n(z)=e_0K_z^n W_\delta(z)$. In the auxiliary estimates the parity $\delta$ is held fixed when the number of pairs changes.

## Approximation of the real ground energy

Let $a$ be the infimum of $\int_0^\infty (|f'|^2+x|f|^2)\,dx$ over unit Dirichlet functions at zero. No numerical Airy zero is needed. The sine trial on $[0,3]$ gives $a\le\pi^2/9+3/2<2.60$. For $H\ge10^4$ we claim
$$|H^2p(H^{-3})+a|\le10/H. \tag{2}$$
Write $d=1/H$, $x_j=(j+1)d$, $t_j=e^{-j/(2H^3)}$ for $j\ge0$, $t_{-1}=1$, $w_{-1}=0$. The infimum $e_H=H^2(2-\rho)$ of the scaled discrete form on unit vectors has gradient weights $H^2t_j$ on edges and potential $V_j=H^2(2-t_{j-1}-t_j)$ at vertices. In particular $0\le V_j\le x_j$ and $V_j$ increases.

For an upper bound take $w_j=\sqrt H\int_{jd}^{(j+1)d} f(x)\,dx$ and extend $f$ by zero on the left. Write $D_h=H^2\sum_{j\ge-1}|w_{j+1}-w_j|^2$. Jensen's inequality for the cell averages and for $f(x+d)-f(x)$ gives $D_h\le\int|f'|^2$. The squared norm lost on replacing $f$ by its cell averages is at most $d^2\int |f'|^2$, by Cauchy–Schwarz within each cell. Also $\sum x_j|w_j|^2\le\int(x+d)|f|^2$. Taking a minimizing sequence yields $e_H\le(a+d)/(1-d^2a)$.

Conversely, interpolate linearly between $f(x_j)=\sqrt H\,w_j$, including $f(0)=0$. Then $\int |f'|^2=D_h$ and $\int |f|^2=\|w\|^2-D_h/(6H^2)$. By convexity of the square on each edge, $\int x|f|^2\le\sum x_j|w_j|^2$ because the linear hat function centered at $x_j$ has integral $d$ and first moment $dx_j$. Hence
$$a\|w\|^2\le (1+a/(6H^2))D_h+\sum x_j|w_j|^2.$$

Localize at $M=\sqrt H$. Set $\chi(x)=\cos u(x)$, $\zeta(x)=\sin u(x)$ where $u$ is zero up to $M$, increases linearly to $\pi/2$ at $2M$, and is constant thereafter. The sum of the energies of $\chi w$ and $\zeta w$ exceeds the energy of $w$ by at most $3\|w\|^2/M^2$. Indeed the edge error is $H^2t_j\Re(\overline w_jw_{j+1})$ times the squared distance between the two successive unit vectors $(\chi,\zeta)$, at most $(\pi d/(2M))^2$. On the support of $\zeta$ the potential exceeds $M/2$, by its explicit value at the first vertex at or above $M$. On the support of $\chi$ one has $V_j\ge x_j-4/H$ by $1-e^{-v}\ge v-v^2/2$ at $x_j\le2M$. Each incident edge has $t_j\ge1-2M/H^2$. The interpolation inequality therefore bounds the energy of $\chi w$ below by $(a-5/H)\|\chi w\|^2$, using $(1-2M/H^2)a/(1+a/(6H^2))\ge a-1/H$. Combining the two cutoffs gives $e_H\ge a-8/H$. Finally $-H^2p=-2H^2\log(1-e_H/(2H^2))$ differs from $e_H$ by less than $4/H^2$. This proves (2), and the [real upper bound on $\rho$](mode-bounds.md#upper-bound-for-a-single-small-corank) gives $a\ge1.65$ by taking the limit.

## Analytic estimates for the eigenvalue and amplitude

Assume $H\ge10^{20}$. On $|w|\le.04$ put
$$E(w)=H^2p(\beta(1+w))+a(1+w)^{2/3}.$$
Use the branches real at zero. Equation (2) at $H(1+w)^{-1/3}$ gives $|E(w)|\le11/H$ on the real diameter. On the full disk $|E|<1$, by (2) at zero and the [resolvent bound](harmonic-small-area.md#real-and-complex-estimates-near-the-saddle) $H^2|p(\beta(1+w))-p(\beta)|<.42$. The harmonic measure of the semicircular arc in either half disk of radius $r=.04$ is at most $4\arctan(|w|/r)/\pi$. Indeed $(r+w)/(r-w)$ maps the upper half disk to the first quadrant. Its argument times $2/\pi$ is that harmonic measure. Applying the maximum principle to $\log|E|$ gives $|E|\le(11/H)^{.68}$ on $|w|\le.01$ and $|E|\le(11/H)^{.40}$ on $|w|\le.02$.

Cauchy's estimates on the smaller disk, differentiating in $w$, now give
$$ -p'(\beta)>H,\qquad .35H^4<p''(\beta)<.60H^4,\qquad
 |p'''(\beta(1+w))|<H^7\quad(|w|\le.004). \tag{3}$$
For example the errors in the first two derivatives at zero are bounded by $100(11/H)^{.68}$ and $2\cdot10^4(11/H)^{.68}$. The third derivative error is at most $6(11/H)^{.68}/.006^3$. The leading derivatives in these units are those of $-a(1+w)^{2/3}$, with $1.65\le a<2.60$. Also for $|y|\le.02$,
$$ H^2\Re\big(p(\beta(1+iy))-p(\beta)\big)\le-.15y^2. \tag{4}$$
Through $|y|=.004$ use (3) and Taylor's formula. For $.004\le |y|\le.02$, $\Re(1+iy)^{2/3}\ge1+.109y^2$ by Taylor's formula through the quadratic term and the third derivative bound $|(8/27)(1+it)^{-7/3}|\le8/27$. The two errors from $E$ are at most $2(11/H)^{.40}<.01(.004)^2$.

For every $|w|\le.02$ the complementary invariant space of $K_z$, $z=\beta(1+w)$, has norm at most $\lambda e^{-.5/H^2}$. Here $\|\Pi_z-\Pi_\beta\|\le .02(12.25)/(1-.02(12.25))<.325$. As in the cited resolvent bound, $\|K_zv\|^2\le\langle v,(K^2+3|w|(I-K))v\rangle$. On $[0,\lambda-.9/H^2]$ the convex polynomial $t^2+.06(1-t)$ is at most $\lambda^2-1.49/H^2$ by its two endpoint values and $1-\lambda\le4.1/H^2$. At the top eigenvalue it is at most $\lambda^2+.246/H^2$. A unit vector in $\ker\Pi_z$ has overlap at most $.325$ with the real unit top vector, giving the asserted norm bound. Peeling the [two boundary blocks](harmonic-small-area.md#real-and-complex-estimates-near-the-saddle) of length $L=\lceil H^2\rceil$ yields, for any $b\ge 100H^2$ pairs,
$$ \left|\frac{F_b(z)-c(z)e^{bp(z)}}{c(\beta)\lambda^b}\right|
     \le e^{20-.5b/H^2}. \tag{5}$$
In fact the boundary norms have product at most $10/H$, $c(\beta)>.1/H$, $\lambda^{-2L}\le e^{8.4L/H^2}$ and $\|I-\Pi_z\|<3$.

To control the amplitude derivative, (5) can be applied at an auxiliary length. Fix $b=\lceil200H^2\rceil$ and write
$$S(w)=\frac{F_b(\beta(1+w))e^{-b\beta p'(\beta)w}}{c(\beta)\lambda^b}.$$
We have $S(0)<1.001$ by (5). At $w=\pm.04$ use the real boundary estimates at $H'=H(1+w)^{-1/3}$ to bound $F_b$ by $(10/H')\lambda(\beta(1+w))^{b-2\lceil(H')^2\rceil}$. The linear part of the exponent cancels. The real Taylor remainder in $b p$ is below $.13$ since $p''(\beta(1+t))<.65H^4$ there, by the same Cauchy argument as (3) at $H'$ (the numerical margins also hold at $H'\ge.98\cdot10^{20}$). This gives $S(\pm.04)<e^{14}$. Since $S$ is a positive Laplace transform on the real diameter, $\log S$ is convex there and $|S(w)|\le S(\Re w)$. It follows that $|S(w)|<4.1$ on $|w|\le.004$. The error in (5) after the extra exponential factor is still below $.001$ since $-\beta p'(\beta)\le4.2/H^2$ by the secant to zero. The complex Taylor remainder $b|p(z)-p(\beta)-\beta p'(\beta)w|$ is below $.002$ there by (3). Isolating the principal term and then applying Cauchy's estimate gives
$$
 |c(\beta(1+w))/c(\beta)|<5 \ (|w|\le.004),\qquad
 \beta |c'(\beta(1+w))/c(\beta)|\le2500 \ (|w|\le.002). \tag{6}
$$

## A shorter block for intermediate frequencies

For $H\ge10^{20}$ put $l=\lfloor H^2/10\rfloor$. A block of $2l$ fair steps with labels paired $l$ apart has unrestricted modulus row sum at most $\cos^{2l}(l\theta/4)\le e^{-l^3\theta^2/16}$ for $l|\theta|\le\pi$. This is the [paired-label calculation](peak-rate.md#fourier-inversion-for-lattice-differences). That condition holds throughout $|y|\le10^4$. Killing at the wall and retaining the real tilt gives a modulus row sum at most $(1+e^{-l^3\theta^2/16})/2$. By symmetry and $\lambda^l\ge e^{-4.2l/H^2}$, the norm of the entrywise moduli is at most $.85\lambda^l$ for $200\le|y|\le10^4$ (use $l\ge.0999H^2$). For $0<|y|\le200$, apply the [integer-multiple comparison](harmonic-small-area.md#comparing-two-frequencies) with the multiplier $\lceil200/|y|\rceil$. The block norm is then at most $\lambda^l(1-.15y^2/(200+|y|)^2)$.

For $N\ge 1000$ at least $9N$ of the shorter blocks fit between the two boundary blocks, and $2n-4L\ge1.99n$. Define $\Psi=F_n(\beta+i\theta)/(c(\beta)\lambda^n)$. The shorter blocks give
$$
|\Psi|\le e^{20}\begin{cases}
 \exp(-3\cdot10^{-5}Ny^2),& |y|\le1,\\
 \exp(-3\cdot10^{-5}N),&1\le |y|\le10^4 .
\end{cases} \tag{7}
$$
On $1\le |y|\le200$ use the monotonicity of $|y|/(200+|y|)$. We will also use the bound $e^{20}\exp(-8\cdot10^{-6}Ny^2)$ throughout $|y|\le200$, using $200+|y|\le400$. For $200\le |y|\le10^4$ the bound $e^{20}(.85)^{9N}$ is available. Beyond $10^4$ the [full-block bound](harmonic-small-area.md#inversion-for-hge20) gives $|\Psi|\le e^{20}e^{-N|y|^{2/3}/80}$ by its row estimate on the middle $2n-4L$ steps. All these bounds apply on the lattice Fourier interval.

## Signs at the saddle

Let $k=-np'(\beta)$, $N\ge10^{10}$ and $H\ge10^{20}$. Set $\sigma^2=np''(\beta)$, $x=\sigma\theta$ and $d_*=\beta\sigma$. Then $\sqrt{.35N}<d_*<\sqrt{.60N}$ and $x=d_*y$. After centering by $e^{ik\theta}$ the principal exponent is $-x^2/2$ up to $N|y|^3/6$ on $|y|\le.004$. On $|x|\le6$ this error is below $.002$, and the relative amplitude differs from one by at most $2500\cdot6/d_*<.254$. Thus the real centered principal term exceeds $.74 e^{-x^2/2}$ there.

For the signed inversion integrals use weight $1+x^2$ to bound all tails. The principal term on $|x|>6$ and $|y|\le.004$ has modulus at most $5e^{-.49x^2}$ by the same Taylor remainder and (6), giving a weighted integral below $.01$. Between $.004$ and $.02$ in $|y|$, (4) gives $4\cdot10^6 e^{-x^2/4}$ for the principal term, using the full-disk amplitude estimate in the harmonic proof. Here $|x|\ge.004\sqrt{.35N}>230$, so its weighted integral is below $.01$. On $|y|\le10^4$, the sum of the integrated low-frequency remainder in (5) and the tail from $.02\le|y|\le10^4$ in (7) is at most
$$2e^{20}(1+10^4\sqrt{.60N})^3
     (e^{-.5N}+e^{-3\cdot10^{-5}(.02)^2N})<.01.$$
At the lower threshold the smaller exponent is 120 and thereafter grows linearly. The integral above $10^4$ is below $.01$ by extracting $e^{-N(10^4)^{2/3}/160}$ from the last bound following (7) and integrating the remainder against $1+y^2$.

In the scaled variable the mass integral and the integral with multiplier $4\sigma^2\sin^2(x/(2\sigma))$ both exceed one. The latter multiplier lies between $.99x^2$ and $x^2$ on the central interval, and both central Gaussian integrals exceed two. The integral of $|x\Psi|$ is below ten, by the same errors and the central majorant $1.27 e^{-x^2/2}$. Inversion therefore gives a relative change at most $10/\sigma<\beta/4$ in tilted mass from $k$ to $k+1$, and a strictly negative tilted centered second difference. Removing the geometric tilt gives (1) as in the [harmonic inversion](harmonic-small-area.md#inversion-for-hge20).

For $n\ge10^{100}$ and $2n\le k\le10^{-5}n^{3/2}$, the real saddle is below one. If $H\ge10^{20}$, (3) gives $H<k/n$ and hence $N>10^{10}$. If $20\le H<10^{20}$ then $N\ge10^{60}$, so the earlier harmonic inversion applies directly. The bounded-height result there covers smaller $H$ and the interval $n/105\le k\le2n$. This proves the stated small-corank theorem.
