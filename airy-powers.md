# Transfer powers and an interval of strict corank growth

Write $b_k=a_{D-k}$ for either staircase, with $m=2n$ or $2n+1$. For **every $n\ge10^{19}$ and every integer $0\le k\le m^{3/2}/100$**, we have $b_{k+1}>b_k$. The new large-height estimate gives this sign at any integer saddle $k=-np'(\beta)$ with $H=\beta^{-1/3}\ge10000$ and $N=n/H^2\ge1450$. Both assertions concern individual coefficients.

Use the [two-step transfer](effective-small-area.md#real-transfer-operator) $K_z$, $\lambda=e^{p(\beta)}$, $d=1/H$, $y=\Im z/\beta$, and the [Dirichlet Airy energy estimate](airy-grid.md), with ground energy $1.65\le a<2.60$. The [rational verifier](verify_airy_powers.py) checks the scalar bounds below.

## A power bound outside the perturbation disk

Put $t=1+iy$, $A=K_{t\beta}/\lambda$. We claim
$$
 \|A^j\|\le
 \begin{cases}
  2e^{-.173j d^2 y^2},&.08\le |y|\le.2,\\
  4e^{-.12j d^2 y^2},&.2\le |y|\le1.
 \end{cases} \tag{1}
$$
Let $U$ be the diagonal unitary with entry $\exp(-\mathrm i\theta j/4)$ at height $j$, where $\theta=\beta y$. The single-step matrix is $T_{t\beta}=e^{\mathrm i\theta/4} U T_\beta U$. Let $u_e$ be the real positive unit top vector of $K_\beta$, $g=U^*u_e$. Bounding the second half-step by its norm $\sqrt\lambda$ and using the real spectral gap in the first half gives
$$
 \|Aw\|^2\le \|w\|^2-1.48d^2(\|w\|^2-|\langle g,w\rangle|^2).
 \tag{2}
$$
Indeed the squared norm of the first half is the quadratic form of $K_\beta$ at $Uw$, and $1-\lambda_2/\lambda\ge1.48d^2$. The adjoint has the same bound with $\bar g$.

Take the conjugate of the normalized even-grid sample of $f(x)=C\operatorname{Ai}(t^{1/3}x-a)$, $x=(j+1)d$, with $\|f\|_2=1$. This unit vector $v$ satisfies
$$ \|A^*v-\bar\nu v\|\le\Delta d^2,\quad
 \nu=\exp[-at^{2/3}d^2+3td^3/2]/\lambda,\quad \Delta=400d^2. \tag{3}$$
For details use the [one-step grid operator $B$](airy-grid.md#sampling-the-half-line-eigenfunction), with $V=tx,E=at^{2/3}$. Here $|t|<1.42, |E|<3.3,\Re t=1$. Through degree two its expansion on $f$ equals $(1-Ed^2/2)f$. In units $d^4$ the residual against $e^{-Ed^2/2}$ is bounded by
$$ \|f^{(4)}\|/6+\|V^2f\|_d/8+\|V f''\|_d/4+.36\|f'\|+.2d^2\|f\|_d+|E|^2\|f\|_d/8.$$
The terms come from averaging the two Taylor shifts, expanding the potential, the antisymmetric shift, the hyperbolic cosine remainder, and the scalar exponential. The integral exponential remainders apply since both $V$ and $E$ have nonnegative real part. Use $f^{(4)}=2tf'+(V-E)^2 f$ and the weighted moment recursion in the grid proof. Multiply by $2e^{3d^3/4}/(\lambda\|f_{\rm even}\|_d)$ to square the transfer and normalize. This gives (3), using transpose symmetry and conjugation. The sampled vector is only an approximate eigenvector.

Write $L=-d^{-2}\log|\nu|$. From the real energy estimate,
$$ |L-a(\Re(t^{2/3})-1)|<.24d^2. $$
For the upper bound $\Re(t^{2/3})-1\le y^2/9$ by the second derivative. For $|y|\le.2$ it is at least $y^2/9-56y^4/(81\cdot24)$ by Taylor expansion. For $0\le y\le1$ its derivative is $(2/3)(1+y^2)^{-1/6}\sin(\arctan(y)/3)$. Use $(1+y^2)^{-1/6}>.89$, $\arctan y\ge\pi y/4$ and $\sin v\ge.98v$ for $v\le\pi/12$.

Apply (2) for the adjoint to (3). Since $\|A^*v\|\ge1-(L+\Delta)d^2$, this gives $1-|\langle\bar g,v\rangle|^2\le2(L+\Delta)/1.48$. Also $\|g-\bar g\|\le2d$. Indeed the mean height under $u_e^2$ is at most twice the full-ground mean $-p'(\beta)+1/2$ by the [edge law](harmonic-small-area.md#real-and-complex-estimates-near-the-saddle). Differentiating the real grid expansion by its Cauchy error gives $-p'(\beta)<1.8H$. Use $2(1-\cos(\theta j/2))\le |\theta|j$. Thus $\|(I-vv^*)g\|\le q_0=\sqrt{2(L+\Delta)/1.48}+2d$.

In the two bands take $B_0=2,4$ respectively and equip the space with $\|w\|_*=\max(\|w\|,B_0|\langle v,w\rangle|)$. On its unit ball $|\langle g,w\rangle|\le q_0+1/B_0$. By (2) the ordinary norm of $Aw$ is at most $1-.74[1-(q_0+1/B_0)^2]d^2$. By (3) its other seminorm is at most $e^{-Ld^2}+B_0\Delta d^2$. Both bounds are at most $1-\gamma y^2d^2$ for the respective $\gamma=.173,.12$, using the bounds on $L$ just derived. Iteration and $\|w\|\le\|w\|_*\le B_0\|w\|$ prove (1).

## Real boundary amplitude

Let $f$ now be the positive unit continuum ground state at $t=1$, and $I=\int_0^\infty f(x)\,dx$. For **either** terminal parity $\delta$ the principal amplitude satisfies
$$ .99 I/H < c_\delta(\beta) < 1.01 I/H\qquad(H\ge9000). \tag{4}$$
For the full (both-parity) single-step ground $u$, the [boundary identity](two-harmonics.md#a-boundary-identity-for-the-real-eigenvector) puts $u_0^2$ between $2(1-e^{-\beta/2})\lambda$ and $\beta$. The terminal parity gives the expression
$$ c_\delta=2u_0(\sqrt\lambda)^\delta\sum_{j\equiv\delta\ (2)} u_j\,e^{-\beta\lfloor j/2\rfloor/2}.$$
It remains to estimate this sum.

Give full-grid samples the ordinary sequence normalization by multiplying their values by $\sqrt d$. The corrected real sample $U=f+d^2F$ in the [Airy grid proof](airy-grid.md#sampling-the-half-line-eigenfunction) has norm $s_U\in[1-2d-4d^2,1+2d+4d^2]$ and single-step residual at most $201d^6$ before normalization. Its target $\zeta$ is within $600d^6$ of $\sqrt\lambda$ by the real two-step estimate. Every other spectral point of $T_\beta/2$ is at distance at least $.73d^2$ from $\zeta$, by $\sqrt\lambda-\sqrt{\lambda_2}\ge(\lambda-\lambda_2)/2$. The real spectral theorem bounds the distance of the normalized sample to $u$ by $400d^4$ (the perpendicular norm costs a factor at most $\sqrt2$). The sign is fixed by the nonnegative sample of $f$ and the correction of norm at most $4d^2$. In particular the difference of $u$ from the uncorrected sample divided by $s_U$ has norm at most $5d^2$.

The geometric terminal weights have norm at most $2d^{-3/2}$. Write $S_j$ for the displayed terminal sum for parity $j$. After multiplying by $2\sqrt d$ the cost of the preceding norm error is at most $20d$. For the leading sample take Riemann sums on cells of width $2d$, at their centers or right endpoints. The unweighted error relative to the integral in absolute units is at most $2d\|f'\|_1$. The terminal weight change costs at most $(d^2/4)(\|xf\|_1+2d\|(xf)'\|_1)$ since $1-e^{-\beta\lfloor j/2\rfloor/2}\le d^2x/4$. Weighted $L^2$ moments and Cauchy–Schwarz against $(1+x)^{-1}$ give the three $L^1$ bounds $11,21,53$. Also $I\ge1/\|f\|_\infty>1/2$ since $\|f\|_\infty^2\le2\|f'\|_2$. Including $s_U$ gives $.9903<2\sqrt d S_j/I<1.010$. The boundary identity, $\lambda\ge1-2.60d^2$ and the terminal parity factor give (4).

## Inverting at the integer saddle

Use the [shorter-walk decomposition](airy-grid.md#integrating-the-shorter-walk-at-the-saddle) with $b=\lceil200H^2\rceil$, $d_0=\beta\sqrt{(n-b)p''(\beta)}$, $x=d_0y$. Thus $.35(N-201)<d_0^2<.60N$. Write $J$ for the centered transform in units $c\lambda^n$, $S$ for the similarly centered shorter walk, and $P(w)=p(\beta(1+w))-p(\beta)-\beta p'(\beta)w$. For $|y|\le.08$,
$$ J=(S(iy)-R_b)e^{(n-b)P(iy)}+R_n,\qquad |R_i|\le e^{20-.16i/H^2}.$$
The real full-transform estimate gives $.999<S(0)<1.001$. At both real shifts $w=\pm.08$ the shifted height is at least 9000 and $b/H'^2>180$. Equation (4) gives $c(\beta(1+w))/c(\beta)<1.06$. By the [real boundary-block estimate](airy-grid.md#boundary-factors-in-fourier-inversion) the shorter transform at its own tilt is at most $1.001$ times its principal mass. Using $p''<.68H^4$ on the shifted segment gives $S(\pm.08)<1.65$. For the shorter walk's centered area $Z$ in tilt units, $S(iy)/S(0)=\mathbb E e^{-iyZ}$. The inequality $\cosh v\ge1+v^2/2$ gives $\mathbb E Z^2<205$.

At these heights the Cauchy cubic bound from the grid expansion is $|p'''|<H^7$ throughout $|w|\le.08$. The centered exponent differs from $-x^2/2$ by at most $|x|^3/(6\cdot .35d_0)$, so its real part is at most $-.46x^2$. The full-line Gaussian principal integral is at least $\sqrt{2\pi}\, .999(1-205/(2d_0^2))$ by averaging the exact translated Gaussian. Omission of the Gaussian past $u=.08d_0$ costs $2.002e^{-u^2/2}/u$. Replacing the Gaussian on the retained interval costs at most $1.001/(6\cdot.35d_0\cdot.46^2)$, by integrating $|x|^3 e^{-.46x^2}$. The adjacent-sign multiplier costs another $1.003/(.46d_0)$, bounding the integral of $1.001|y|$ times the principal modulus. Both complementary terms, also with this weight, cost less than $.001$.

Peel $\lceil20H^2\rceil$ pairs at either end for the remaining frequencies. Their product costs at most $1.01$ relative to the real ground components. Apply (1) in the middle. For each band $[l,r]=[.08,.2],[.2,1]$, including both frequency signs, the absolute integral with weight $1+1.001|y|$ is at most
$$1.01 B_0(1+1.001r)\sqrt{.60N}\,e^{-Cl^2}/(Cl),\qquad C=\gamma(N-42).$$
For $1\le |y|\le45$ use the [Hölder block](holder-blocks.md#a-block-inequality) and its integer-multiple comparison. The block has relative norm at most $.924$ throughout $[4.5,45]$, since $12\cdot45/H<\pi$. There are at least $N-42$ whole blocks after peeling. On $[1,1.125],[1.125,1.5],[1.5,4.5],[4.5,45]$ take an integer multiple in $[4.5,45]$, of order at most $5,4,3,1$ respectively. The resulting envelope is $1.01e^{-.076(N-42)/j^2}$ with the respective upper bound $j$. Beyond 45 the [full-block estimate](airy-grid.md#boundary-factors-in-fourier-inversion) gives $3e^{-N |y|^{2/3}/80}$, since the middle still has at least $1.94n$ single steps. The weighted tail costs less than $.001$ by extracting $e^{-N45^{2/3}/160}$.

At $N=1450$ the Gaussian lower bound exceeds all costs by more than $.20$ in the scaled integral. The Gaussian losses decrease with $N$, as do the outer bounds (each exponential dominates its prefactor from this endpoint). Since $\beta/(1-e^{-\beta})<1.001$, this gives $b_{k+1}>b_k$ by tilted inversion.

## Smaller heights and the uniform interval

For $n\ge10^{19}$ and $4\le H<110$ we also have strict growth at an integer saddle. Use the [flat contour](flat-pairs.md#estimates-down-to-height-scale-four) with $H^2|p(\beta(1+w))-p(\beta)|<.37$ on $|w|\le.08$, $.0084<p''/H^4<116$. Real coefficients in the Taylor expansion give, for $|y|\le y_0=.0003$,
$$ H^2\Re P(iy)\le-\tfrac12 (p''/H^4)y^2+
   \frac{.37 y^4}{.08^4(1-(y/.08)^2)}\le-.40(p''/H^4)y^2.$$
The complementary bound $e^{20-.4i/H^2}$ extends through $y_0$. Indeed the real projection displacement is below $.005$. On the perpendicular spectrum the polynomial $K_\beta^2+3y_0(I-K_\beta)$ lies below $\lambda^2-.95/H^2$ by its two endpoint values on $[0,\lambda-.60/H^2]$ (use $\lambda>.844$). At $\lambda$ its excess is at most $3y_0\cdot2.60/H^2$. Mixing the two estimates with top overlap below $.005$ gives squared norm $\le\lambda^2-.80/H^2$, as required.

Use the same short-transform decomposition, now with $b=\lceil400H^2\rceil$ and $d_0^2>.0084(N-401)$. At $w=\pm.04$ peel two boundary blocks using the original height $H$. Their norm product is at most $10/H$ for either shift, since $\Re z\ge\beta/2$. Division by $c>.05/H$ and the shifted energy $-H^2p(z)<3.09$ cost at most $200 e^{2\cdot3.09(1+1/16)}<e^{13}$. Removing the constant and linear Taylor terms costs at most $.37\,(.5)^2/(1-.5)$ per height-scale unit of the shorter length. Thus $S(\pm.04)<e^{88}$ and $|S(iy)-S(0)|<2300 |y|$, by integrating $\Pr(|Z|>v)\le\min(1,2 e^{88-.04v}/S(0))$; also $|S(0)-1|<.001$ from the real remainder.

The cubic bound $4600 H^7$ and real-part estimate above give an integrated error below $.23$ in replacing the exponent by the Gaussian, using $1.001\cdot4600/(6\cdot.0084d_0\cdot.40^2)$. Replacing $S(iy)$ by its mass costs below $.003$, by integration of $2300|x|e^{-.40x^2}/d_0$. Here $y_0d_0>10$, so the Gaussian tail, complementary terms and local adjacent multiplier together cost below $.01$ ($\beta/(1-e^{-\beta})<1.01$). From $y_0$ to $10^4$ use the [flat-pair envelope](flat-pairs.md#inversion-with-a-uniform-number-of-blocks) at $H\le20$, with loss at least $1.4\cdot10^{-7}Ny_0^2$. At $20\le H<110$ the [block at multiples in $[200,400]$](airy-overlap.md#positive-tilts-between-the-peak-and-the-saddle) gives loss $.00004Ny^2$ through $.2$ and $.0000017N$ above it to $10^4$, using flat pairs above 200. The prefactor is $e^{20}$ in both cases. The outer weighted costs are each below $.001$, including the usual stretched-exponential tail beyond $10^4$. The Gaussian mass exceeds two after subtraction. This proves the assertion at smaller heights.

Finally, for $k<9n$ use the [linear tail theorem](finite-tail.md). For $k\ge9n$ choose the saddle, which has $H>4$. For $110\le H<10000$ the [Airy grid saddle](airy-grid.md) applies since $N>10^{11}$. At $H\ge10000$, $k/n>(2a/3-.016)H\ge1.084H$ by the same grid estimate. Consequently $k\le .01m^{3/2}$ implies $N>1.084^2/(.01^2\cdot2.001^3)>1450$. This joins all integer steps in the claimed range.

~~~sh
python3 -B verify_airy_powers.py
~~~
