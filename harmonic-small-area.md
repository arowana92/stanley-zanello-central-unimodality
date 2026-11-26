# Small coranks via integer multiples of the Fourier frequency

Write $m=2n+\delta$, $\delta\in\{0,1\}$, and $b_k=a_{D-k}$ for either central staircase. For $n\ge10^{100}$ one has
$$ b_{k+1}>b_k,\qquad b_k^2>b_{k-1}b_{k+1}
       \qquad(2n\le k\le 3\cdot10^{-15}n^{3/2}). \tag{1}$$
The same strict inequalities hold between $n/105$ and $2n$ at these sizes. The two statements use integer $k$ in the indicated real intervals.

The argument tilts the coefficients so the selected corank lies near the mean. A Gaussian approximation there gives a negative second difference if the error from the other Fourier frequencies is small enough. Estimate (2) obtains that error from the cancellation of paired walk steps at a multiple of the original frequency. This controls a whole interval of coranks with one choice of block length at each tilt.

Use the [symmetric transfer operator](effective-small-area.md#real-transfer-operator). Thus $T_\beta$ has edge weights $e^{-\beta j/2}$ on $(j,j+1)$, $\rho$ and $u$ are its top eigenvalue and unit positive eigenvector, $K_z=(T_z/2)^2$ acts on even heights, $\lambda=\rho^2/4$ and $p=\log\lambda$. The normalized transform is $F(z)=2^{-m}\sum_k b_k e^{-zk}=e_0 K_z^n W_\delta(z)$. We write $c(z)=e_0\Pi_z W_\delta(z)$ for the amplitude of the top spectral projection. At $\beta>0$ the saddle equation is $k=-np'(\beta)$. First assume $H=\beta^{-1/3}\ge20$. Put $N=n/H^2$ and $L=\lceil H^2\rceil$.

## Comparing two frequencies

For a finite positive measure with Fourier transform $B(\theta)$,
$$B(0)-|B(r\theta)|\le r^2\big(B(0)-|B(\theta)|\big)
           \qquad(r=1,2,\ldots). \tag{2}$$
Choose $\phi=\arg B(\theta)$, taking any angle at a zero. Bound $|B(r\theta)|$ below by $\Re(e^{-ir\phi}B(r\theta))$ and integrate $1-\cos(rv)\le r^2(1-\cos v)$ at $v=\theta x-\phi$. Each entry of $K_{\beta+i\theta}^L$ is such a transform, with atom weights equal to the real tilted path weights. Write $M(\theta)$ for the symmetric matrix of its entrywise moduli. Testing nonnegative unit vectors in (2) gives
$$\|M(\theta)\|\le(1-r^{-2})\lambda^L+r^{-2}\|M(r\theta)\|.$$
Indeed the norm of a symmetric matrix with nonnegative entries is the supremum of its quadratic form over nonnegative unit vectors.

For $|\theta|\le\pi$ the absolute row sum of a tilted oscillatory block of $t$ even steps is at most $2\exp(-t|\theta|^{2/3}/75)$. To see the constant, pair labels in blocks of $2l$ steps as in the [fair Fourier bound](peak-rate.md#fourier-inversion-for-lattice-differences). At fixed start and endpoint the symmetric edge action differs from the negative down-label sum by a constant, also on unrestricted paths. An unrestricted row with modulus sum at most $\alpha$ gives a weighted surviving row with modulus sum at most $\min(v,\alpha+1-v)\le(1+\alpha)/2$, where $v$ is the total retained fair mass. This works because every retained real weight is in $[0,1]$ and omitted paths get weight zero. The paired blocks in that bound lose a factor $e^{-c}$ with $c/(2l)\ge |\theta|^{2/3}/75$ and $e^c<2$. Multiply the row bounds for consecutive blocks and bound the remainder by one. Symmetry gives the same operator norm bound for the entrywise moduli over all $t$ steps.

The sine trial on $0,\ldots,\lfloor3H\rfloor$ gives $2-\rho\le(3+\pi^2/9)/H^2<4.1/H^2$, so $-\log\lambda\le4.2/H^2$. Set $Y=10^4$ and $y=H^3\theta$. For $Y\le |y|\le\pi H^3$ the estimate with $t=2L$ gives $\|M(\theta)\|\le\lambda^L/2$, since $2e^{(4.2-2Y^{2/3}/75)L/H^2}<1/2$. For $0<|y|\le Y$, take $r=\lceil Y/|y|\rceil$. Then $Y\le r|y|\le 2Y<\pi H^3$ and (2) gives the block bound
$$\|K_{\beta+i\theta}^L\|\le\lambda^L(1-y^2/(8Y^2)). \tag{3}$$

The phase comparison also has an exact finite check. For start $i$ even, endpoint $j$, and down-label sum $S$ in a word of length $t$, the vertex area is $ti/2+\lfloor t^2/4\rfloor-S$. Twice the symmetric edge action equals twice this area minus $\lfloor j/2\rfloor-i/2$, by telescoping. The [verifier](verify_blocks.py) checks both equalities on every word of lengths two through twelve from heights zero, two and six, including words crossing the boundary.

~~~sh
python3 -B -c 'from verify_blocks import check_edge_actions; check_edge_actions()'
~~~

## Real and complex estimates near the saddle

The gap of $K=K_\beta$ is at least $.9/H^2$. In the [nodal cut argument](effective-small-area.md#real-transfer-operator), a cut at distance $l<H$ bounds the second positive eigenvalue $\nu$ of $T$ by $2\cos(\pi/(H+1))\le 2-8/H^2$. This follows from the fourth-order cosine bound and $H\ge20$. A cut at $l\ge H$ bounds it by $\rho e^{-1/(2H^2)}\le\rho-.98/H^2$. In both cases $\lambda_2\le(\rho-.98/H^2)^2/4$, giving the gap. The [upper bound on $\rho$](mode-bounds.md#upper-bound-for-a-single-small-corank) applies also at $8\beta$, whose height scale is $H/2$. Convexity gives
$$-p'(\beta)\ge \frac{p(\beta)-p(8\beta)}{7\beta}
   \ge\frac{4\cdot1.65-4.2}{7}H>H/3. \tag{4}$$

A lattice variance estimate improves the curvature bound. Extend $u$ by zero to negative indices and put $\mu=\sum_j j u_j^2$, $E=\sum_j(u_{j+1}-u_j)^2\le2-\rho$. The sum of $(j+1/2-\mu)(u_{j+1}^2-u_j^2)$ equals $-1$ by telescoping. Cauchy–Schwarz and $(u_{j+1}+u_j)^2\le2(u_{j+1}^2+u_j^2)$ give
$$1\le E\,(4\operatorname{Var}_{u^2}j+1).$$
Under the edge law $w_j=2e^{-\beta j/2}u_j u_{j+1}/\rho$, a uniformly chosen endpoint has law $u^2$. Its height is the lower edge index plus an independent fair zero or one. Consequently $\operatorname{Var}_w j\ge H^2/16.4-1/2>.059H^2$. The [reduced-resolvent variance bound](effective-small-area.md#real-transfer-operator) gives $p''\ge2(\operatorname{Var}_w j)^2>.006H^4$.

We record constants for analytic perturbation. With $A=I-K$ and $\epsilon=|z-\beta|/\beta\le.04$ one has $\|A^{-1/2}(K_z-K)A^{-1/2}\|\le\epsilon$. Indeed for real two-step action $d\ge0$ the modulus of the weight change is at most $\epsilon(\beta d)e^{-\beta d/2}\le\epsilon(1-e^{-\beta d})$. Sum this inequality by row and use the [Dirichlet form bound](effective-small-area.md#complex-tilts-near-the-saddle). On the circle of radius $r=.4/H^2$ about $\lambda$ the distance to the spectrum is at least $r$. There $\|A(w-K)^{-1}\|\le M=2+(1-\lambda)/r\le12.25$. The factored resolvent identity on this circle gives $\|\Pi_z-\Pi_\beta\|\le\epsilon M/(1-\epsilon M)$, in particular $\|\Pi_z\|<2$. Its eigenvalue lies inside the circle, so $|p(z)-p(\beta)|<.42/H^2$. By Cauchy's estimates
$$p''(\beta)<600H^4,\qquad |p'''(z)|<4\cdot10^5 H^7
     \quad (|z-\beta|\le .02\beta). \tag{5}$$

The real amplitude satisfies $c(\beta)>.1/H$. In fact $\max u_j^2\le2\sqrt E<4.1/H$ by telescoping. For $j>40H$ the potential $2-e^{-\beta(j-1)/2}-e^{-\beta j/2}$ exceeds $35/H^2$, and its expectation (with the missing boundary edge given weight zero) is at most $2-\rho$. Each parity therefore retains squared mass at least $1/2-4.1/35>.38$ on $[0,40H]$. The sum of $u_j$ there on either parity is at least $.38\sqrt{H/4.1}$. In $c(\beta)$ this is multiplied by at least $2u_0(\rho/2)^\delta e^{-10/H^2}$, with $u_0^2\ge H^{-3}/8$ from the boundary equation. This proves the lower bound.

The [two boundary estimates](effective-small-area.md#complex-tilts-near-the-saddle) give $\|e_0K_z^L\|\le H^{-3/2}$ and $\|K_z^L W_\delta(z)\|\le10\sqrt H$ for $\Re z\ge\beta/2$. Inserting these blocks on each side of $\Pi_z$ and dividing by $|\lambda_z|^{2L}$ gives $|c(z)/c(\beta)|\le 200 e^{2(4.2+.42)L/H^2}<4\cdot10^6$ on the full disk. On the half disk $\beta|c'(z)/c(\beta)|\le2\cdot10^8$.

For $|z-\beta|\le10^{-8}\beta$, the projection difference is below $2\cdot10^{-7}$. The form perturbation gives $\|K_z v\|^2\le\langle v,(K^2+3\epsilon(I-K))v\rangle$ as in the cited resolvent argument. The convex function $t^2+3\epsilon(1-t)$ is at most $\lambda^2-1/H^2$ on $[0,\lambda-.9/H^2]$ by its endpoint values, and at most $\lambda^2+2\cdot10^{-7}/H^2$ at $\lambda$. A unit vector in $\ker\Pi_z$ has overlap below $2\cdot10^{-7}$ with the real unit top vector. The restricted norm is therefore at most $\lambda e^{-.4/H^2}$.

## Inversion for $H\ge20$

Put $\Psi(\theta)=F(\beta+i\theta)/(c(\beta)\lambda^n)$ and $y_0=10^{-8}$. Assume $N\ge10^{28}$. For $|y|\le y_0$ the principal term in $\Psi$ is $(c(z)/c(\beta))e^{n(p(z)-p(\beta))}$ with $z=\beta+i\theta$. Its absolute error is below $e^{20}e^{-.39N}$ by peeling off the two boundary blocks, then using the restricted norm and $\|I-\Pi_z\|<3$. For $y_0\le|y|\le Y$ at least $N/2$ full blocks fit between the two boundary blocks. Apply (3), with $\|K_z^s\|\le\lambda^s$ for the remainder, to get
$$|\Psi(\theta)|\le e^{20}\exp(-Ny^2/(16Y^2)).$$
For $Y\le |y|\le\pi H^3$ apply the absolute row estimate directly to the middle $2n-4L\ge1.99n$ steps. Division by $\lambda^n$ costs at most $e^{4.2N}$. Since $(1.99/75-1/80)Y^{2/3}>4.2$ this gives
$$|\Psi(\theta)|\le e^{20}\exp(-N|y|^{2/3}/80).$$

Set $\sigma^2=np''(\beta)$, $d=\beta\sigma$ and $x=\sigma\theta=d y$. We have $\sqrt{.006N}<d<25\sqrt N$. After centering by $e^{ik\theta}$, the principal exponent differs from $-x^2/2$ by at most $4\cdot10^5 N|y|^3/6$. This is at most $x^2/4$ for $|y|\le y_0$. For $|x|\le16$ the same error is less than $.007$, and the relative amplitude differs from one by at most $2\cdot10^8\,16/d<.001$. Thus the real centered principal term there is at least $.99 e^{-x^2/2}$.

Here are explicit bounds on the integral errors with weight $1+x^2$. For $|x|>16$ in the low-frequency range the principal tail costs at most $4\cdot10^6\int_{|x|>16}(1+x^2)e^{-x^2/4}\,dx<.01$. The low remainder and the intermediate frequencies together cost at most
$$2e^{20}(1+dY)^3\big(e^{-.39N}+e^{-Ny_0^2/(16Y^2)}\big)<.01.$$
The weaker exponent already exceeds $624$ at the threshold and grows linearly in $N$, whereas the prefactor grows at most as $N^{3/2}$. For the high tail integrate $2e^{20}(1+d)^3(1+y^2)e^{-Ny^{2/3}/80}$ over $y\ge Y$. Extract $e^{-NY^{2/3}/160}$ and bound the remaining exponential by $e^{-y^{2/3}}$. This contribution is below $.01$ as well.

Writing $J(x)=e^{ik\theta}\Psi(\theta)$, the integral of $\Re J$ over the scaled period exceeds one. So does its integral with multiplier $4\sigma^2\sin^2(x/(2\sigma))$, which is between $.99x^2$ and $x^2$ on $[-16,16]$ and at most $x^2$ elsewhere. Both corresponding central Gaussian integrals exceed two. The integral of $|xJ|$ is below $10^8$ by the same tail bounds and the central absolute majorant. Inversion gives relative change at most $10^8/\sigma<\beta/4$ in the tilted coefficient from $k$ to $k+1$. Undoing the tilt gives strict growth, since $e^\beta(1-\beta/4)>1$ for $0<\beta\le1$. The positive integral with the sine multiplier gives strict negative centered second difference of the tilted mass. The arithmetic-geometric mean inequality then gives strict log-concavity, preserved upon undoing the tilt.

## Bounded height scales

For completeness the following estimates cover $1/8000\le\beta\le8$ and $n\ge10^{100}$. They also give strict growth and strict log-concavity at every integer saddle in this range. The nodal cut gives $\lambda-\lambda_2\ge\lambda(1-e^{-\beta})>3\cdot10^{-5}$. The boundary equations give $u_0^2\ge1/64000$ for $\beta\le1$ and $u_0^2>.19$ for $\beta\ge1$, by the boundary inequality $1-2u_0^2\le e^{-\beta/2}(1-u_0^2)$. Hence $c(\beta)\ge u_0^2\ge1/64000$ and
$$p''\ge w_0w_1/2\ge 2 e^{-\beta}u_0^4>10^{-10}.$$
Here the lower bounds on $u_0^2$ are used on their respective sides of one.

On $|z-\beta|\le10^{-10}$ the row and column bounds give $\|K_z-K\|\le8000|z-\beta|$ by the two-step weights. The circle of radius $10^{-5}$ about $\lambda$ has distance at least $10^{-5}$ from the real spectrum. Resolvent comparison gives $\|\Pi_z\|<1.09$ on the parameter disk and $|p(z)-p(\beta)|<5\cdot10^{-5}$, since $\lambda\ge1/4$. Also $\|W_\delta(z)\|\le\|v_z\|\le150$ by its geometric tail. Thus $|c(z)/c(\beta)|<2\cdot10^7$ on the disk. Cauchy's estimates on its half disk give $|c'(z)/c(\beta)|<4\cdot10^{17}$, $|p'''(z)|<3\cdot10^{27}$ and $p''(\beta)\le10^{16}$. On $|\theta|\le10^{-39}$ the resolvent projection differs from $\Pi_\beta$ by at most $10^{-29}$. On its complementary invariant space $\|K_z\|\le\lambda-10^{-5}$ by the real gap and the operator perturbation. The principal term in $\Psi$ consequently has absolute error at most $3\cdot10^7 e^{-10^{-5}n}$.

For the other frequencies use the two loops at height two. Their modulus deficit is at least $(e^{-16}/4)\sin^2(\theta/2)$. The even unit ground vector there satisfies $u_e(2)\ge\sqrt2 e^{-\beta/2}u_0>.003$, using the two bounds on $u_0$ above. A nonnegative unit vector at distance at least $.0015$ from $u_e$ loses at least $(3\cdot10^{-5})(.0015)^2/2$ in the real Rayleigh quotient. A closer vector pays the loop deficit times at least $.0015^2$. Thus $\|K_{\beta+i\theta}\|\le\lambda-10^{-14}\sin^2(\theta/2)$. For $10^{-39}\le|\theta|\le\pi$ this gives $|\Psi(\theta)|\le 10^7 e^{-10^{-93}n}$, since $\sin^2(\theta/2)\ge\theta^2/\pi^2$.

Use $x=\sigma\theta$ as above. On $|\theta|\le10^{-39}$ the exponent error is at most $3\cdot10^{27}n|\theta|^3/6\le x^2/4$. On $|x|\le16$ this error is below $.001$ by $\sigma^2>10^{-10}n$, and the amplitude error $4\cdot10^{17}\,16/\sigma$ is below $.001$. The principal tail costs at most $2\cdot10^7\int_{|x|>16}(1+x^2)e^{-x^2/4}\,dx<.01$. The other errors cost at most $10^{10}(1+\sigma)^3(e^{-10^{-5}n}+e^{-10^{-93}n})<.01$, using $\sigma\le10^8\sqrt n$. The same inversion gives strict log-concavity and a relative tilted adjacent change below $10^8/\sigma<\min(\beta/4,1/4)$. Undoing the tilt gives strict growth also for $\beta\ge1$.

Finally, the real slope decreases continuously from infinity to zero. It is at most $\log4$ at $\beta=1$, and less than $1/105$ at $\beta=8$ by the [finite sparse-tilt estimate](upper-curvature.md#joining-the-tilts-between-the-sparse-and-peak-regimes). For $n/105\le k\le 2n$ the saddle is therefore at $\beta\le8$ and cannot have $H\ge20$ by (4). For $2n\le k\le3\cdot10^{-15}n^{3/2}$ the saddle is below one. If $H\ge20$, (4) gives $H<3k/n$ and $N>1/(9(3\cdot10^{-15})^2)>10^{28}$. All remaining saddles are covered by the bounded-height argument. This proves (1).
