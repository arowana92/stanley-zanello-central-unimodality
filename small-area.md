# The intermediate small-area regime

Let $K=\sum_{t=1}^m\lfloor H_t/2\rfloor$ on a nonnegative simple walk from zero, with $H_t$ its height. The coefficient $b_k$ counts walks with $K=k$. Both lengths $m=2n$ and $m=2n+1$ are allowed. We retain a free endpoint throughout.

**Theorem.** On every sequence with $k/m\to\infty$ and $k/m^{3/2}\to0$, one has $b_{k+1}>b_k$ eventually.

The issue here is that the positive exponential tilt needed to encourage small area tends to zero. An $o(1)$ relative error on individual coefficients would lose the sign of the adjacent difference. We bound the difference of the *tilted* masses relative to the tilt itself.

## Diffusive blocks and their kernels

Choose the even block length $L=2\lfloor (k/m)^2/2\rfloor$. Then $L\to\infty$, $m/L\to\infty$. Use a first block of $L$ steps, $N=\lfloor m/L\rfloor-2$ middle blocks of $L$ steps, and a last block of $r=m-(N+1)L$ steps, where $L\le r<2L$. In particular $k/(NL^{3/2})\to1$.

Weight fair paths by $e^{-zK/L^{3/2}}$ for complex $\Re z>0$. Kill paths on their first visit to $-1$. Let $Q_L(z;i,j)$ be the resulting transition weight of one block from even height $i$ to even height $j$. The exponent uses only the heights *after* steps of that block. For even $i$, use the cell $[i/\sqrt L,(i+2)/\sqrt L)$ of width $\delta=2/\sqrt L$. On $L^2(0,\infty)$ extend the matrix to an integral operator by giving its kernel the constant value $Q_L(z;i,j)/\delta$ on each pair of cells. Composition now agrees exactly with matrix multiplication.

**Kernel limit.** In Hilbert–Schmidt norm, locally uniformly on $\Re z>0$, these operators converge to $Q(z)$ with kernel
$$p_1(y-x)\,\mathbb E^{x,y}_{\rm br}\!
 \left[{\bf1}_{\{\min X>0\}}\exp\!\left(-\tfrac z2\int_0^1 X(t)\,dt\right)\right],$$
where $p_1$ is the standard normal density and $X$ is a unit-time Brownian bridge between $x,y>0$.

Here are convergence and domination details. For $i/\sqrt L\to x$, $j/\sqrt L\to y$ in the interior, the binomial local limit gives the factor $p_1(y-x)$ after division by $\delta$. The interpolated simple-walk bridge tends to the Brownian bridge. One can obtain its finite-dimensional distributions from products of binomial transition probabilities divided by the endpoint probability. For tightness on each half, compare to an unconditioned walk. The unused half's transition probability is at most $C/\sqrt L$, and the denominator is asymptotic to $\delta p_1(y-x)$. Reverse time for the second half. The minimum of the limiting bridge has no atom at zero by reflection. The normalized area differs from half its interpolated area integral by $o(1)$ for paths in a bounded rescaled height range, so bounded convergence in distribution gives the pointwise kernel limit. On surviving paths the weight has modulus at most one.

For a compact region of parameters with $\Re z\ge a_0>0$, put $M=\max(i,j)$. The binomial mass at displacement $d$ is bounded by $C L^{-1/2}e^{-c d^2/L}$, by the central binomial bound and the ratios of successive binomial masses. If $|i-j|\ge M/4$ this alone gives a square-integrable envelope $C e^{-c M^2/L}$ after division by $\delta$. Otherwise $i,j>3M/4$ apart from the trivial zero case. Paths staying above $\lfloor M/2\rfloor$ have tilt at most $C e^{-c M/\sqrt L}$. For paths reaching that level, reflection up to the first hit bounds their endpoint probability by the unrestricted binomial mass at displacement $i+j-2\lfloor M/2\rfloor\ge M/2$. Thus there is an envelope $C(e^{-c\max(x,y)}+e^{-c\max(x,y)^2})$ in scaled coordinates, with constants uniform in $L$. Dominated convergence proves the norm claim, also along any $z_L\to z$ in the half-plane. Analyticity in Hilbert–Schmidt norm follows from the same bounds on a slightly larger compact neighborhood using Cauchy's formula.

On the real axis $Q(a)$ is the time-one Dirichlet heat semigroup with generator $\frac12\,d^2/dx^2-a x/2$, by Feynman–Kac. It is compact, self-adjoint and positive semidefinite, with strictly positive interior kernel. Its top eigenvalue is simple, isolated and equals
$$\lambda(a)=\exp(-E a^{2/3}),\qquad E>0.$$
Indeed dilation $x=a^{-1/3}u$ multiplies the Dirichlet Schrödinger operator at one by $a^{2/3}$. Its ground energy is positive since a zero-energy state would have zero kinetic and potential energy. Simplicity follows from strict positivity of the kernel and the variational principle (a sign-changing maximizer improves on taking absolute values). Real transfer operators and this Airy scaling for area-tilted walks have been studied by Ioffe, Shlosman and Velenik. The norm argument above also treats complex tilts and the lattice parity used here. [Ioffe, Shlosman and Velenik](https://arxiv.org/abs/1403.5073)

For $y\ne0$, $\rho(Q(a+iy))<\lambda(a)$. At positive endpoints the bridge areas on survival cannot have a constant phase at frequency $y$. Tubes about strictly positive continuous paths with these endpoints have positive bridge probability, and smooth perturbations within the interval vary the area continuously. Thus $|Q(a+iy;x,x')|<Q(a;x,x')$. If equality of spectral radii held, a nonzero eigenvector $w$ at that modulus would give $\lambda(a)|w|\le |Q(a+iy)||w|\le Q(a)|w|$. Pairing with the strictly positive real ground state contradicts the strict kernel inequality.

## Boundary factors and powers

Let $u_L(z)$ be the step function taking value $\sqrt L\,Q_L(z;0,j)/\delta$ on the $j$ cell. Let $v_{L,r}(z)$ have value equal to the total surviving weighted mass of an $r$-step suffix starting at $i$ on the $i$ cell. For the whole walk the unconditioned transform is exactly
$$Z_m(z)=\mathbb E[e^{-zK/L^{3/2}}{\bf1}_{E_m}]
      = L^{-1/2}\langle u_L(z),Q_L(z)^N v_{L,r}(z)\rangle,$$
where $E_m$ denotes survival and the pairing is *bilinear* integration. This records the small probability of surviving from the wall before a spectral approximation is made.

Both boundary functions have uniformly bounded $L^2$ norms on compact subsets of $\Re z>0$. For the first, reflection expresses the unrestricted-by-area surviving probability to $j$ as the difference of the binomial masses at $j$ and $j+2$. This is at most $C L^{-1}(1+j/\sqrt L)e^{-c j^2/L}$, giving the bound after the normalization in $u_L$. For the suffix, split at the event that the walk drops to $i/2$ or below. Its probability is at most $C e^{-c i^2/L}$ by reflection or the maximal Hoeffding bound for $r<2L$. On the complement the area tilt is at most $C e^{-c i/\sqrt L}$.

We also need a real lower bound. Along $a_L\to a>0$, the measures $u_L(a_L)\,dx$ converge weakly to a nonzero positive measure on $(0,\infty)$. Indeed $\sqrt L\,\Pr(E_L)\to\sqrt{2/\pi}$, and under $E_L$ the rescaled walk converges to the Brownian meander. This gives the limiting endpoint law weighted by the strictly positive factor $\exp(-a\int M/2)$, with the same normalizing constant. The $L^2$ bound implies weak convergence as $L^2$ functions as well, by testing first against compactly supported continuous functions. Along a further subsequence assume $r/L\to\tau\in[1,2]$. For each starting $x>0$ the invariance principle from $i/\sqrt L\to x$ gives convergence of $v_{L,r}(a_L)$ to the positive surviving Brownian Feynman–Kac mass over time $\tau$. The minimum has no atom at zero, and the preceding envelope gives strong $L^2$ convergence. These arguments include odd suffix lengths. [Meander invariance principle](https://doi.org/10.1214/aop/1176996098)

On any compact interval $I\subset(0,\infty)$ the isolated eigenvalue and projection persist for $Q_L(z)$ near $I$, with $\lambda_L(z)\to\lambda(z)$ and $P_L(z)\to P(z)$ locally uniformly. This follows by norm convergence and the resolvent integral on a circle about the isolated eigenvalue. Let $p_L=\log\lambda_L$ with the real branch on $I$. In particular the derivatives of $p_L$ converge to those of $-Ea^{2/3}$ on $I$ by Cauchy's formula. The scalar amplitudes $c_L(z)=\langle u_L(z),P_L(z)v_{L,r}(z)\rangle$ and their first derivatives are uniformly bounded there. Their real values have a uniform positive lower bound for large $L$. Otherwise take a convergent subsequence of $a_L,r/L$ and use weak convergence on the left, strong convergence on the right, and the positive rank-one limiting projection. The resulting limit is strictly positive.

For real $a\in I$ and $z=a+iy$ in a sufficiently small neighborhood of $a$ we have
$$\sqrt L\, Z_m(z)= c_L(z)e^{N p_L(z)}+
 O\!\left((\eta\lambda_L(a))^N\right),\qquad \eta<1.$$
For $y_0\le |y|\le Y$ with any fixed $0<y_0<Y$, the whole expression is $O((\eta'\lambda_L(a))^N)$ with $\eta'<1$. For the first bound enclose the complementary spectrum by a circle of radius strictly below $\lambda(a)$. For the second use the strict complex spectral-radius bound on all of the spectrum. Norm convergence ensures uniform resolvent bounds on the circles for the finite-$L$ operators. Integrating the resolvents for the powers, then using a finite cover of the parameter sets, gives both estimates including the boundary factors.

## Inversion with a shrinking tilt

Choose $I=[a_0,a_1]$ such that $(2E/3)a_0^{-1/3}>1>(2E/3)a_1^{-1/3}$. For large $L,N$ choose a real $a\in I$ solving
$$-p_L'(a)=k/(NL^{3/2}).$$
Existence follows from the derivative convergence and $k/(NL^{3/2})\to1$. On this interval $p_L''(a)$ is bounded above and bounded away from zero, since its limit is $(2E/9)a^{-4/3}$. All estimates can thus be used at this varying saddle.

For high frequencies $Y\le |y|\le\pi L^{3/2}$ a separate bound avoids any loss from the expanding inversion interval. Put $\theta=y/L^{3/2}$. In the [paired-label bound](peak-window.md#a-bound-on-the-characteristic-function), keep the real factor $e^{-aK_{\rm block}/L^{3/2}}$ on surviving segments and set the weight to zero on killed paths. Its value lies in $[0,1]$. The unrestricted Fourier kernel for block area has the same paired-label cancellation. Starting height fixes the time parities, so the area is a constant minus the sum of the descending local labels of its downs, by summing the prefix down counts. This holds even on unrestricted paths of negative height. If the total retained real mass of a row is $p$, deleting weights from the unrestricted Fourier row gives the same estimate $\min(p,\rho+1-p)$. Peel off the first $L$ steps, paying the absolute row-sum bound $\Pr(E_L)=O(L^{-1/2})$. Using the frequency-dependent blocks in all remaining steps yields
$$|Z_m(a+iy)|\le C L^{-1/2}\exp(-cN |y|^{2/3}).$$
Since $Z_m(a)\gg L^{-1/2}\lambda_L(a)^N$ and $\lambda_L(a)$ is bounded away from zero, choosing $Y$ a sufficiently large constant leaves
$$|Z_m(a+iy)/Z_m(a)|\le C\exp(-c'N |y|^{2/3})\quad (|y|\ge Y)$$
in the inversion interval.

Write $\mathbb P_a$ for the probability law on surviving paths proportional to $e^{-aK/L^{3/2}}$. In Fourier inversion at $k$ use $y=L^{3/2}\theta$. For small $y$, the expansion of $p_L(a+iy)$ has terms $iy p_L'(a)-y^2p_L''(a)/2+O(|y|^3)$ beyond its constant term, uniformly by analyticity. For the transform with the negative Fourier phase, inversion multiplies by $e^{iyk/L^{3/2}}$, cancelling the linear term. Under the substitution $t=y\sqrt N$, the amplitude ratio tends to one for bounded $t$, and the integrand is dominated in this neighborhood by a Gaussian in $t$ plus an exponentially small remainder. Outside, the two spectral and high-frequency bounds above make the integrals negligible. It follows that
$$\mathbb P_a(K=k)=\frac{1+o(1)}{L^{3/2}\sqrt{2\pi N p_L''(a)}}.$$

Inserting $|e^{iy/L^{3/2}}-1|\le |y|/L^{3/2}$ in the same integral gives the absolute bound
$$|\mathbb P_a(K=k+1)-\mathbb P_a(K=k)|=O(L^{-3}N^{-1}).$$
Here $\int |y|e^{-cNy^2}\,dy=O(1/N)$ near zero. The expanding high-frequency tail is integrable with the extra factor $|y|$ by the preceding estimate. Dividing by the lower mass estimate and undoing the real tilt gives
$$\frac{b_{k+1}}{b_k}=e^{a/L^{3/2}}
   \left(1+O\!\left(\frac{1}{L^{3/2}\sqrt N}\right)\right)>1$$
eventually, since $\inf I>0$ and $N\to\infty$.

## Consequence and finite-size gap

Both central families are unimodal for all sufficiently large $n$. To see the quantifiers, suppose infinitely many sizes failed. The lower-half inequality, rising-side estimate, strict log-concavity through the global peak, and fixed-linear small-corank estimate force a subsequence with a strict decline in corank order where $k/m\to\infty$ and $k/m^{3/2}\to0$, as detailed in the [rising-side proof](rising-side.md#reduction-to-intermediate-small-area). The theorem just proved contradicts that decline.

This argument uses compactness, convergence without rates and subsequences. The [finite reduction](finite-reduction.md) gives an explicit threshold using uniform transfer bounds and exact area moments. A finite exceptional size beyond the [computed range](README.md#exact-coefficient-checks) remains possible.
