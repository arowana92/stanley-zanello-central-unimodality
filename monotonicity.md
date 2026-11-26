# Coefficient inequalities for both central shapes

Write $m=2n$ or $2n+1$, $D=\lfloor m^2/4\rfloor$ and $b_k=a_{D-k}$. Thus $k$ measures the number of missing cells. The following bounds concern the *actual adjacent coefficients*, including the ballot restriction.

1. For every $m$, the ranks increase weakly through $\lceil D/2\rceil$.
2. For all sufficiently large $m$, $a_{j+1}>a_j$ whenever $D/2\le j\le D-m^{3/2}\log m$.
3. For each fixed $C>0$, all sufficiently large $n$ satisfy $b_{k+1}>b_k$ simultaneously for $0\le k\le Cn$, for both parities of $m$.

In particular every global maximum has corank $k$ with $k/n\to\infty$ and $k=O(n^{3/2}\log n)$ as $n\to\infty$. The bounds leave the signs of successive differences in the intervening range undetermined. In particular they allow several peaks there.

## 1. Lower half for all sizes

Strict partitions with largest part at most $m-1$ form the shifted Young lattice inside the ordinary strict staircase $(m-1,m-2,\ldots,1)$. This is the maximal parabolic quotient of the type $B_{m-1}$ Weyl group for the spin node, ordered by Bruhat order. In the strict-partition parametrization, containment gives the order and adding a cell is a cover. Hence length is size, and the shapes below a fixed $\lambda$ form the principal parabolic interval ending at length $D=|\lambda|$. Björner and Ekedahl's Theorem A gives $a_i\le a_j$ for $i\le j\le D-i$, in particular the first assertion above. The result also applies to noncentral strict shapes. [Strict partitions and Schubert containment, Billey and Mitchell, introduction](https://sites.math.washington.edu/~billey/papers/affine.partitions.pdf) · [Minuscule parabolic quotients, §3](https://doi.org/10.1093/IMRN/RNY018) · [Björner and Ekedahl, Theorem A](https://arxiv.org/abs/math/0508022)

## 2. Growth beyond the middle

Use the ballot-word encoding in the [README](README.md). First allow all words. For $1\le r\le m$ let $X_r$ be independent Bernoulli variables with
$$p_r=\Pr(X_r=1)=1/(1+e^{\alpha r/m}),\qquad S=\sum_{r=1}^m rX_r.$$

Read the variables in decreasing order of $r$, taking a down step when $X_r=1$. Let $E$ denote survival at all times (height always nonnegative). The joint mass $P_j=\Pr(S=j,E)$ equals $a_j e^{-\alpha j/m}/Z$, with $Z=\prod_r(1+e^{-\alpha r/m})$.

**Choice of tilt.** For each $j$ in the range of assertion 2 choose $\alpha$ so that $\mathbb E S=j$. The mean at zero is $m(m+1)/4=D+O(m)$. At a sufficiently large absolute constant $A$ the mean falls below $D/2$ for all large $m$, by the Riemann sum for $\int_0^1 x/(1+e^{Ax})\,dx$. Its derivative is $-m^{-1}\sum_r r^2p_r(1-p_r)$, bounded in magnitude above and below by positive constants times $m^2$ on $[0,A]$. Thus
$$c\,m^{-1/2}\log m\le \alpha\le A$$
with an absolute $c>0$. All subsequent bounds are uniform over these tilts.

**Smoothing by the small parts.** Let $S_M=\sum_{r=1}^M r X_r$ for $m/2\le M\le m$ and $f(u)=\Pr(S_M=u)$. We use two estimates:
$$\sup_u |f(u+1)-f(u)|=O(m^{-3}),\qquad
 f(u)\ge c_H m^{-3/2}\quad (|u-\mathbb ES_M|\le Hm^{3/2}),$$
for each fixed $H$ and sufficiently large $m$.

Here are details ensuring that lattice effects do not obscure an adjacent difference. The absolute characteristic function on $[-\pi,\pi]$ is at most $\exp(-c_1\sum_{r\le M}\sin^2(r\theta/2))$ by the uniform bounds on $p_r(1-p_r)$. For $|\theta|\le1/M$ the sum is $\gg M^3\theta^2$. For $1/M\le|\theta|\le 4\pi/M$, the first $\lfloor M/(4\pi)\rfloor$ terms give $\gg M$. Beyond $4\pi/M$, summing the geometric series for $\sum_r e^{ir\theta}$ gives the same lower bound. Inverting with the extra factor $|1-e^{-i\theta}|\le|\theta|$ proves the first estimate. For the second, put $\sigma^2=\sum_{r\le M}r^2p_r(1-p_r)\asymp m^3$. At $\theta=t/\sigma$, the log of the centered characteristic function is $-t^2/2+O(|t|^3m^4/\sigma^3)$ for bounded $t$, by Taylor expansion of the independent factors. The preceding integral bounds give Gaussian domination out to $1/M$ and exponentially small integral outside. Fourier inversion therefore gives $\sigma f(u)=(2\pi)^{-1/2}\exp(-(u-\mathbb E S_M)^2/(2\sigma^2))+o(1)$ uniformly in $u$, proving the claim.

**Cost of the ballot condition.** Set $L=\lceil B\log m/\alpha^2\rceil$ with $B$ a sufficiently large absolute constant and $M=m-L$. Then $L=O(m/\log m)$, so $M\ge m/2$. Write $E_L$ for survival through time $L$ and $s_L=\Pr(E_L)$. By coupling to fair independent steps using the same uniforms, $s_L\ge 2^{-L}\binom{L}{\lfloor L/2\rfloor}\gg m^{-1/2}$.

The expected height at time $t$ is at least $c_2\alpha t$. Indeed at least half of the first $t$ weights $r$ satisfy $r\ge m/2$ and their height increments have mean $\tanh(\alpha r/(2m))\gg\alpha$. All other increments have nonnegative means. Hoeffding's bound and a union bound give $\Pr(E_L\setminus E)\le m\exp(-c_3\alpha^2 L)\le m^{-10}$ by the choice of $B$.

Write $U=S-S_M$ for the weight of the prefix. By the same bounded-sum inequality,
$$\Pr(|U-\mathbb E U|>K m\sqrt{L\log m})\le m^{-10}$$
for a fixed large $K$. The threshold is $O(m^{3/2})$ by the bound on $L$. Consequently the joint mass at $j$ with $E_L$ imposed is at least $(s_L-m^{-10})c_H m^{-3/2}$: condition on each surviving prefix in this window and apply the smoothing bound to $u=j-U$, using $j=\mathbb E S$. Removing the paths that later hit $-1$ gives $P_j\gg s_Lm^{-3/2}$.

Conditioning just on the prefix also bounds the adjacent difference for $E_L$ by $O(s_Lm^{-3})$, uniformly even for prefixes outside the window. Passing to $E$ changes this bound by at most $2m^{-10}$. Hence
$$P_{j+1}/P_j=1+O(m^{-3/2}).$$
The corresponding coefficient ratio gains the factor $e^{\alpha/m}$. Since $\alpha/m\gg m^{-3/2}\log m$, the ratio exceeds one for all large $m$. This proves assertion 2.

## 3. Decrease near the top

**An elementary bound for every $n$.** The $n$ row ends of the full shifted shape are maximal cells: successive row lengths differ by two and their right endpoints move one column to the left. The missing cells of a subshape form an upper order ideal of size $k$. At least $n-k$ of these maximal cells are still available to add. Every upper ideal of size $k+1$ has at most $k+1$ predecessors. Counting edges gives
$$(k+1)b_{k+1}\ \ge\ (n-k)b_k.$$
In particular the inequality is strict between $b_k$ and $b_{k+1}$ when $2k<n-1$. Every rank occurs, for example by taking initial segments of a linear extension.

**Area of the walk.** At time $t$ let $h_t$ be the height and $d_t=(t-h_t)/2$ the total downs so far. Each down at time $i$ contributes $m+1-i$ to $\sum_t d_t$. Since $\sum_t\lfloor t/2\rfloor=D$, the corank is
$$k=\sum_{t=1}^m\left\lfloor h_t/2\right\rfloor.$$
We derive a coefficient ratio for $k/n$ in any compact subinterval of $(0,\infty)$.

For a real $s<0$ weight a walk by $e^{sk}$. On heights $h\ge0$ take the symmetric tridiagonal matrix $T_s$ with zero diagonal and edge $(h,h+1)$ of weight $e^{sh/2}$. Put $v_s(h)=e^{s\lfloor h/2\rfloor/2}$. The edge exponent is the average of the two endpoint values of $\lfloor h/2\rfloor$. Multiplying along the path leaves half the terminal value to be supplied by $v_s$. With $e_0$ the unit row at zero, the exact identity is
$$B_m(s):=\sum_k b_ke^{sk}= e_0 T_s^{\,m}v_s.$$
The same identity holds for complex $s$ with negative real part.

**Dominant eigenvalue.** Both $T_z$ and $v_z$ depend analytically in norm on $\Re z<0$ by exponential decay. The operator $T_z$ is compact (even Hilbert–Schmidt). Write $K_z$ for $T_z^2$ restricted to even heights, and put $\delta=m-2n\in\{0,1\}$. Then $B_m(z)=e_0 K_z^n (T_z^\delta v_z)_{\rm even}$. For real $s$, $K_s$ is positive semidefinite and tridiagonal, with strictly positive adjacent entries and diagonal. Its top eigenvalue $\lambda(s)>0$ is simple and separated in modulus from the rest of its spectrum. Indeed the Rayleigh quotient attains its maximum by compactness, taking absolute values gives a nonnegative maximizer, and the recurrence gives strict positivity. The recurrence with the left boundary also determines each eigenvector from its first coordinate, proving simplicity. Bipartiteness of $T_s$ identifies $\lambda(s)=\rho(T_s)^2$ (the two blocks of the square have the same nonzero spectrum). Denote $p(s)=\log\lambda(s)$.

Near each real $s<0$ the isolated simple eigenvalue, its logarithm and its spectral projection are analytic. In particular
$$B_m(z)=c_\delta(z)e^{np(z)}+O((\eta\,\lambda(s))^n),\qquad \eta<1,$$
with $c_\delta(s)>0$ from the positive left and right factors. This expansion follows by integrating the resolvent on a small circle around the simple eigenvalue and a circle about zero enclosing the complementary spectrum. The contours persist under small norm perturbations. All local estimates below can be made uniform on compact real intervals by a finite cover.

**Slopes.** We have $p''(s)>0$. To see this, let $u$ be the positive normalized top eigenvector of $T_s$ (existence and positivity follow by the same Rayleigh argument). The function
$$g(t)=\log\!\left(2\sum_{h\ge0}u_hu_{h+1}e^{th/2}\right)$$
is bounded above by $p(t)/2$ and agrees with it at $t=s$. Its second derivative at $s$ is the variance of $h/2$ under the positive summand weights after normalization, hence strictly positive. Thus $p''(s)/2\ge g''(s)>0$. The same contact gives $p'(s)/2=g'(s)$.

As $s\to-\infty$, $T_s$ converges in norm to the single edge of weight one, so $p(s)\to0$ and by convexity $p'(s)\to0$. As $s\uparrow0$, $\rho(T_s)\to2$. The upper bound is the norm bound two for the adjacency operator of the half-line, and finite constant test vectors on increasingly long intervals approach that bound as $s\uparrow0$. For the normalized eigenvectors $u=u(s)$ each fixed coordinate tends to zero: any weak subsequential limit solves $T_0u=2u$ coordinatewise, and the left boundary forces $u_h=(h+1)u_0$, which is square summable only for the zero vector. Consequently the probability weights proportional to $2u_hu_{h+1}e^{sh/2}$ escape every finite set (their total tends to two). Their mean of $h/2$ tends to infinity. This proves that $p'$ maps $(-\infty,0)$ bijectively onto $(0,\infty)$.

**Lattice span and local inversion.** For $0<|\theta|\le\pi$, the spectral radius of $K_{s+i\theta}$ is strictly less than $\lambda(s)$. Entrywise absolute values are bounded by $K_s$, with strict inequality at every even height $h\ge2$ on the diagonal. There the two contributions have exponents $h-1,h$, with different phases. If equality of spectral radii held, compactness would give an eigenvector $w$ of that modulus. The inequality $\lambda(s)|w|\le K_s|w|$ must be equality after pairing with the strictly positive top eigenvector of $K_s$, and hence coordinatewise. Thus $|w|$ is strictly positive, contradicting the strict diagonal inequality in the triangle bound. Off any neighborhood of $\theta=0$ the spectral gap gives a uniform exponential power bound by compactness of the parameter set and the resolvent formula for powers (locally take a circle of radius less than $\lambda(s)$ enclosing the spectrum).

Choose $s$ so that $p'(s)=k/n$. For $r=0,1$, Fourier inversion gives
$$b_{k+r}e^{s(k+r)}=\frac{1}{2\pi}\int_{-\pi}^{\pi} B_m(s+i\theta)e^{-i(k+r)\theta}\,d\theta.$$
In a neighborhood of zero,
$$p(s+i\theta)=p(s)+i\theta p'(s)-\theta^2p''(s)/2+O(|\theta|^3).$$
After scaling $\theta=t/\sqrt n$, the linear term cancels and $e^{-ir\theta}\to1$. The quadratic term gives an integrable Gaussian majorant there, and the rest of the circle contributes exponentially less. Both integrals have the same leading term $c_\delta(s)e^{np(s)}/\sqrt{2\pi n p''(s)}$. The errors are relative $o(1)$ uniformly for $k/n$ in any fixed compact subinterval of $(0,\infty)$: the corresponding $s$ range is compact in $(-\infty,0)$, with $p''$ bounded below and the two prefactors bounded away from zero. We obtain
$$\frac{b_{k+1}}{b_k}=e^{-s}(1+o(1)).$$
On the chosen interval $\inf e^{-s}>1$. Applying this to $1/4\le k/n\le\max(1,C)$, and using the elementary bound for smaller $k$, proves assertion 3.

The proof gives no threshold uniform in $C$. Sending $C$ to infinity *after* $n$ gives the stated lower bound on the corank of a mode. Substituting a growing $C=C(n)$ into the eigenvalue estimate would require control as $s\uparrow0$, where the limiting operator loses its isolated eigenvalue.
