# Strict log-concavity throughout the upper half at large sizes

Write $k=D-j$ for corank and $b_k=a_{D-k}$. Both statements below apply to the odd-part and even-part staircases.

* At every size $n$, the log-concavity determinant exceeds $b_k^2/(40k)$ for $1\le k\le n/3$. This uses the [paired-step ratio recurrence and rational certificate](paired-steps.md). The elementary argument below gives strict log-concavity for $1\le k\le n/105$.
* Every $n\ge10^{164}$ satisfies strict log-concavity at **every interior rank $j\ge D/2$**. [Proof using tilted second differences](mode-comparison.md#lattice-differences-at-the-tilted-mode)

The second assertion implies unimodality by lower-half growth. The [finite reduction](finite-reduction.md) also bounds first differences, giving unimodality at a smaller threshold. The exact upper-half curvature checks begin at $n=9$.

## A finite polynomial at small positive tilt

Fix $n$ and one parity, and use the run polynomials of the [row-deficit decomposition](fixed-corank.md#removing-row-ends). Its recurrence is
$$Z_n=Z_{n-1}+\sum_{r=1}^{n-1}U_r Z_{n-r-1}+V_n.$$
On $|w|\le1/8$ each $Z_n(w)$ is nonzero and $|Z_n/Z_{n-1}-1|\le1/4$. Inductively, every inverse factor $Z_{i-1}/Z_i$ costs at most $4/3$ in modulus. Dividing the recurrence by $Z_{n-1}$ bounds the deviation from one by $\sum_{r\ge1}(4/21)^r=4/17<1/4$, using the run bound $(1/7)^r$ and $Z_0=1$. The terminal term uses only $n-1$ inverse factors.

Let $L_n(w)=\log Z_n(w)=\sum_{h\ge1}a_hw^h$ with $L_n(0)=0$. Adding the analytic logarithms of the ratios gives $|L_n(w)|\le n\log(4/3)<.29n$ on this disk. Consequently $|a_h|\le.29n\,8^h$. Put $\delta=0$ for the odd-part shape and $1$ for the even-part shape. The first three log coefficients are
$$a_1=n,\qquad a_2=-n/2+\delta,\qquad a_3=4n/3-1-\delta.$$
In fact the coefficients of $Z_n$ through degree three after the constant term are $n,\binom n2+\delta,\binom n3+(n-1)(1+\delta)$. A double deficit needs a positive next row deficit or the terminal even row. A triple deficit alone is impossible. Expanding the logarithm gives the formulas.

For $0<q\le1/100$ we have
$$\sum_{h\ge2} h^3 |a_h|q^h \le nq/6. \tag{1}$$
After division by $nq$, the second and third terms contribute at most $4q+36q^2$. The terms $h\ge4$ are bounded by the geometric majorant with first term $.29\cdot4^3 8^4 q^3$ and ratio $(5/4)^3\,8q$. At $q=1/100$ the total is less than $.14$.

Under the tilt by $q^k$ the mean is $M(q)=qL'_n(q)$, strictly increasing in $q$ since its logarithmic derivative is the variance. Set $w=nq$. From (1), $23w/24\le M(q)\le25w/24$. Thus every integer $1\le k\le n/105$ is attained as $M(q)$ at some $q\le1/100$. In the rest of this section use that choice of $q$.

## Centered inversion at the exact finite-size mean

Write the centered characteristic function as
$$e^{-ik\theta}Z_n(qe^{i\theta})/Z_n(q)=e^{-A(\theta)+iB(\theta)}.$$
For $|\theta|\le\pi$, (1) gives
$$
\tfrac{11}{12}w(1-\cos\theta)\le A(\theta)\le\tfrac{13}{24}w\theta^2,\qquad
|B(\theta)|\le\tfrac7{36}w|\theta|^3.
$$
For the lower bound use $1-\cos(h\theta)\le h^2(1-\cos\theta)$ and $\sum_{h\ge2}h^2|a_h|q^h\le w/12$. For the other two bounds use $1-\cos t\le t^2/2$ and $|\sin t-t|\le |t|^3/6$. The exact mean cancels the linear phase.

Suppose $k\ge17$, so $w\ge16$. With $x=\sqrt w\,\theta$ consider the real part times $2w(1-\cos\theta)$, integrated in $x$ from $0$ to $\pi\sqrt w$. The integrand is nonnegative up to $x=3$, since $|B|\le(7/36)27/4<\pi/2$. On $0\le x\le1.5$ the cosine of the phase exceeds $.98$, $e^{-A}>.29$, and the multiplier is at least $.95x^2$ by Taylor's inequality at $|\theta|\le.375$. This contributes more than $.30$. On $3\le x\le\pi\sqrt w/2$ the absolute contribution is at most
$$\int_3^\infty x^2 e^{-.37x^2}\,dx<.18,$$
because $1-\cos\theta\ge4\theta^2/\pi^2$ on $[0,\pi/2]$. Integration by parts bounds this integral by $e^{-9b}(3/(2b)+1/(12b^2))$ at $b=.37$. From $\theta=\pi/2$ to $\pi$ use the lower bound $A\ge11w/12$. The absolute contribution is at most $2\pi w^{3/2}e^{-11w/12}<.001$ for $w\ge16$. Thus the integral is positive. By symmetry and Fourier inversion the tilted mass at $k$ strictly exceeds the average of its two neighbors. The arithmetic-geometric mean inequality and cancellation of the tilt give strict log-concavity of $b_k$.

For $1\le k\le16$ with $n\ge105k$, we have $n\ge4(k+1)^2$. The [counting bound](fixed-corank.md#a-counting-proof-when-the-size-is-at-least-quadratic-in-the-corank) proves strict log-concavity directly. This finishes the all-size assertion.

## Joining the tilts between the sparse and peak regimes

For $n\ge10^{100}$ the remaining interval $n/105\le k\le2n$ is covered by the [bounded-tilt inversion](harmonic-small-area.md#bounded-height-scales). We justify the required range of slopes here and record a separate estimate valid at $n\ge10^{531}$. Use the real symmetric transfer operator and notation of the [effective small-area proof](effective-small-area.md#real-transfer-operator), so $F(z)=4^{-n}2^{-\delta}Z_n(e^{-z})=e_0 K_z^n W_\delta(z)$, $\lambda$ is the top eigenvalue of $K_\beta$, and $p(\beta)=\log\lambda$. The real slope $-p'(\beta)$ decreases continuously from infinity to zero on $\beta>0$. This follows from the [slope proof](monotonicity.md#3-decrease-near-the-top) with the sign of the tilt reversed.

At $\beta=8$, the slope is at most $25e^{-8}/24<1/105$. Indeed, the normalized finite means $M(e^{-\beta})/n$ converge to $-p'(\beta)$. At fixed $\beta>0$ the top eigenvalue is simple with a spectral gap and nonzero endpoint amplitude, yielding $n^{-1}\log F(\beta)\to p(\beta)$. The two secant inequalities for these convex functions then give convergence of derivatives at every differentiability point of $p$. Therefore the saddle $-p'(\beta)=k/n$ in the stated interval lies in $0<\beta\le8$.

For $\beta\le1$ the [inversion bounds](effective-small-area.md#sign-of-the-adjacent-differences) already give strict log-concavity at this saddle whenever $N=n/H^2\ge10^{470}$, $H=\beta^{-1/3}$. The restriction $k/n\ge2$ in that paper's last paragraph was used to choose a saddle below one. Here its existence in this case is given, and the real slope bound gives $H\le10^{30}k/n\le2\cdot10^{30}$. Hence the required lower bound on $N$ holds.

For clarity we give constants for $1\le\beta\le8$. With $u$ the positive unit ground state of $T_\beta$ and $u_e=\sqrt2\,u|_{\rm even}$, the [nodal cut and boundary estimates](effective-small-area.md#real-transfer-operator) give
$$
\lambda\ge1/4,\qquad\lambda_2\le e^{-\beta}\lambda,\qquad
u_0^2\ge(1-e^{-\beta/2})/(2-e^{-\beta/2})>.19 .
$$
The second bound cuts a second positive eigenvector of $T_\beta$ at its first sign change. The translated tail has norm at most $e^{-\beta/2}\rho$, and the positive eigenvalues are squared in $K_\beta$. The edge weights $w_0=2u_0^2$, $w_1=2(\rho^2-1)u_0^2$ from the same real argument give $p''\ge w_0w_1/2>10^{-5}$ because $\rho^2\ge1+e^{-\beta}$. The top amplitude $c(\beta)=e_0\Pi_\beta W_\delta(\beta)\ge u_0^2>.19$ for the top projection $\Pi_\beta$. Here both terminal vectors have coordinate at zero at least $1/2$.

On $|z-\beta|\le10^{-4}$, $\|K_z-K_\beta\|\le|z-\beta|$. Each unweighted two-step transition has action $d\ge0$ and $d e^{-(1-10^{-4})d}<1$, so row and column sums give this norm bound. The circle of radius $.02$ about $\lambda$ is at distance at least $.02$ from the real spectrum. The resolvent identity there gives an analytic rank-one projection with $\|\Pi_z-\Pi_\beta\|\le .005/(1-.005)<.006$. The eigenvalue inside the circle satisfies $|p(z)-p(\beta)|<.1$ for the local log branch. Cauchy's estimates on the disk of half the radius imply $p''(\beta)\le10^9$ and $|p'''(z)|\le10^{14}$. On the same smaller disk $|c(z)/c(\beta)|<20$ and $|c'(z)/c(\beta)|<4\cdot10^5$, since $\|W_\delta(z)\|\le3$ on the full disk by its geometric tail and $\|T_z/2\|\le1$. On $\ker\Pi_z$, a unit vector has overlap at most $.006$ with $u_e$, so $\|K_\beta x\|\le\lambda\sqrt{e^{-2}+.006^2}$. Adding the perturbation gives $\|K_z|_{\ker\Pi_z}\|<.4\lambda$. Therefore $F(z)/(c(\beta)\lambda^n)$ equals its principal term $(c(z)/c(\beta))e^{n(p(z)-p(\beta))}$ up to absolute error $40(.4)^n$.

For the rest of the circle, the two phases in the height-two diagonal have respective real weights $e^{-\beta}/4$ and $e^{-2\beta}/4$. Their modulus deficit is at least $(e^{-16}/4)\sin^2(\theta/2)$, by squaring. Also $u_e(2)=\sqrt2(\rho^2-1)e^{\beta/2}u_0>.01$. For a nonnegative unit vector at distance at least $.005$ from $u_e$, the real Rayleigh quotient loses at least $(\lambda-\lambda_2)(.005)^2/2>10^{-6}$. Every closer vector has coordinate two at least $.005$ and suffers the diagonal deficit there. Applying this to the symmetric matrix of entrywise moduli gives
$$\|K_{\beta+i\theta}\|\le\lambda-10^{-13}\sin^2(\theta/2).$$
In particular for $10^{-22}\le|\theta|\le\pi$ the power loses a factor at least as strong as $e^{-10^{-59}n}$ relative to $\lambda^n$.

For $n\ge10^{160}$ put $\sigma^2=np''(\beta)$ and $x=\sigma\theta$. In $|\theta|\le10^{-22}$, cancel the linear phase by $e^{ik\theta}$. Taylor's theorem gives principal exponent $-x^2/2$ with error at most $10^{14}n|\theta|^3/6$, so its real part is at most $-x^2/4$. For $|x|\le12$ the same error and the amplitude error $4\cdot10^5 |x|/\sigma$ are each below $.001$ using $\sigma^2\ge10^{-5}n$. The real centered principal term there is at least $.99e^{-x^2/2}$. Multiply by $4\sigma^2\sin^2(x/(2\sigma))$ and integrate in $x$. This multiplier lies between $.99x^2$ and $x^2$ on $[-12,12]$, giving a contribution greater than one. The principal tail still in the small disk costs at most $20\int_{|x|>12}x^2e^{-x^2/4}\,dx<.01$. The complementary powers and off-disk frequencies together cost at most $10^4\sigma^3((.4)^n+e^{-10^{-59}n})<.01$ by $\sigma^2\le10^9n$. The integral is positive. Inversion again gives strict negative centered second difference of the tilted mass at $k$, and hence strict log-concavity after removing the tilt.

The sparse and bounded tilts together cover $1\le k\le2n$ for $n\ge10^{100}$. At $n\ge10^{550}$ the [small-corank bound](harmonic-small-area.md) takes over at $2n$ and meets the [tilted comparison](tilted-peak.md#a-range-of-coranks-with-strict-log-concavity). The [overlap calculation](finite-reduction.md#joining-the-three-intervals) covers every interior upper-half rank.
