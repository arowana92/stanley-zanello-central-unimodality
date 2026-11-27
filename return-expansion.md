# Locating the peak to one lattice spacing

Let $b_k$ count subdiagrams of corank $k$ in the odd or even central staircase and let $P_m(k)=b_k/\binom m{\lfloor m/2\rfloor}$. The ballot word has length $m=2n$ or $2n+1$, respectively. We use the parity $\delta$ of the **strict** walk and the corresponding scale and shift
$$
L=m+1=2N+\delta,\qquad \delta\in\{0,1\},\qquad
s=(2N)^{3/2},\qquad d=(m+1+\lceil m/2\rceil)/2.
$$
Let $F,G$ be the respective densities of half the area of a unit Brownian meander and of a unit Brownian excursion. Let $x_*$ be the unique maximum point of $F$. Define
$$
\mathcal D h=-\tfrac32(h+xh'),\qquad
C_\delta=(\tfrac1{12}+\tfrac\delta2)\mathcal D F
-\tfrac1{30}(\mathcal D^2-\mathcal D)F
+(\tfrac\delta4-\tfrac3{40})(G-F).
$$

**Theorem.** Put $z_m=s(x_*-C_\delta'(x_*)/(NF''(x_*)))-d$. For some absolute $B,C$, every maximizing integer corank $k$ satisfies
$$
 |k-z_m|\le \tfrac12+C N^{-1/2}(1+\log N)^B. \tag{1}
$$
In particular, when the distance of $z_m$ from the half-integers exceeds the error term, the nearest integer is the unique maximizing corank. The excursion density enters the correction with different coefficients for the two staircases. The proof controls differences of adjacent coefficients on the peak scale. Its error constants are asymptotic and give no new finite cutoff in the [outstanding size range](README.md#asymptotic-result-and-finite-size-gap).

## Splitting at zero

Give each sign of an unrestricted walk probability $1/2$. Write $S_i$ for its height and $Y_\ell=\sum_{i=1}^{\ell} S_i/2$ for its signed area. Conditional on avoiding zero at times $1,\ldots,L$ and starting upward, translating the remaining walk down one gives the uniform ballot word of length $m$. As $\sum H_i=2k+\lceil m/2\rceil$ for its heights, $Y_L=k+d$. Reflection gives the negative branch. All possible signed areas at fixed length lie on one translate of $\mathbb Z$, since $S_i\equiv i\bmod 2$.

Fix a frequency $\theta$. Let $P^\delta_j$ denote the unrestricted transform at length $2j+\delta$, $R_j$ the unnormalized transform of paths ending at zero at time $2j$, and $U^\delta_j$ the unnormalized transform with no return by time $2j+\delta$. Empty walks are allowed in each applicable law. For convolution over the nonnegative half-length index,
$$
 P^\delta=R*U^\delta,\qquad R^{-1}=\mathbf 1_0-H,\qquad
 U^\delta_j=r_j\Phi^\delta_j,\qquad r_j=4^{-j}\binom{2j}{j}. \tag{2}
$$
Here $H_j$ restricts to first return at $2j$, $H_0=0$, and $\Phi^\delta_j$ is the conditional characteristic function. Split at the last zero for the first equation and at the first return for the second. At frequency zero, $R(z)=(1-z)^{-1/2}$, so the first-return probabilities are $q_j=r_j/(2j-1)$ for $j\ge1$ and survival up to either $2j$ or $2j+1$ is $r_j$. In particular $\sum_{j\ge1}|H_j|\le1$ at every real frequency.

The two input transforms are
$$
 P^\delta_j=\prod_{\ell=1}^{2j+\delta}\cos(\ell\theta/2),\qquad
 R_j=r_j\prod_{\ell=1}^j
 \frac{\operatorname{sinc}((j+\ell)\theta/2)}
      {\operatorname{sinc}(\ell\theta/2)},\qquad \operatorname{sinc}(u)=\sin(u)/u.
 \tag{3}
$$
The first product uses the independent signs with weights $1/2,\ldots,(2j+\delta)/2$. A bridge selects a uniform $j$-subset of the $2j$ weights to negate. The subset sum formula for the Gaussian binomial gives the sine product after centering, with removable singularities interpreted by this finite sum.

## Two continuum identities

Write $\theta=\xi/s$, $y=j/N$, and keep $\xi$ fixed in the following functions. Let $M,E$ denote the two positive Brownian half-areas and put
$$
 p(y)=e^{-\xi^2y^3/24},\quad \rho(y)=e^{-\xi^2y^3/96},\quad
 f(y)=\mathbb E\cos(\xi y^{3/2}M),\quad e(y)=\mathbb E\cos(\xi y^{3/2}E).
$$
For functions of time write
$$
 (g\star h)(y)=\frac1\pi\int_0^1
 \frac{g(yu)h(y(1-u))}{\sqrt{u(1-u)}}\,du .
$$
With primes denoting time derivatives, the continuum kernels satisfy
$$
 \rho\star f=p,\qquad \rho\star v_1=p',\qquad
 v_1(y)=f'(y)+\frac{e(y)-f(y)}{2y}. \tag{4}
$$
The quotient extends smoothly at zero. For the first identity take $j/N\to y>0$ in (2). The weights $r_i r_{j-i}$ are the mixture of $\operatorname{Bin}(j,u)$ under $du/(\pi\sqrt{u(1-u)})$, by the beta integral. Thus $i/j$ tends in law to that mixing parameter. Formula (3) gives the Gaussian free and bridge limits. The conditional strict transform tends to the meander cosine transform by the ballot walk limit. Taking limits on the interior and then letting its two endpoints approach 0 and 1 proves the identity. For the first-return law, deleting the two outside steps of a positive first return and translating down one gives a uniform nonnegative bridge. Its scaled area converges to the excursion area. [Meander limit used here](peak-rate.md#starting-height-and-meander-law) · [Caravenna and Chaumont, conditioned bridge invariance principle](https://arxiv.org/abs/1204.6148)

For bounds at small times we use $\mathbb E[Y_{2j}^2\mid \text{first return}]\le Cj^3$. Here is a uniform height estimate that also supplies all Brownian moments used below. Conditional on a positive first step, the probability of reaching $h\ge4$ by time $j$ before any return is at most $(C/h)e^{-c h^2/j}$. First reach $\lfloor h/2\rfloor$ before zero using the fair ruin probability and then climb at least $h/2$ within $j$ steps using the exponential maximal inequality. From the first hit of $h$ in that half, the probability of a first descent to zero at the prescribed final time is at most $C/j$. Indeed the first-passage formula is $h\Pr(S_t=h)/t$ with $t\ge j$, and the binomial point bound is $C t^{-1/2}e^{-c h^2/t}$. Reversing the path controls the other half. Division by $q_j$ gives a Gaussian tail for the maximum divided by $\sqrt j$ above one. Omitting the final descent and dividing by survival gives the same type of estimate for a meander. Weak convergence and these bounds give moments of every fixed order for $E,M$.

For the second identity let $a>0$ and write $\mathscr R(a),\mathscr F(a)$ for the Laplace transforms in $y$ of $\rho(y)/\sqrt{\pi y},f(y)/\sqrt{\pi y}$. The ordinary Laplace transform of $p$ is $\mathscr R\mathscr F$ by the first identity. Evaluate the reciprocal in (2) at $z=\exp(-a/N)$. The generating series of $R_j$ divided by $\sqrt N$ tends to $\mathscr R(a)$ by (3), the binomial asymptotic and dominated Riemann sums. Writing $H_j=q_j h_j$, we have
$$
 \sqrt N(1-H(z))=\sqrt{N(1-z)}+
     \sqrt N\sum_{j\ge1}q_j z^j(1-h_j).
$$
Here $q_j\sim (2\sqrt\pi j^{3/2})^{-1}$ and $h_j\to e(y)$ at $j/N\to y>0$. The height estimate bounds $|1-h_j|\le\min(2,C\xi^2(j/N)^3)$ by reflection and the cosine inequality. Consequently
$$
 \mathscr R(a)^{-1}=\sqrt a+
 \int_0^\infty e^{-ay}\frac{1-e(y)}{2\sqrt\pi y^{3/2}}\,dy .
$$
The transform of $v_1(y)/\sqrt{\pi y}$ equals $a\mathscr F(a)-1/\mathscr R(a)$. To see this write that integrand before the Laplace weight as the derivative of $(f(y)-1)/\sqrt{\pi y}$ plus $(e(y)-1)/(2\sqrt\pi y^{3/2})$. Multiplying by $\mathscr R$ yields the transform of $p'$, since $p(0)=1$. Laplace uniqueness proves (4).

## Gamma averaging and the first correction

Put $[g]_{j,c}=\mathbb E g(T/N)$ for a rate-one gamma variable of shape $j+c$. Gamma averaging and differentiation obey the identities
$$
 [g\star h]_{j,1}=\sum_{i=0}^j r_i r_{j-i}
       [g]_{i,1/2}[h]_{j-i,1/2},\qquad
 B_1(g\star h)=(B_{1/2}g)\star h+g\star (B_{1/2}h),
 \quad B_c g=yg''+cg'. \tag{5}
$$
For the first rule change to the two component times in the integral, then expand their sum to the $j$th power. For the second, the convolution of $y^a,y^b$ is $w(a,b)y^{a+b}$ with $w(a,b)=(1/2)_a(1/2)_b/(a+b)!$, where $(v)_a$ is the rising factorial. Substitution proves the rule on nonnegative integer powers. Uniform polynomial approximation of the second derivatives, integrated twice, extends it to smooth functions on each compact interval.

The following estimates hold uniformly at $0\le j\le N$ for $|\xi|\le(A\log N)^{3/2}$, with any fixed $A$ and all sufficiently large $N$. Write $O_*(N^{-b})$ for a bound $C(1+|\xi|)^D N^{-b}$ with fixed constants. Smooth functions occurring in remainders below have the same polynomial bounds on each fixed time interval for the finitely many derivatives used. In particular this holds for $f,e$ and their quotient in (4). Near zero one can differentiate $\cos\sqrt u$ at $u=\xi^2 y^3 M^2$ or $\xi^2 y^3 E^2$. All its fixed-order derivatives are bounded for $u\ge0$ by the Taylor expansion at zero and direct differentiation for $u\ge1$. The moment bounds then give polynomial bounds also in $y$ for $y\ge0$.

Expanding (3) gives $P^\delta_j=p+N^{-1}p_1+N^{-2}p_2+O_*(N^{-3})$ and $R_j/r_j=\rho+N^{-1}\rho_1+N^{-2}\rho_2+O_*(N^{-3})$, evaluated at $y=j/N$, where
$$
 p_1=p\left[-(2\delta+1)\xi^2y^2/32-\xi^4y^5/1920\right],
 \qquad \rho_1=\rho\left[-\xi^2y^2/192-\xi^4y^5/30720\right].
$$
For detail, sum $\log\cos u=-u^2/2-u^4/12-u^6/45+O(u^8)$ and $\log\operatorname{sinc}u=-u^2/6-u^4/180-u^6/2835+O(u^8)$ over the indicated arguments. The sum of the eighth powers is $O_*(N^{-3})$. Each power sum through degree six is a polynomial in $j$, so the second-order terms after exponentiation are their Gaussian times polynomials in $y,\xi$. The first log correction is $o(1)$ uniformly on this frequency range. This also gives the stated smoothness for $p_2,\rho_2$.

For $c=1/2,1$ the gamma average has the expansion
$$
 [g]_{j,c}=g(y)+N^{-1}L_c g(y)+N^{-2}J_c g(y)+O_*(N^{-3}),
$$
$$
 L_cg=cg'+yg''/2,\qquad
 J_cg=c(c+1)g''/2+(3c+2)yg'''/6+y^2g^{(4)}/8.
$$
Taylor expand through order five. The centered-about-$j$ moments follow from $e^{-uj}(1-u)^{-j-c}$ and the sixth absolute moment is $O((j+1)^3)$. One may truncate to $T\le2N+2$ since the gamma tail beyond this point, including any fixed polynomial weight in $T/N$, is exponentially small uniformly in $j$. The expansion applies to all the functions above.

In gamma averages the first corrections become
$$
 D_p=p_1-L_1p=-\tfrac8{15} B_1p+(\tfrac\delta2-\tfrac3{20})p',
 \qquad D_r=\rho_1-L_{1/2}\rho=-\tfrac8{15}B_{1/2}\rho .
$$
Thus the approximating no-return transform is
$$
 U^a_j=r_j\big([f]_{j,1/2}+N^{-1}[v]_{j,1/2}\big),\qquad
 v=-\tfrac8{15}B_{1/2} f+(\tfrac\delta2-\tfrac3{20})v_1 .
$$
Indeed $\rho\star v+D_r\star f=D_p$ by (4) and (5). For the residual $E_j=P^\delta_j-(R*U^a)_j$ this proves the stronger smooth estimate
$$
 E_j=N^{-2}g(j/N)+O_*(N^{-3}),\qquad
 \sup_{0\le y\le1}(|g(y)|+|g'(y)|)\le C(1+|\xi|)^D. \tag{6}
$$
Explicitly, represent $P^\delta_j$ through second order by the gamma averages of $p,D_p,D_{p,2}=p_2-J_1p-L_1D_p$ with weights $1,N^{-1},N^{-2}$. Use the same representation for $R_j/r_j$ with $\rho,D_r,D_{r,2}$ and index $1/2$. The first rule of (5) then gives $g=D_{p,2}-D_{r,2}\star f-D_r\star v$. Replacing $[g]_{j,1}$ by $g(j/N)$ costs $O_*(N^{-1})$ inside this coefficient. The weights $r_i r_{j-i}$ sum to one, so all discarded product errors retain order $O_*(N^{-3})$.

At the final index, inversion of (2) gives the error $E_N-\sum_{j=1}^N H_j E_{N-j}$. The tail and moment bounds on $q_j,h_j$ give
$$
 \left|1-\sum_{j=1}^N H_j\right|\le C(1+\xi^2)N^{-1/2},
 \qquad \sum_{j=1}^N j|H_j|\le C\sqrt N .
$$
Subtract $E_N$ inside the convolution and use (6) to bound $|E_{N-j}-E_N|\le C(1+|\xi|)^D(j+1)/N^3$. The resulting error is $O_*(N^{-5/2})$ before division by $r_N\asymp N^{-1/2}$. Expanding $U^a_N/r_N$ once now yields
$$
 \Phi^\delta_N(\xi/s)=f(1)+N^{-1}
 \left[(\tfrac1{12}+\tfrac\delta2)f'(1)-\tfrac1{30}f''(1)
       +(\tfrac\delta4-\tfrac3{40})(e(1)-f(1))\right]+O_*(N^{-2}). \tag{7}
$$

## Lattice inversion and the mode

The discrete meander transform has a bound $Ce^{-c|\xi|^{2/3}}$ throughout $|\xi|\le\pi s$. The shift to $k+d$, symmetrization and the bounded ratio $m^{3/2}/s$ preserve the bound. The excursion limit satisfies the same type of bound. To see this, remove the two mandatory outside steps of a positive first return at $2j$ and cut the remaining nonnegative bridge into four nearly equal blocks. The first block has total absolute mass $O(j^{-1/2})$ by survival. The second has maximum absolute row sum $Ce^{-c j|\theta|^{2/3}}$ by the killed-block bound. Every entry of the third has modulus at most $Cj^{-1/2}$ by the unrestricted binomial point bound. The final block ending at the wall has column sum of moduli $O(j^{-1/2})$ by reversal and survival. Multiplication and division by the bridge's unconditioned mass of order $j^{-3/2}$ prove the envelope. Endpoint and translation phases have modulus one. Take $j=N\to\infty$ to obtain the claimed continuum bound. [Killed-block bound on the full Fourier period](peak-rate.md#fourier-inversion-for-lattice-differences)

All fixed $\xi$-derivatives of the continuum cosine transforms inherit a stretched exponential bound with possibly smaller $c$. For derivative order $l\ge1$, a forward difference of step $h$ divided by $h^l$ differs from the derivative by at most $lh\sup|\partial_\xi^{l+1}f(1)|$, which is bounded by a moment times $lh$. Choose $h=\exp(-c'|\xi|^{2/3})$ with $(l+1)c'<c$. The difference itself divided by $h^l$ is bounded by $2^l h^{-l}$ times the envelope on the short interval. This also works for $e$. The time derivatives at $y=1$ are finite sums of $\xi$-derivatives with polynomial multipliers.

Thus (7) can be Fourier inverted, cutting at $(A\log N)^{3/2}$ with $A$ large enough that all tails, including a fixed polynomial frequency weight, are $O(N^{-3})$. On the positive axis the signed limiting densities are $F/2,G/2$. Time scaling of $F$ is $y^{-3/2}F(x/y^{3/2})$, with derivatives at $y=1$ equal to $\mathcal D F$ and $(\mathcal D^2-\mathcal D)F$. Multiplying the signed lattice probabilities by two gives $P_m$ at the sites $k+d$ for $k\ge0$. For $x=(k+d)/s$ and $x_{1/2}=(k+d+1/2)/s$ we obtain
$$
 \begin{aligned}
 sP_m(k)&=F(x)+N^{-1}C_\delta(x)+O(N^{-2}(1+\log N)^B),\\
 s^2(P_m(k+1)-P_m(k))&=F'(x_{1/2})+N^{-1}C_\delta'(x_{1/2})
                   +O(N^{-2}(1+\log N)^B).
 \end{aligned} \tag{8}
$$
These absolute errors are uniform for $k\ge0$. At the midpoint the difference multiplier is $-2is\sin(\xi/(2s))$. Its replacement by $-i\xi$ costs $O(s^{-2})$ after integration against the envelope.

Every maximizer has $x\to x_*$, and $F''(x_*)<0$ by [strong log-concavity and convergence of the maximizers](peak-window.md#curvature-of-the-limiting-density). In a fixed neighborhood of $x_*$ the function $F'+C_\delta'/N$ has derivative bounded above by a negative constant. Its unique zero there is $x_*-C_\delta'(x_*)/(NF''(x_*))+O(N^{-2})$ by Taylor's theorem. At a maximizing site the two adjacent differences have opposite weak signs. Equation (8) places the zero between their midpoints up to the absolute error divided by the derivative bound. Multiplying by $s$ gives (1).

## Sizes with a tied maximum

**Corollary.** In each family, among the first $X$ staircase sizes, at most $O(X^{5/6})$ can have more than one maximizing corank. Outside a set of that size, the unique maximum is the nearest integer to $z_m$.

For fixed $\delta$, $z_m$ as a function of $N$ has the form $aN^{3/2}+bN^{1/2}+cN+d_0$, with $a=2^{3/2}x_*>0$. Indeed $m=2N+\delta-1$ makes the centering $d$ affine at fixed parity. On $X\le N<2X$ its second derivative is bounded between positive constants times $X^{-1/2}$ for large $X$. Write $H=\lfloor X^{1/6}\rfloor$. By (1), rounding gives the unique maximizer except possibly when $\operatorname{dist}(z_m,\mathbb Z+1/2)\le C X^{-1/2}(1+\log(2X))^B<1/(2H)$. On this last neighborhood
$$
 H^{-2}\left|\sum_{u=0}^{H-1}\exp(2\pi i u(z_m-1/2))\right|^2\ge4/\pi^2
$$
by the sine formula. For $1\le h<H$, the second derivative estimate for exponential sums gives
$$
 \left|\sum_{X\le N<2X}e^{2\pi i h z_m}\right|
 \le C\big(X^{3/4}\sqrt h+X^{1/4}/\sqrt h\big).
$$
For completeness, the phase has increasing derivative and second derivative between $\lambda$ and $C\lambda$, where $\lambda\asymp h/\sqrt X$. Discard the intervals where its derivative lies within $\sqrt\lambda$ of an integer, and the unit steps crossing their ends. There are $O(X\lambda+1)$ such intervals, each of length $O(1/\sqrt\lambda)$. On each intervening interval the increments of the phase increase between two consecutive integers, staying at least $\sqrt\lambda$ from both. Summing by parts with $1/(e^{2\pi it}-1)$ at those increments costs $O(1/\sqrt\lambda)$ per interval, since the real part is constant and the imaginary part is monotone between poles. This gives $O(X\sqrt\lambda+1/\sqrt\lambda)$ as asserted.

Expanding the square and summing over $N$ bounds the exceptional count by $O(X/H+X^{3/4}\sqrt H+X^{1/4}/\sqrt H)=O(X^{5/6})$. Sum over dyadic intervals and use $N=n$ for the odd-part staircase and $N=n+1$ for the even-part staircase. This counts exceptions to the rounding rule. At an exceptional size the conjecture still allows adjacent equal maxima.

## An exact check on the correction

At fixed $k\ge1$ the coefficient of $\theta^{2k}$ in $\Phi^\delta_j(\theta)$ is a polynomial in $j$ of degree at most $3k$, at all integer $j\ge0$. To prove this, first expand the logarithms in (3) at zero. At order $2a$ their power sums have degree at most $2a+1\le 3a$, so exponentiation gives degree at most $3k$ for $P^\delta_j$ and $R_j/r_j$. The binomial mixture from (4) gives
$$
 \sum_i r_i r_{j-i}\,i^{\underline a}(j-i)^{\underline b}
 = j^{\underline{a+b}}w(a,b),
$$
where underlining denotes a falling factorial. By induction on $k$ in (2), terms involving a positive bridge order and a lower strict order therefore give polynomials of degree at most $3k$. For the remaining unknown coefficient the convolution sends $j^{\underline b}$ to $w(0,b)j^{\underline b}$. These multipliers are nonzero. The resulting polynomial solution is the actual sequence by triangular inversion of (2).

Consequently one can recover the top two coefficients of the finite moment polynomial from exact rank rows. An independent prediction comes from (4) and (7). Write $f(y)=\sum f_k \xi^{2k}y^{3k}$ and likewise for $e,\rho,p$ at the level of Taylor coefficients at zero. With $\rho_k=(-1/96)^k/k!$, compute $f_k$ by $\sum_{i=0}^k\rho_i f_{k-i}w(3i,3k-3i)=(-1/24)^k/k!$. For the excursion let $d_k$ be the formal reciprocal coefficients of $\sum_{k\ge0}\rho_k(1/2)_{3k}u^k$. Differentiating the reciprocal Laplace identity at zero gives $e_k=-2d_k/(1/2)_{3k-1}$ for $k\ge1$. Formula (7) predicts the next coefficient from $f_k,e_k$ by replacing $f'(1),f''(1)$ by $3k f_k,3k(3k-1)f_k$. This coefficient comparison can also be made formally in (3)–(7), using the exact gamma moments at each fixed order.

For example, the quadratic cosine coefficient of the half-meander is $f_1=-59/480$ and that of the half-excursion is $e_1=-5/96$. The coefficient of $\xi^2/N$ in the scaled discrete transform is $-11/960$ for $\delta=0$ and $-57/320$ for $\delta=1$.

Run the standard-library verifier with

~~~sh
python3 -B verify_return_expansion.py
~~~

Direct enumeration of strict partitions checks the input rows through $n=8$. Enumeration of all free sign words checks the entire signed convolution through $L=18$. For each parity, finite differences at $N=0,\ldots,33$ recover both predicted coefficients for every even moment of orders 2 through 20, with rational arithmetic. These tests cover constants, scaling and both parity shifts. The proof of the local estimate comes from the Fourier remainder in (6)–(8).

## Numerical values and rounding at small sizes

For orientation, $x_*\simeq0.3840394441$. The two values of $-C_\delta'(x_*)/F''(x_*)$ are approximately $0.1099874091$ for $\delta=0$ (even parts) and $0.3382014743$ for $\delta=1$ (odd parts). These are floating-point estimates. The exact constants in (1) are defined by the densities.

The [numerical script](estimate_return_peak.py) uses the Laplace transforms of the Brownian half-areas. If $-a_i$ are the negative zeros of $\mathrm{Ai}$ and $r_i^*=\int_{-a_i}^\infty\mathrm{Ai}(u)\,du/\mathrm{Ai}'(-a_i)$, they are
$$
 \mathbb E e^{-tM}=\sqrt{\pi/2}\,t^{1/3}\sum_i r_i^* e^{-a_i t^{2/3}/2},
 \qquad
 \mathbb E e^{-tE}=\sqrt{\pi/2}\,t\sum_i e^{-a_i t^{2/3}/2}.
$$
These are the area transforms at argument $t/2$ in the usual unit-area convention, continued into $\Re t>0$ with principal powers. The script integrates on two vertical lines, $\Re t=20,28$, varying the number of Airy zeros, the cutoff and the quadrature spacing. The three displayed constants agree between runs to within $10^{-9}$. The underlying Brownian area distributions and leading discrete limits are classical. [Majumdar and Comtet, §II](https://arxiv.org/pdf/cond-mat/0409566#page=3) · [Takács, *Limit distributions for the Bernoulli meander*](https://www.cambridge.org/core/journals/journal-of-applied-probability/article/abs/limit-distributions-for-the-bernoulli-meander/D396ABE2C18FDCB75D12F270EED6FFEC) · [Denisov, Kolb and Wachtel, Theorem 3 and Corollary 4](https://doi.org/10.1112/jlms/jdu078)

Running `python3 -B estimate_return_peak.py` and rounding the prediction gives a maximizing corank for 188 of the 192 shapes at $1\le n\le96$. The four misses have ballot lengths $9,36,53,183$. At $n=96$ the predicted coranks are $886.582588$ and $895.279690$ for the odd- and even-part shapes, respectively. The exact modes are at coranks 887 and 895. This experiment tests the finite-size correction separately from the moment checks.
