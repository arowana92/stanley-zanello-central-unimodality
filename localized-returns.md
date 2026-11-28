# Localizing the first-return error in the peak estimate

**Theorem.** For both central staircases and every $n\ge10^6$, the corank counts from $\lceil .145m^{3/2}\rceil$ to the end of the row are unimodal and contain all global maximizers, of which there are at most two, consecutive if tied. Here $m=2n$ for the odd-part shape and $m=2n+1$ for the even-part shape. A [positive-tilt argument](cubic-tilt.md) completes whole-row unimodality for $n\ge10^{10}$.

We use the signed walk of length $m+1=2N+\delta$, $s_0=(2N)^{3/2}$ and $d=(m+1+\lceil m/2\rceil)/2$. Its signed half-area, conditional on no return by the final time, is distributed as $\pm(k+d)$ for a random corank $k$. Write $P_m(k)$ for its positive-branch probability conditional on that branch, and $F$ for the density of half the unit Brownian meander area. At $z_0=(k+d)/s_0$ the errors in approximating $s_0P_m(k),s_0^2\Delta P_m(k),s_0^3\delta^2 P_m(k)$ by $F(z_0),F'(z_0),F''(z_0)$ satisfy the following bounds. The first difference is forward and the second is centered. Take $k\ge0$ for the first two estimates and $k\ge1$ for the third.

| Lower bound on $N$ | Density error | First-difference error | Second-difference error |
| ---: | ---: | ---: | ---: |
| $750000$ | $.0045$ | $.147$ | $10.3$ |
| $10^6$ | $.0033$ | $.101$ | $6.1$ |
| $10^{10}$ | $.000001$ | $.00002$ | $.04$ |

The last line also applies at smaller coranks. At $N\ge125000$ a separate estimate below bounds the density error by $.069$. The proof estimates errors at the time remaining after a return. A late return can leave a substantial error there but has small point probability and a decaying conditional area transform. [Previous bound with a uniform return error](return-bounds.md) · [Rational verifier](verify_local_returns.py)

## A size-uniform bound for smooth residuals

A separate kernel-checked estimate exploits cancellation in the inverse convolution. Let $N=n+\delta\ge1$, let $r_N=4^{-N}\binom{2N}{N}$, and fix the frequency $\theta$. Given a proposed series $V$, let $E_j$ be coefficient $2j+1-\delta$ in the free series minus the bridge series times $V$, evaluated at area frequency $\theta/2$. If $|E_N|\le e$, $|E_N-E_{N-j}|\le jb/N$ for $0\le j\le N$, and $|\theta|N\sqrt N\le\xi$, then the conditional signed amplitude differs from the proposed real coefficient divided by $r_N$ by at most
$
(1+\xi/2)e+b.
$
The bound holds for both parities and has no upper size cutoff. Applying it to the signs around the peak requires a trial series with certified residual and variation bounds. [Lean amplitude theorem](CentralUnimodality/SmoothBallotAmplitude.lean)

For the proof, write $p_j=r_{j-1}-r_j$ for the fair probability of a first return at time $2j$, and let $H_j$ be its unnormalized Fourier transform. Take $p_0=H_0=0$. The identity $\sum_{j=1}^N j p_j=Nr_N$ follows by induction from the central binomial recurrence. For every $j\ge1$ the unnormalized first absolute area moment of those returns is exactly $1/2$. Indeed, a positive first return encloses a Dyck path of semilength $d=j-1$. Its area equals the sum of height plus one over the $2d+1$ vertices of that inner path. At threshold $h\le d$, the number of marked vertices at height at least $h$ is $\binom{2d+1}{d-h}$. Summing these tails gives $4^d$. Reflection doubles the total, and fair weighting gives $2\cdot 4^d/4^j=1/2$. [Marked-height sum](CentralUnimodality/ExcursionFirstMoment.lean) · [First-return moment](CentralUnimodality/FirstReturnArea.lean)

Thus $|H_j-p_j|\le|\theta|/4$ at each positive return time. In the inverse convolution, collect the coefficient of $E_N$ and leave the other terms as $H_j(E_N-E_{N-j})$. The first coefficient has modulus at most $r_N+N|\theta|/4$. The remaining terms total at most $br_N$, since $|H_j|\le p_j$. Division by $r_N$ and $1/r_N\le2\sqrt N$ give the stated estimate. [Return characteristic function](CentralUnimodality/ReturnCharacterMoment.lean) · [Cancellation in the inverse](CentralUnimodality/SmoothReturnInverse.lean)

## Finite quadrature for the return split

At half-length $N$, the zero-frequency split at $2k$ has mass $w_{N,k}=r_k r_{N-k}$. With $S_Ng=\sum_{k=0}^N w_{N,k}g(k/N)$, Lean proves
$
 |S_Ag-S_Ng|\le \frac{M}{8}\left(\frac1{A-1}-\frac1{N-1}\right),\qquad 2\le A\le N ,
$
whenever the absolute first-order Taylor remainder on $[0,1]$ is at most $M(y-x)^2/2$. To see the constant, draw $k$ from the law at $N+1$. Delete one position uniformly. The number remaining is $k-1$ with probability $x=k/(N+1)$ and $k$ otherwise. The new fraction has conditional mean $x$ and variance $x(1-x)/N^2$. The recurrence for $r_k$ proves that the remaining count has law $w_{N,\cdot}$. The same deletion proves the exact polynomial integration rule
$
 \sum_{k=0}^N w_{N,k}\binom{k}{a}\binom{N-k}{b}
 =\binom N{a+b} r_a r_b .
$
[Quadrature proof](CentralUnimodality/ReturnSplitQuadrature.lean) · [Mixed binomial moments](CentralUnimodality/ReturnSplitMoments.lean)

There is also a direct bound for the true last-return residual of any real trial sequence $f$. Write $t=2N+\sigma$ with $\sigma=0,1$, let $\omega=\theta/2$ be the frequency of the integer sum of heights, and give the trial coefficient at length $2j+\sigma$ the value $r_j f(j)$. Define
$
 P_t=\omega^2 t(t+1)(2t+1)/12,\qquad Q_k=\omega^2 k^2(2k+1)/6,\qquad H_t=\sum_{i=1}^t i^4 .
$
On $|\omega|t\le1$, if $|f(j)|\le B$ for $0\le j\le N$, the complex residual differs from the real number
$
 e^{-P_t}-\sum_{k=0}^N w_{N,k}e^{-Q_k}f(N-k)
$
by at most $\omega^4(3H_t/4+8BH_N/5)$. The cosine and sinc products give the two quadratic exponents. The logarithmic errors per factor are bounded by quartic powers, and the exponential has derivative at most one on the nonpositive real axis. The zero frequency follows by counting walks with a specified endpoint. At fixed $|\omega|N^{3/2}$ and bounded $B$, this error is $O(1/N)$. Bounding the displayed quadrature and the variation of the residual at the frequencies needed for peak inversion remains necessary. [Coefficient bounds](CentralUnimodality/GaussianSymbols.lean) · [Residual bound](CentralUnimodality/GaussianResidual.lean)

## A polynomial trial on the wider frequency interval

Write $v=j\tau$, where $\tau=|\xi|^{2/3}/N$, and put $r_j=4^{-j}\binom{2j}{j}$. For a polynomial $A(x)=\sum_a A_a x^a$, let $G_{j,c}A=\sum_a A_a\tau^a(j+c)^{\overline a}$, where the superscript denotes a rising factorial. Put $h_{ab}=(1/2)^{\overline a}(1/2)^{\overline b}/(a+b)!$ and define $B\star F$ by multiplying each pair of monomials with weight $h_{ab}$. At every $N\ge0$ and every real step $\tau$, Lean proves
$$
 \sum_{k=0}^N r_kr_{N-k}\,(G_{k,1/2}B)(G_{N-k,1/2}F)
 =G_{N,1}(B\star F).
$$
For the monomial proof, apply the exact mixed binomial moment at $N+a+b$ and shift the surviving indices by $a$. Linearity gives the polynomial identity. Approximating the free symbol by $G_{N,1}P$ within $e$ and each normalized bridge by $G_{k,1/2}B$ within $d$ then bounds the discrepancy between the actual complex residual and $G_{N,1}(P-B\star F)$ by $e+d\max_{j\le N}|G_{j,1/2}F|$. [Rising moments](CentralUnimodality/GammaSplitMoments.lean) · [Polynomial identity and residual bound](CentralUnimodality/GammaPolynomialSplit.lean)

A separate inverse estimate handles a smooth model with an additional discretization error. If the true residual differs from $G(j)$ by at most $v_0$ at each $j\le N$, and $G$ satisfies the endpoint and variation bounds $e,b$ above, the conditional signed amplitude error is at most $(1+\xi/2)e+b+4\sqrt N\,v_0$. Indeed the first-return masses after time zero sum to $1-r_N$, giving the unconditioned error factor $2-r_N$. Thus a discretization error of order $1/N$ vanishes after conditioning, even without a derivative estimate for that error. [Kernel proof](CentralUnimodality/ResidualModel.lean)

For $0\le v\le256$ there is a rational certificate for five specific polynomials. Their coefficients are integers in units of $2^{-120}$ in the basis $T_i(1-2v/256)$. The free and bridge trials $P,B$ have degree at most 600. The amplitude trial $F$ and the first-correction trials $M_0,M_1$ have degree at most 420. The candidates came from cosine interpolation of the elementary exponentials, and of the moment and Airy approximations in the return expansion. All bounds below are verified from the stored integers. [Coefficient table](CentralUnimodality/PolynomialTrialData.lean) · [Independent standard-library verifier](verify_gamma_polynomials.py)

The two input polynomials approximate $p(v)=e^{-v^3/24}$ and $\rho(v)=e^{-v^3/96}$ uniformly within $10^{-21}$. To check this, put $z=v/256$, $V=256$, let $D=24$ or $96$ and compute the defect $A'(z)+(3V^3/D)z^2 A(z)$. Its maximum absolute value plus $|A(0)-1|$ bounds the solution error on $[0,1]$ by the integrating factor formula. For the corrections put $D_{P,\sigma}(v)=P(v)\big((7-2\sigma)v^2/32-v^5/120\big)$ and $D_B(v)=B(v)(v^2/24-v^5/1920)$. Exact rational bounds over the full interval are

| Polynomial | Absolute value | Absolute $v$ derivative |
| --- | ---: | ---: |
| $P-B\star F$ | $2\times10^{-15}$ | $4\times10^{-13}$ |
| $D_{P,\sigma}-B\star M_\sigma-D_B\star F$, either parity | $3\times10^{-14}$ | $6\times10^{-12}$ |

The verifier expands the convolution in monomials, converts back to Chebyshev coefficients, and sums their absolute values. The derivative uses the exact Chebyshev differentiation recurrence. It also evaluates the split independently at 33 combinations of size and step for a pair of test polynomials. Run `python3 -B verify_gamma_polynomials.py` from the checkout. These bounds certify the polynomial residual on a continuum of frequencies. Transferring them to the lattice input errors and then to adjacent coefficient signs requires further estimates.

## An unbounded lattice peak check using polynomial trials

For every strict-walk half-length $N=n+\delta\ge10^{54}$, the peak interval from `centralStart` to the three-fifths cutoff is unimodal in both staircase families. This gives a second computer-assisted proof of the peak assertion at these sizes. It uses the polynomial table above and the finite walk recurrence. Lean verifies the comparison for the concrete trial throughout the frequency interval. An independent rational quadrature verifies the spatial integrals.

Let $S=(2N)^{3/2}$, $\theta=\xi/S$, $u=|\xi|^{2/3}\le256$, $\tau=u/N$ and $\omega=\theta/2$, so $\omega^2=\tau^3/32$. Define an arcsine average by $I(g)=\pi^{-1}\int_0^\pi g(\sin^2 t)\,dt$. For any continuous trial $f$, write
$$
 R(v)=p(v)-I\big(x\mapsto\rho(vx)f(v(1-x))\big).
$$
Lean proves $I(x^a(1-x)^b)=h_{ab}$ and therefore $I(B(vx)F(v(1-x)))=(B\star F)(v)$. It also proves the binomial-mixture identity $I(\binom jk x^k(1-x)^{j-k})=r_kr_{j-k}$. The conditional binomial mean is $x$ and its variance after division by $j^2$ is $x(1-x)/j$. Taylor's theorem thus bounds the difference between the discrete split average at $j>0$ and $I$ by $M_2/(8j)$ for any integrand with second derivative bounded by $M_2$. [Angular moment identity](CentralUnimodality/ArcsineSplit.lean) · [Finite-size quadrature theorem](CentralUnimodality/ArcsineQuadrature.lean)

For either parity and $0\le j\le N$, the actual free and normalized bridge inputs are respectively within $\tau^3 N^2+\tau^6 N^5$ of $p(\tau j),\rho(\tau j)$ whenever $|\omega|(2N+1)\le1$. The quadratic exponent differs by at most $\tau^3N^2$, and the quartic remainder follows from $\sum_{i=1}^t i^4\le t^5$ and $t\le3N$. If $|f|\le M$ on $[0,u]$ and the second derivative in $x$ of $\rho(vx)f(v(1-x))$ is bounded by $K v^2$, the true residual of the trial $r_j f(\tau j)$ thus differs from $R(\tau j)$ uniformly by at most $((1+M)(u^3+u^6)+Ku^2/8)/N$. The $j=0$ quadrature is exact. The inverse theorem gives, with $e=\sup|R|$ and $L$ a Lipschitz constant for $R$ on that interval,
$$
 |\Phi_N(\xi/S)-f(u)|\le (1+|\xi|/2)e+uL+
 \frac{4}{\sqrt N}\left((1+M)(u^3+u^6)+Ku^2/8\right).
$$
Here $\Phi_N$ is the actual signed conditional amplitude. The kernel statement accepts a quadratic Taylor remainder, so it also applies when that remainder is available directly. [Lattice input estimates](CentralUnimodality/LatticeCubicInputs.lean) · [Finite amplitude theorem](CentralUnimodality/ContinuumResidual.lean)

Apply the estimate with $f=F$ from the table. The Chebyshev coefficient sums enclose $|F|,|F'|,|F''|$ by $1.881,1.342,1.600$. With $V=256$, use $|\rho'|\le V^2/32$ and $|\rho''|\le V^4/1024+V/16$. The product rule gives $K<9\,000\,000$. For an input polynomial with total ODE error $\eta$ as defined above, its derivative differs from the derivative of its cubic exponential by at most $(1/V+3V^2/D)\eta$. Finally,
$$
 R(v)=(P-B\star F)(v)+(p-P)(v)-I\big((\rho-B)(vx)F(v(1-x))\big).
$$
Use the triangle inequality, the product rule, and $0\le x,1-x\le1$ to bound its value and Lipschitz constant. The verifier uses the rational errors themselves before rounding. Including the finite-size term gives **$|\Phi_N(\xi/S)-F(|\xi|^{2/3})|<10^{-10}$ on $|\xi|\le4096$** for every $N\ge10^{54}$. The angle restriction holds since $|\omega|^2(2N+1)^2\le9V^3/(32N)$. [Independent rational calculation](verify_gamma_polynomials.py)

The Lean theorem `amplitude_4096` gives the weak bound $10^{-10}$ on the same closed interval. Its key integer calculation verifies every coefficient in the degree-1,020 polynomial $P-B\star F$. Multiplying monomials of degrees $a,b$ by $(2a)!/a!$ and $(2b)!/b!$ converts the beta product to ordinary polynomial multiplication after multiplying the output at degree $k$ by $4^k k!$. Lean checks the cleared integer identity at base $2^{14337}$ and bounds each coefficient in absolute value by less than half the base. Unique signed digits then give equality of polynomials. The resulting Chebyshev row bounds the base residual by $1.45\times10^{-15}$ and its derivative by $3.595\times10^{-13}$. The two Gaussian input errors give $e=1.5\times10^{-15}$ and $L=3.6\times10^{-13}$ for the actual continuous residual. The kernel uses $M=2$ and a quadratic remainder constant $K=18{,}000{,}000$ in the finite-size estimate. [Integer certificate](CentralUnimodality/PackedBaseResidual.lean) · [Exact convolution](CentralUnimodality/ExactTrialConvolution.lean) · [Residual estimates](CentralUnimodality/CertifiedCurveResidual.lean) · [Uniform amplitude theorem](CentralUnimodality/LargePolynomialAmplitude.lean)

For the spatial calculation let $J_N(x)=\int_0^{\pi S}\Phi_N(\xi/S)\cos(x\xi)\,d\xi$. At $x=(k+d)/S$, with $d=(3n+2\delta+1)/2$, this is a positive size-dependent constant times the number of partitions of corank $k$. Indeed the characteristic function is the mean of $\cos((k+d)\xi/S)$, and on the interval $[0,\pi]$ the product-to-sum formula kills every off-diagonal term. The difference of distinct sites and their sum are nonzero integers before scaling. At the same site the integral is $\pi/2$ since $k+d>0$. Derivatives of orders 1 and 2 come from differentiating the cosine.

The verifier substitutes $\xi=w^3$ on the retained interval. On $0\le w\le8$ it applies composite Simpson quadrature with spacing $1/256$ to $3w^{3r+2}F(w^2)\cos(xw^3+r\pi/2)$, where $r=1,2$. On each unit interval it restricts the Chebyshev polynomial exactly to the corresponding range of $w^2$ and bounds the first four derivatives. Expanding $(w+h)^{3r+2}$, $F(w^2+2wh+h^2)$ and the phase exponential to order four gives the fourth-derivative bound by the product rule. The integrated and endpoint remainders of the cubic Taylor expansion about the midpoint of each two-step panel together cost at most $\|\partial_w^4\|_\infty h^4/45$ per unit interval. On $8\le w\le16$ the verifier uses the Chebyshev bound for $F$ restricted to $[64,256]$.

The spatial grid has spacing $1/H$, $H=4096$. The floor and ceiling nodes enclosing each interval are included. The linear interpolation cost is at most $\sup|\partial_x^{r+2}J|/(8H^2)$ for the low-frequency trial piece, bounded by the absolute frequency integral there. For phase arithmetic write $D=2^{120}$. At a frequency node $k$ the mesh rotation angle is $(k/256)^3/H\le1/8$. Taylor's polynomial through degree 28 and a single floor put each rotation coordinate within $2/D$ of its true value. If the current complex error is at most one then its computed modulus is at most two. Multiplication by the rotation increases the error by at most $2(2\sqrt2)/D+\sqrt2/D<8/D$, including both output floors. Thus every phase error is below $8H/D$. Horner evaluation at the dyadic area node rounds the trial just once, within $1/D$.

The amplitude replacement on $[0,4096]$ costs at most $10^{-10}4096^{r+1}/(r+1)$. From there to $.008S$ the kernel bound is $100e^{-.157u}$. At $r\le2$ its integral costs at most $150\cdot256^4 e^{-.157\cdot256}/(.157-4/256)$ using $(256+y)^4\le256^4e^{4y/256}$. On $.008S\le\xi\le\pi S$, the 216-step killed-walk bound is at most $16e^{2-N/200}$, and $\pi S\le12N^2$. The two omitted arcs together cost less than $.001$. [Frequency bounds](CentralUnimodality/SignedArcBounds.lean) · [216-step constant](CentralUnimodality/KilledProducts.lean)

| Quantity | Spatial interval | Lower bound throughout the interval |
| --- | --- | ---: |
| $J_N'$ | $[.1359,.339]$ | $.216$ |
| $-J_N''$ | $[.333,.404]$ | $162.58$ |
| $-J_N'$ | $[.398,.631]$ | $2.681$ |

The margins are rounded down after every allowance. The derivative decreases strictly across the middle interval and has opposite signs at its ends, giving a unique maximum there. Sampling this function on a lattice gives a weakly unimodal row on the covered interval. At these sizes the corank window in `ThreeFifthsPeak` lies inside the three spatial intervals. In fact $m=2N-\delta$, $d=(3N-\delta+1)/2$, the lower corank is $\lceil .1375m^{3/2}\rceil$ and the upper corank is at most $.6m^{3/2}$. The scaled endpoints lie between $.1375(1-1/(2N))^2$ and $.6+(3N+1)/(2S)$, inside $[.1359,.631]$. This proves the stated peak assertion. The threshold $10^{54}$ comes from the coarse uniform discretization bound and leaves the intermediate sizes to the earlier proof. The two numerical verifiers run with the Python standard library.

~~~sh
python3 -B verify_gamma_polynomials.py
python3 -B verify_polynomial_peak.py
~~~

The coefficient table is shared between the Python verifiers and Lean. Lean derives both Chebyshev derivative rows and checks $|F|,|F'|,|F''|\le2$ over $[0,256]$. It checks both Gaussian equation defects in the unit variable to within $10^{-22}$ and the initial errors to within $10^{-22}$. Multiplying by $e^{v^3/D}$ and bounding the derivative on $[0,v]$ proves both input values accurate to $2\times10^{-22}$. The free and bridge derivative errors are at most $2\times10^{-18}$ and $5\times10^{-19}$ respectively. The numerical constants in the Python calculation above come from its own evaluation of the same table. [Derivative certificates](CentralUnimodality/PolynomialTrialBounds.lean) · [Exact differential-equation checks](CentralUnimodality/PolynomialGaussianDefect.lean) · [Uniform Gaussian comparison](CentralUnimodality/PolynomialGaussianInputs.lean)

Lean also proves the exact continuous inversion formula at every positive lattice site, including the normalization $\pi S/(2\,\text{mass})$, and the integral formula for every spatial derivative. The three fixed sign intervals above imply `ThreeFifthsPeak` at every $n\ge300000$. Indeed a strict fall followed by a strict rise would give two ordered points where the derivative is first negative and then positive. Both points would be inside the middle interval where the derivative is nonincreasing. This argument applies directly to the original rank counts. The spatial integral inequalities remain to be verified in Lean. [Continuous lattice inversion](CentralUnimodality/ContinuousRankInversion.lean) · [Spatial signs and rank comparisons](CentralUnimodality/IntegralPeakSigns.lean) · [Exact interval for the induction](CentralUnimodality/IntegralPeakWindow.lean)

## Integrating the trial exactly on the central arc

There is a second rational verification of the three spatial signs. On $0\le\xi\le512$ expand $\cos(x\xi+r\pi/2)$ in $x\xi$ through degree 1024. On all three intervals $|x\xi|\le324$, so the factorial remainder is at most $324^{1025}/1025!<10^{-30}$. Write $F(v)=2^{-120}\sum_i a_i(v/256)^i$. With $\xi=512t^3$ the integral of $\xi^{r+j}F(\xi^{2/3})$ is exactly
$$
 \frac{3\,512^{r+j+1}}{2^{120}}
 \sum_i \frac{a_i4^{-i}}{3(r+j+1)+2i}.
$$
The coefficient of $x^j$ in the integrated Taylor polynomial is this moment times $\cos((r+j)\pi/2)/j!$. Lean proves this formula from the monomial antiderivative and bounds the absolute integrated truncation error by $10^{-15}$ for $r\le2$. [Exact moments](CentralUnimodality/CompactTrialMoments.lean) · [Spatial polynomial](CentralUnimodality/IntegratedTaylorRow.lean) · [Change of variable and error](CentralUnimodality/CompactPhaseIntegral.lean)

On $[l/q,h/q]$ the rational verifier substitutes $x=(l+ht)/(q(1+t))$, clears the denominator, and checks each coefficient of the resulting polynomial. Positive coefficients certify a positive value for all $t\ge0$. The leading coefficient gives the right endpoint. Subtracting a rational margin before substitution gives signed lower bounds $1/8$, $128$, and $2$ on the three intervals in their spatial order. The same test on nine intervals covering $64\le v\le256$ gives $|F(v)|\le10^{-14}$ and covers the rest of the trial integral through $\xi=4096$. Including the lattice approximation and the full-period tail gives margins greater than $0.1241$, $125.709$, and $1.9991$, respectively. Run `python3 -B verify_polynomial_integral.py` from the checkout. [Independent sign calculation](verify_polynomial_integral.py) · [Interval sign test](CentralUnimodality/IntervalPolynomialSigns.lean) · [Kernel bound for the full-period error](CentralUnimodality/SpatialTrialTransfer.lean)

Lean certifies the stronger compact margins $1/5$, $160$, and $2$ for these three sign intervals. To check the 514 moments together, let $w_j$ be the integer weights after clearing the powers of four, let $L=\operatorname{lcm}(1,\ldots,4000)$, and extend $w_j$ by zero outside its row. For $s=0,1,2$ form polynomials whose coefficients are $W_{s,k}=w_{3(140-k)+s}$ for $0\le k\le140$ and $Q_{s,t}=L/(6t+3+2s)$ for $0\le t\le653$. Every denominator is at most 3925 and divides $L$. The coefficient of degree $h+140$ in $\sum_s W_s Q_s$ is the cleared reciprocal sum for moment $h$, for every $0\le h<514$. Lean evaluates the three products at $2^{8193}$ and proves that the absolute value of every coefficient is below $2^{8192}$. Their centered digits therefore recover the exact signed coefficients. Applying the three interval tests to the resulting Taylor rows gives the central peak comparison for both families at every $N\ge10^{54}$. [Three-product identity](CentralUnimodality/StridedSpatialMoments.lean) · [Integer verification](CentralUnimodality/SpatialMomentProducts.lean) · [Peak theorem](CentralUnimodality/UnboundedPolynomialPeak.lean)

<a id="a-direct-polynomial-peak-certificate-from-300000"></a>

## A direct polynomial peak certificate from 150,000

For every half-length $N=n+\delta\ge150000$, the first spatial derivative for both staircase laws is positive on $[.1359,.339]$ and negative on $[.398,.631]$. The second derivative is negative on $[.333,.404]$. These three signs cover the induction's central interval for every $n\ge150000$, including the change of its starting corank at $n=300000$. Computing the two weighted Fourier errors from the dyadic trial gives upper bounds $0.173166$ and $21.159$ in the independent Python implementation. The three full-period sign margins exceed $0.022011$, $132.233662$, and $1.822011$, respectively. Run `python3 -B verify_direct_peak.py` from the checkout. [Verifier](verify_direct_peak.py) · [Rank comparison](CentralUnimodality/IntegralPeakWindow.lean)

On $0\le u=|\xi|^{2/3}\le114$ use the corrected split and keep the Fourier decay of the first return in its inverse. The time step is at most $114/150000<1/1250$ and the largest trigonometric argument is below $9/8$. On $114\le u\le144$ the signed staircase amplitude is bounded directly by $100e^{-.186u}$ and the polynomial trial by $10^{-14}$. The square-root brackets used in the Lean tables have width $10^{-9}$. [Frequency scaling](CentralUnimodality/PeakFrequencyScale.lean) · [Outer retained cells](CentralUnimodality/TruncatedCellEnvelope.lean) · [First-return discount](CentralUnimodality/ReturnFrequencyBins.lean)

### The corrected split

Let $I$ denote arcsine expectation in $x$ and $S_j$ the discrete split at half-length $j$. Under $I$, draw $K$ conditionally with the binomial law of parameters $j,x$. Then $K/j$ has law $S_j$ for $j>0$. Put $q=x(1-x)$. The second, third and fourth central moments of $K$ are $jq$, $jq(1-2x)$ and $3j^2q^2+jq(1-6q)$. In particular $\mathbb E[(K/j-x)^4]\le3/(16j^2)$, using $3q^2\le3/16$ and $q-3q^2\le3/16$. Taylor expansion through the cubic gives
$$
 \left|S_j g-Ig-\frac1{2j}I[q g'']\right|
 \le \frac{\|g'''\|_\infty/24+\|g^{(4)}\|_\infty/128}{j^2}.
$$
The norms are on $[0,1]$. The quadratic Taylor inequality gives $|S_jg-Ig|\le\|g''\|_\infty/(8j)$. [Binomial moments](CentralUnimodality/BinomialFourthMoment.lean) · [Corrected quadrature](CentralUnimodality/CorrectedArcsineQuadrature.lean)

Set $v=j\tau$, $\tau=u/N$, and $L_c A=cA'+v A''/2$. For polynomials $B,F$, write $g_v(x)=B(vx)F(v(1-x))$ and $H=B\star F=Ig_v$. Differentiating in $v$ and applying $I[(2x-1)d]=2I[qd']$ gives
$$
 I[qg_v'']=2v\{L_1 H-(L_{1/2}B)\star F-B\star(L_{1/2}F)\}.
$$
The integration by parts uses $x=\sin^2t$ and the vanishing of $\sin t\cos t$ at both endpoints. The first correction to $H$ in $S_jg_v$ is therefore $\tau$ times the expression in braces. If $|g_v^{(s)}|\le v^sD_s$ for $s=3,4$, the remaining error is at most $\tau^2(vD_3/24+v^2D_4/128)$. [Arcsine identities](CentralUnimodality/ArcsineDifferentiation.lean) · [Differential identity](CentralUnimodality/SplitFirstCorrection.lean) · [Lattice-scaled estimate](CentralUnimodality/SmoothSplitQuadrature.lean)

### A second correction to the discrete split

For $j\ge1$, let $X$ have the arcsine law on $[0,1]$ and let $K$ conditional on $X=x$ have the binomial law with parameters $j,x$. Write $I$ for expectation over $X$ and $S_jg=\mathbb E[g(K/j)]$. Put $q=x(1-x)$. If $g$ has six continuous derivatives and $M_r$ bounds $|g^{(r)}|$ on $[0,1]$, then
$
\left|S_jg-I\left[g+\frac{qg''}{2j}
 +\frac{1}{j^2}\left(\frac{q(1-2x)g'''}6+\frac{q^2g^{(4)}}8\right)\right]\right|
 \le \frac{1}{j^3}\left(\frac{M_4}{96}+\frac{M_5}{192}+\frac{M_6}{1440}\right).
$
The same inequality holds before the arcsine integration at each $x\in[0,1]$. In the quintic Taylor expansion at $x$, the exact fourth centered moment leaves the term $q(1-6q)g^{(4)}(x)/(24j^3)$. The fifth centered moment satisfies $|\mathbb E[(K-jx)^5\mid X=x]|\le5j^2/8$. The sixth centered moment is at most $j^3/2$. These two bounds control the fifth Taylor coefficient and the sixth-order remainder. [Centered moment identities and bounds](CentralUnimodality/BinomialSixthMoment.lean) · [Taylor estimate and arcsine integration](CentralUnimodality/SecondOrderQuadrature.lean)

For the staircase split $g(x)=B(vx)F(v(1-x))$, let $v=j\tau$ and bound $|g^{(r)}(x)|$ by $v^rD_r$. The right side becomes $\tau^3(vD_4/96+v^2D_5/192+v^3D_6/1440)$. This isolates a signed term of order $\tau^2$ before first-return inversion. A further reduction of the peak cutoff using this estimate needs the corresponding second corrections to the free and bridge symbols and bounds on the resulting spatial errors. [Lattice-scaled theorem](CentralUnimodality/SecondOrderQuadrature.lean)

### The residual at each time

Use $p=e^{-v^3/24}$, $b=e^{-v^3/96}$, $p_1=-\ell_p p$, $b_1=-\ell_b b$, with the log coefficients below. The signed trial at time $j$ is $r_j(F(v)+\tau G(v))$, where $G=M_\sigma+L_{1/2}F$ uses the correction for walk parity $\sigma$. Its residual is $R_0(v)+\tau R_1(v)+O(\tau^2)$ with $R_0=p-b\star F$. The earlier smooth-residual estimate gives $|R_0|\le1.5\,10^{-15}$ and Lipschitz constant $3.6\,10^{-13}$.

First replace $p,b$ by the polynomials $P,B$. With $P_1=-\ell_p P$ and $B_1=-\ell_b B$, the polynomial first residual is exactly
$$
 P_1-L_1(B\star F)-(B_1-L_{1/2}B)\star F-B\star M_\sigma .
$$
The corrected-split identity cancels the two copies of $B\star L_{1/2}F$. For the true symbols the first residual before that identity is $p_1-b_1\star F-b\star G-(v/2)I[q(b'' F-2b'F'+bF'')]$, where the two factor arguments are $vx$ and $v(1-x)$. The transfer cost follows from Gaussian errors through derivative two, $q\le1/4$, and the Chebyshev coefficient norms of $F,F',F''$ and $G$. The Gaussian ODE $b'+(v^2/32)b=0$ and the differentiated polynomial ODE defect bound the second error. In both parities the polynomial norm is below $2.852\,10^{-12}$ and the transfer allowance below $9.06\,10^{-16}$. [Exact residual calculation](verify_split_correction.py)

For the order-$\tau^2$ remainder use half-unit bins. Write $D_s(A,C)$ for a bound on $\sum_{h=0}^s\binom{s}{h}|A^{(h)}(vx)C^{(s-h)}(v(1-x))|$ at every split of every $v$ in a bin. The bounds $E_p,E_b$ for $|W-(g+\tau g_1)|/\tau^2$ are the log-product bounds in the next section. The largest trigonometric argument is below $1.116$. The verifier checks the sixth-order constants $.05,.001$ against the first Euler-product zeros. Add the following four bounds to $E_p$, taking their suprema separately over possible splits.

- The lattice product remainder is $E_b(|F|+\tau_*|G|)+|b_1G|$, where $\tau_*=1/1250$.
- Applying the leading quadrature to the order-$\tau$ terms costs $v[D_2(b_1,F)+D_2(b,G)]/8$.
- The cubic contribution to the corrected leading split is $vD_3(b,F)/24$.
- The fourth-order remainder is $v^2D_4(b,F)/128$.

Denote the resulting bound in bin $i$ by $E_i$. At $j=0$ the split is evaluation at zero and both quadrature errors vanish. For a half-unit bin of index $a$, substitute $z=v/256=(2a+1+t)/1024$, $|t|\le1$. Absolute coefficient sums after differentiation give rigorous polynomial derivative bounds there. If $v$ lies in bin $i$, the two factor indices sum to $i$ or $i-1$. Half-open bins suffice under the final integral.

### Inversion and the three signs

Split the inverse first-return sum at $j=N/20$. For $u\in[i\Delta,(i+1)\Delta)$, $\Delta=1/2$, the endpoint and early returns together contribute at most
$$
 2\sqrt N\,\tau^2(E_i+\max_{\lfloor.95i\rfloor\le k\le i}E_k).
$$
For later $j$, the recurrence for $r_j$ makes $\sqrt j\,r_j$ nondecreasing. Thus $q_j=r_j/(2j-1)$ satisfies $q_j/r_N\le.501/[N(j/N)^{3/2}]$. If the remaining time lies in bin $k$ and $a=i\Delta>0$, then $j/N\ge p_k=\max(.05,1-(k+1)\Delta/a)$ and the bin contains at most $N\Delta/a+1$ possible indices. The elapsed rescaled time is at least $(i-k-1)/2$. The conditional first-return bound $125e^{-.15uj/N}$ gives the rational factor $d_{ik}=\min(1,125/2^{\lfloor\max(0,i-k-1)/10\rfloor})$, since $e^{.75}>2$. Add $\tau^2(.501)(\Delta/a+1/N)p_k^{-3/2}d_{ik}E_k$ for each $k\le\lfloor.95(i+1)\rfloor$. In the first bin the early estimate covers every return. The smooth residual costs $(1+|\xi|/2)\|R_0\|+u\operatorname{Lip}(R_0)$, the first correction costs $4\sqrt N\tau\|R_1\|$, and removing the final trial correction costs $\tau |G(u)|$. After inserting $\tau=u/N$, each size-dependent upper bound decreases with $N$. [Pointwise inverse and mass ratio](CentralUnimodality/LocalizedInverse.lean)

Integrate using $\xi^r\,d\xi=(3/2)\sqrt u\,u^{3r/2}\,du$. The retained errors through $\xi=1728$ are below $.176$ and $148.4$ for orders one and two. From $1728$ to $.008S$, put $t=\xi^{1/3}$. The derivative of $-1200t^{3r+1}e^{-.157t^2}$ dominates $300t^{3r+2}e^{-.157t^2}$ for $t\ge12$ and $r\le2$. The remaining arc to $\pi S$ costs at most $.001$ by the twenty-second term of the exponential series. The integrated Taylor polynomial has respective signed margins $1/5,160,2$. The trial tail and the compact Taylor remainder are included in the verifier. [Inner arc](CentralUnimodality/ModerateFrequencyTail.lean) · [Outer arc](CentralUnimodality/SpatialOuterTail.lean) · [Full rational check](verify_direct_peak.py)

Lean now proves the pointwise input bounds for the actual cosine and bridge products throughout the retained arc at every $N\ge300000$. On $0\le x\le9/8$ it proves that $-\log\cos x-x^2/2-x^4/12$ and $-\log\operatorname{sinc}x-x^2/6-x^4/180$ are increasing, with upper bounds $x^6/20$ and $x^6/1000$. Taylor envelopes for sine and cosine through degree nine reduce the differentiated inequalities to five integer polynomial sign tests on $0\le x^2\le4/3$. The bridge identity $\operatorname{sinc}(2x)=\operatorname{sinc}(x)\cos x$ makes the difference of the two bridge losses nonnegative. Summing the powers and exponentiating gives the two $E_p,E_b$ formulas above including time zero. [Log losses](CentralUnimodality/QuarticLogLosses.lean) · [Scaled remainders](CentralUnimodality/ScaledQuarticInputs.lean) · [Actual input symbols](CentralUnimodality/RetainedLatticeSymbols.lean)

For arbitrary smooth trial functions $F,G$, the theorem `direct_corrected_residual` proves the local bound $\tau^2 E_i$ for the true discrete residual after subtracting $R_0+\tau R_1$. Its hypotheses are the local derivative and product bounds specified above. The kernel also checks the inverse mass estimate and both omitted-arc bounds. The first-correction polynomial certificate, the local numerical bounds and their propagation through inversion and integration at $N\ge300000$ are outstanding in Lean. [Local residual theorem](CentralUnimodality/DirectCorrectedResidual.lean)

## Local bounds for the input symbols

We give the details of the discretization so that each inequality between mesh points is specified. Use the [last-return identity, equations (2)–(5)](return-expansion.md#splitting-at-zero) and the [corrected input approximation](return-bounds.md#a-bound-for-the-signed-transform). Put $u=|\xi|^{2/3}$ for $\theta=\xi/s_0$, $\tau=u/N$, $v=j\tau$, and use $0\le u\le U$, $U=150,160,180$ in the respective rows. Here $\tau\le\tau_*=1/5000$, and all cosine and sinc arguments have modulus below $.8$. Write $[g]_{j,c}=\mathbb E g(\tau T)$ for gamma shape $j+c$, rate one. Recall the free and bridge continuum functions $p=e^{-v^3/24}$, $\rho=e^{-v^3/96}$ and the corrections $D_g=-g\ell_g-cg'-vg''/2$ from the cited approximation. The inputs $W_j$ are the free transform ($g=p,c=1$) and the transform conditional on a bridge ($g=\rho,c=1/2$).

Divide the time variable into half-unit bins $[a,b]$. For the suprema on a bin of any polynomial times $e^{-v^3/B}$ the verifier bounds each unsigned monomial separately. Its maximum is at the nearer endpoint if its unique maximum point $(jB/3)^{1/3}$ is outside the bin, or at that point if it is inside, for monomial degree $j>0$. Constants are bounded at the left endpoint.

The quadratic and quartic log terms are those of the preceding proof. The remaining positive log series are bounded on this larger argument range by $.05x^6$ for cosine and $.001x^6$ for sinc. From the Euler products the sixth and higher terms divided by $x^6$ are at most the quartic coefficient times $2/(3(\alpha^2-x^2))$, where $\alpha$ is the first positive zero. Summing the squares exactly and using the quartic and sixth power sums gives
$$
 0\le -\log W_j+\log g(v)-\tau\ell_g(v)\le \tau^2 L_g(b),
$$
$$
 L_p(b)=13b/192+\tau_*/64+(b+\tau_*)^4/384+.05(b+\tau_*)^7/1792,
$$
$$
 L_\rho(b)=(7b^4+2\tau_* b^3)/(180\cdot32^2)+.001(b+\tau_*)^7/1792.
$$
For the last two bounds the numerator sixth-power sum is at most $(2j+2)^7/7$ before multiplying by $\tau^9/32^3$. Thus the cost of the lattice expansion divided by $\tau^2$ is at most $L_g(b)g(a)+\|g\ell_g^2\|_{[a,b]}/2$.

For gamma averaging use $I=[a,b]$, $W=[\max(0,.9a-.5),1.1b+.5]$, and take sup norms on the indicated intervals. Taylor's formula gives the following additional cost in units $\tau^2$:
$$
 \tfrac12 c(c+1)\|g''\|_I+
 \tfrac16((2+3c)b+6\tau_*)\|g'''\|_I+
 \tfrac1{24}(3b^2+26b\tau_*+24\tau_*^2)\|g^{(4)}\|_W
 +c\|D_g'\|_I+\tfrac12(b+2\tau_*)\|D_g''\|_W+10^{-16}.
$$
Indeed the first four moments about $j$ are bounded as in the previous proof. With probability at least $1-3e^{-.004j-.03/\tau}$ one has $|\tau(T-j)|\le .1v+.5$, by the centered gamma transform at $\pm .06$. Only the Taylor remainders use $W$. Off that event apply Cauchy–Schwarz and $\mathbb E|T-j|^8\le2^8(j+8)^8$, from the gamma moments. The global fourth and correction-second derivative norms are below 100. The exceptional terms are bounded by $10^4\tau_*(8+4/.002)^4 e^{-.015/\tau_*}<10^{-16}$ by maximizing the polynomial times $e^{-.002j}$. The same exception allowance covers each gamma average of the bounded $D_\rho,f,V_\delta$ below. At $\tau=0$ take the exact values.

## Meander and excursion factors

Let $f(v)=\mathbb E\cos(v^{3/2}Y)$ and $e(v)=\mathbb E\cos(v^{3/2}Y_E)$ for the Brownian half-areas of the meander and excursion. Set $Q_0=(e-f)/(2v)$, extended at zero, and $V_\delta=-8(vf''+f'/2)/15+(\delta/2-3/20)(f'+Q_0)$. For small $v$ use the [second-moment estimates](return-bounds.md#bounds-from-the-brownian-area-transforms) $|f|\le1$, $|f'|\le.75\sqrt v$, $|f''|\le.75v$, $|Q_0|\le\min(.5,v^2/8,1/v)$.

For $v\ge4$, let $S_p=\sum_j(1+a_j)a_j^p e^{-a_jv/4}$ for the positive Dirichlet Airy energies. Isolate the ground energy in $(2.337,2.339)$ and use $a_2>b_0=3.837$, with the [nodal proof and counting estimate](return-bounds.md#height-of-a-positively-tilted-meander-density). For $0\le p\le2$ one has
$$
 S_p\le (1+2.339)(2.339)^p e^{-2.337v/4}+ e^{-b_0v/4}
 \int_0^\infty(1+x)x^p(1+x^2/3)e^{-w}\,dw,\qquad x=b_0+w .
$$
Indeed after extracting $e^{-b_0v/4}$ reduce the remaining rate to one. Integrate the counting function by parts, dropping the derivative of the positive polynomial from its upper bound. The weight is decreasing on $[b_0,\infty)$. The integral of each $w^j$ against this exponential is $j!$.

Termwise differentiation in the [two Airy transforms](return-bounds.md#bounds-from-the-brownian-area-transforms) now gives
$$
\begin{aligned}
 |f|&\le1.26\sqrt v\,S_0,\quad
 |f'|\le.63(v^{-1/2}S_0+\sqrt v\,S_1),\\
 |f''|&\le1.26(S_0/(4v^{3/2})+S_1/(2\sqrt v)+\sqrt v\,S_2/4),\quad
 |Q_0|\le.63(v^{-1/2}+\sqrt v)S_0.
\end{aligned}
$$
Take the better estimate on every bin where both apply. The linear formula bounds $|V_\delta|$ for either parity, with global bound 205 from the earlier proof.

## The inverse sum over return times

For $i=\lfloor v/\Delta\rfloor$, $\Delta=1/2$, let $P_i,B_i$ bound the free and bridge input errors in units $\tau^2$ as above. For the free bound take the larger cost over the two parities. On the enlarged bin $W$ let $D_i,V_i$ bound the absolute gamma averages of $D_\rho,V_\delta$, using the exceptional allowance. Bound $[f+\tau V_\delta]$ there by $M_i=\|f\|_W+10^{-16}+\tau_* V_i$. A bound in units $\tau^2$ for the unnormalized residual at $j$ is
$$
 E_i=P_i+\max_{h+l\in\{i-1,i\}}\{ B_h M_l+D_h V_l\},\qquad h,l\ge0 .
$$
The free and bridge gamma convolutions and their first-order terms cancel exactly by [(4)–(5) of the last-return proof](return-expansion.md#gamma-averaging-and-the-first-correction). The remaining convolution weights sum to one. The two possible sums of bin indices account for every split of $v$.

Let $u\in[i\Delta,(i+1)\Delta]=[a,b]$. Apply the convolution inverse $1-H$, with $H_j$ the unnormalized first-return transform at time $2j$. The residual at $N$ and the returns at $j\le N/20$ cost in total at most
$$
 2\sqrt N\,(b/N)^2\left(E_i+\max_{\lfloor.95i\rfloor\le t\le i} E_t\right)
$$
in the normalized signed transform. This uses $1/r_N\le2\sqrt N$ and $\sum_j|H_j|\le1$. Bins may be taken half-open throughout, with the last endpoint handled by continuity. For $i=0$ the same bin contains all remaining times and the displayed bound covers the whole inverse.

For $i>0$ and $j>N/20$, put $(N-j)\tau$ in bin $t$, $0\le t\le\lfloor.95(i+1)\rfloor$. There are at most $N\Delta/a+1$ such indices per bin. The absolute first-return probability is $q_j=r_j/(2j-1)$, so $q_j/r_N\le1.01(N/j)^{3/2}/N$ by Wallis at $j>N/20\ge37500$. Below we prove $|H_j|/q_j\le\min(1,240 e^{-.13uj/N})$ on the retained Fourier arc. Thus the additional error per bin is at most
$$
 (b/N)^2 (\Delta/a+1/N)\,1.01\,p^{-3/2}\min(1,240 e^{-.13 w})E_t,\qquad
 p=\max(.05,1-(t+1)\Delta/a),\quad w=\max(.05a,a-(t+1)\Delta).
$$

Finally remove the gamma averaging at index $N$. Taylor expand $f$ about $u$ and use the bounds $M_1,M_2,M_V$ for $|f'|,|f''|,|V_\delta|$ on $[.98a,1.02b]$. This costs at most $(b/N)(M_1/2+(1+1/N)bM_2/2+M_V)+N^{-2}$, as in the [previous inversion](return-bounds.md#inversion-and-the-peak). The exceptional gamma probability is at most $3e^{-N/6000}$ using $\pm.015$ in the transform. Cauchy–Schwarz for the linear term costs less than $2\cdot10^6 e^{-N/12000}<N^{-2}$ including the other bounded terms. For order $l=0,1,2$ multiply the sum of the inverse and averaging errors on each bin by $(3/2)\Delta\sqrt b\,(b^{3/2})^l$, then sum and multiply by $2/\pi$. This is the integral against $\xi^l d\xi$ with both signs of frequency and both branches of area accounted for. Every term with a negative power of $N$ decreases from the stated lower endpoint.

## Fourier bounds on the larger arc

For $0<|\theta|\le.001$, a fair killed block of length $L=\lceil9|\theta|^{-2/3}\rceil$ has maximum absolute row sum at most $e^{-.166L|\theta|^{2/3}}$. In the [first-hit block calculation](prefix-clock.md#a-fourier-block-stopped-at-its-first-hit) one now has $L\ge900$, $L|\theta|/2\le.451$, and the sine-square factor is at least $.93$ of the squared argument. Thus the unrestricted row bound at length $t\le L$ is $\exp[-.93(t^3-t)\theta^2/96]$. For a first hit at $t\ge90$ the binomial point bound in that calculation gives $\sup_h h\Pr(S_t=h)<.5$. Split hit times at $L/10$ and into the ninety intervals $(aL,bL]$ of width $.01L$ thereafter. The probability in each such interval is at most $.5(.005+1/900)/a$ on the single allowed parity. With $c=.93\cdot 9^3/96$, the block norm is bounded by
$$
 e^{.00001}\left(e^{-c}+e^{-c(.9)^3}
  +\sum_{(a,b]} .5(.005+1/900)e^{-c(1-b)^3}/a\right).
$$
Here $L\theta^2/96<.00001$ and $L|\theta|^{2/3}\le9.01$. The rational check gives the claimed block decay. Keeping the fair prefix of length $\lfloor m/64\rfloor$ as before costs at most 16 in survival ratio. Whole blocks in the suffix, with at most one block of rounding loss, give $100e^{-.162u}$ at our scale for the signed meander. The limiting meander inherits the bound and also satisfies the earlier rate $.19$.

For a first return at $2j$, remove the two exterior steps and translate the positive interior down one. It becomes a uniform nonnegative bridge of length $2j-2$, with an area phase of constant modulus one from the shift. Reflection bounds the signed transform by the same modulus. Set $b'=\lfloor(2j-2)/16\rfloor$. Keep a boundary segment of length $b'$ at each end, and a segment of that length immediately before the terminal boundary segment. The first segment and the reversed last have survival masses at most $1/\sqrt{b'}$. Each transition entry of the other short segment has modulus at most $1/\sqrt{b'}$ by the fair binomial point bound. On the remaining steps multiply complete killed-block row bounds. Divide by the nonnegative bridge mass $r_{j-1}/j\ge1/(2j^{3/2})$. Since $b'>.124j$ for $j>N/20$ and the middle has at least $13(2j-2)/16$ steps, this gives $240 e^{-.13uj/N}$ as used above.

Beyond $U$ integrate the two transforms with $100e^{-.162u}$ through $|\theta|=.001$ and on the full continuum tail. Beyond that lattice frequency use the earlier full-period bound $8e^{-u/101}$, extracting $e^{-2N/20200}$. For the forward and centered lattice multipliers integrate $\xi^2/(2s_0)$ and $\xi^4/(12s_0^2)$ against the continuum cosine transform. Use the Airy bounds above through $u=40$ and $|f(u)|\le10\sqrt u e^{-.58u}$ thereafter. These calculations give the error table. The comparison of its errors with derivative signs, including the lower endpoint $.145$, is in the [cubic integral argument](cubic-tilt.md#the-peak-interval).

Lean gives a sharper conditional first-return estimate. At return time $2j$, let $d=j-1$ and write $|\theta|=z^3\le .001$. Keep $\lfloor d/8\rfloor$ initial steps and $t=\lfloor d/4\rfloor$ terminal steps of the interior bridge. Appending one down-step to a surviving terminal path ending at height one makes it a first hit of zero. The fair first-hit point bound at time $t+1$ therefore bounds every normalized terminal kernel entry by $1/(t+1)$. The initial survival probability is at most five times the fair bridge return probability $r_d$ for $d\ge40$. Whole killed blocks on the remaining steps give the following bound on the signed first-return symbol $H_j$ with fair mass $p_j$:
$$
 |H_j(\theta/2)|\le p_j\,125\exp(-0.30jz^2)
 = p_j\,125\exp(-0.15uj/N),\qquad u=2Nz^2,\quad j\ge41.
$$
The proof uses positive frequency. Complex conjugation gives the same modulus at negative frequency. [Pinned endpoint estimate](CentralUnimodality/FirstReturnFourier.lean) · [Explicit rate and constants](CentralUnimodality/FirstReturnInnerArc.lean)

## The density at 125000 pairs

For $N\ge125000$ take $U=85$, $\tau_* = .0007$ and use the same half-unit bins and input polynomials. All cosine and sinc arguments still have modulus below $.8$. Enlarge the gamma windows to $W=[\max(0,.88a-1),1.12b+1]$. At tilt $\lambda=.12$ the probability of $|\tau(T-j)|>.12v+1$ is at most $3\exp(-.004j-.12/\tau)$, since $.12\lambda-\lambda^2/(2(1-\lambda))>.004$. In the Cauchy–Schwarz exceptional bound replace $.015/\tau_*$ by $.06/\tau_*$ and use the new $\tau_*$. The result is still below $10^{-16}$. For late returns $j>N/20\ge6250$ the Wallis and segment estimates still give factors $1.01$ and $240$, as checked at the lower endpoint.

In removing the final gamma average take derivative suprema on $[.95a,1.05b]$. Tilt $\pm.04$ gives probability at most $3e^{-N/1000}$ outside that window, since $.05(.04)-(.04)^2/(2(1-.04))>.001$. The previous exceptional cost is at most $2\cdot10^6e^{-N/2000}<N^{-2}$. The sum of the averaging and return errors in the density integral, including $2/\pi$, is below $.05656$.

Only the order-zero tail is needed. The existing $100e^{-.162u}$ bound for both laws costs at most $.01190$ beyond $U$. For the lattice arc past $|\theta|=.001$ integrate $8e^{-u/101}$ from $v=2N/100$. Its contribution including $2/\pi$ is at most
$$ \frac{24\sqrt v\,e^{-v/101}}{\pi(1/101-1/(2v))}<.000001. $$
This uses $\sqrt{v+t}\le\sqrt v\,e^{t/(2v)}$. Together the errors are below $.069$. All terms decrease as the size exceeds the stated lower bound, or are uniformly bounded there by the same fixed integral. The [verifier](verify_local_returns.py) uses rational enclosures for all three terms. The application to coefficients uses this density estimate at two separated sites. [Odd-part reflected comparisons](type-b-transfer.md#from-a-failed-comparison-to-an-odd-part-valley)
