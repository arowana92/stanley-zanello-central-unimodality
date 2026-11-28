# The central peak from 10,000 rows

**Computer-assisted theorem.** For both central staircase families and every row count $n\ge10000$, the corank sequence is weakly unimodal from the induction's starting corank through the smaller of the midpoint and $\lfloor3m^{3/2}/5\rfloor$, where $m=2n+\delta$ and $\delta\in\{0,1\}$. The proof below establishes the three signs on continuous intervals for every half-length $N=n+\delta\ge10000$. The transfer to the stated integer ranks applies for $n\ge5000$. The full Lean peak theorem currently starts at $n=150000$. [Integer rank transfer](CentralUnimodality/IntegralPeakWindow.lean) · [Lean status](research/lean-status.md)

| Derivative | Scaled position | Sign | Full-period margin exceeds |
| --- | --- | --- | ---: |
| First | $[.1359,.339]$ | Positive | $0.071350$ |
| Second | $[.333,.404]$ | Negative | $125.913863$ |
| First | $[.398,.631]$ | Negative | $1.871350$ |

The two retained errors, integrated against the first and second powers of frequency on $[0,1728]$, are below $0.123827$ and $27.478759$. The calculation uses rational upper bounds. The finite checks cover time cells, coefficients of polynomials, and signs on spatial intervals. Size enters those bounds only through factors that decrease for $N\ge10000$.

## The local expansion

Use $u=|\xi|^{2/3}$, $\tau=u/N$, $v=j\tau$ and $\omega^2=\tau^3/32$. On $0\le u\le114$ one has $\tau\le\tau_*=114/10000$. The free symbol at time $2j+\sigma$ has leading Gaussian $p(v)=e^{-v^3/24}$. The bridge symbol at time $2j$, divided by its survival probability $r_j$, has leading Gaussian $\rho(v)=e^{-v^3/96}$. In each case write the next two symbol coefficients as $g_1=-Ag$ and $g_2=(A^2/2-B)g$.

| Symbol | $A(v)$ | $B(v)$ |
| --- | --- | --- |
| Free, $\sigma=0,1$ | $(2\sigma+1)v^2/32+v^5/1920$ | $(12\sigma+1)v/192+(2\sigma+1)v^4/1536+v^7/80640$ |
| Bridge | $v^2/192+v^5/30720$ | $7v^4/184320+v^7/5160960$ |

These are the first two coefficients of the negative logarithm after its Gaussian term. The cosine logarithm has positive coefficients $1/2,1/12,1/45$ at degrees 2, 4 and 6. The corresponding sinc coefficients are $1/6,1/180,1/2835$. Sum the powers through $2j+\sigma$ for the free symbol. For the bridge take the sum through $2j$ minus twice the sum through $j$. Substitution of $j=v/\tau$ gives the table. The verifier recovers the coefficients independently by exact interpolation of these power sums. [Cosine and sinc products](CentralUnimodality/QuarticLatticeLogs.lean) · [Polynomial verifier](verify_second_split.py)

When the largest argument has absolute value at most $9/8$, the logarithmic remainders after degree six are nonnegative and increasing on the positive axis. Their upper bounds are $x^8/70$ and $x^8/32000$. Indeed, in either Euler product write $c_6$ for the coefficient of degree six and $\alpha$ for the smallest positive zero. After dividing by $x^8$, the positive remainder is bounded by $3c_6/[4(\alpha^2-x^2)]$. Lean independently proves both bounds by differentiating the logarithms and checking rational bounds for sine and cosine. Monotonicity also gives the lower bound zero for the difference of the two bridge sums. [Trigonometric estimates](CentralUnimodality/QuarticSymbolSlopes.lean) · [Logarithmic remainders](CentralUnimodality/QuarticLogLosses.lean)

Write $d=-\log(W/g)-\tau A-\tau^2 B$. Then $0\le d\le\tau^3 C$. The verifier uses the following bounds for $C$, with $s=\tau_*$.
$$
\begin{aligned}
 C_p(v)&=\frac1{64}
 +\frac{104v^3/3+24sv^2+8s^2v+s^3}{12288}
 +\frac{(v+s)^6}{11520}+\frac{(v+s)^9}{18432\cdot70},\\
 C_\rho(v)&=\frac{2v^3}{180\cdot32^2}
 +\frac{(v+s)^6}{512\cdot2835}+\frac{(v+s)^9}{18432\cdot32000}.
\end{aligned}
$$
For the free quartic sum, subtract its terms in $j^5,j^4$. The remainder at $\sigma=0$ is $8j^3/3-j/15$. At $\sigma=1$ add $32j^3+24j^2+8j+1$. The bridge quartic sum leaves $2j^3$. The sixth power sum through $t$ is between $t^7/7$ and $(t+1)^7/7$. Its excess in the free case over $(2j)^7/7$ is at most $2(2j+2)^6$. The bridge difference after its leading term is $31j^6+15j^5-j^3$, between zero and $(2j+1)^6$. The eighth power sum is at most $(2j+2)^9/9$. These bounds give the displayed expressions, including the possible free quadratic constant $1/64$. Since $A,B,d\ge0$, expanding the real exponential gives the cubic symbol error
$$
 |W-g-\tau g_1-\tau^2g_2|
 \le \tau^3 g\big(C+A^3/6+AB+sB^2/2\big).
$$
To see this, separate $e^{-d}$ at cost $d$, expand $e^{-\tau A}$ to degree two, and expand $e^{-\tau^2 B}$ to degree one. The cross term is bounded using $1-e^{-\tau A}\le\tau A$. Lean proves this cubic error bound directly for the actual free and normalized bridge Fourier symbols. [Scaled lattice bounds](CentralUnimodality/ScaledSexticInputs.lean)

If an argument exceeds $9/8$, then $(2v+\tau)\sqrt{\tau/32}>9/8$. In the current range this implies $v>28$, $\tau>1/2000$, and $N<228000$. Set $l=\lfloor25/\tau\rfloor$. Then $24\le l\tau\le25$, $l\le j$, and $|\omega|(2l+1)<\pi/2$. Pairing the first $2l$ steps bounds the absolute free and unnormalized bridge symbols by $\exp[-\omega^2(4l^3-l)/12]\le e^{-140}$. This uses only those prefix steps and applies regardless of later angles. The costs of dividing by $r_j$ and replacing the symbols by the quadratic Gaussian trials are together less than $10^{-18}\tau^3$, since $1/r_j\le2\sqrt N<1000$. The verifier includes that allowance in every bin. [Uniform Lean bound on both sides of the angle cutoff](CentralUnimodality/QuadraticOuterSymbols.lean) · [Numeric inequalities](verify_quadratic_peak.py)

## The signed quadratic residual

Let $I$ denote arcsine expectation and write $\beta(B,F)=I[B(vx)F(v(1-x))]$. Put $q=x(1-x)$ and
$$
 J_r(B,F)=\sum_{h=0}^r(-1)^{r-h}\binom rh B^{(h)}(vx)F^{(r-h)}(v(1-x)).
$$
For a discrete split of $j$ pairs the zeroth term is $\beta$, the term in $\tau$ is $L_1(B,F)=vI[qJ_2]/2$, and the term in $\tau^2$ is
$$
 L_2(B,F)=vI[q(1-2x)J_3]/6+v^2I[q^2J_4]/8.
$$
The cubic remainder is bounded by $\tau^3(vD_4/96+v^2D_5/192+v^3D_6/1440)$ when $D_r$ bounds the sum of the absolute terms of $J_r$. This follows from a quintic Taylor expansion under the exact binomial mixture at each $x$. For polynomial inputs the weighted arcsine integrals are explicit beta products with shifted exponents. [Binomial moments and Taylor bound](CentralUnimodality/SecondOrderQuadrature.lean) · [Polynomial evaluation](CentralUnimodality/PolynomialSecondSplit.lean)

Use the signed trial $F+\tau G_\sigma$ from the first-correction certificate. Its residual at order $\tau^2$ is
$$
 R_2=p_2-\beta(\rho_2,F)-\beta(\rho_1,G_\sigma)
       -L_1(\rho_1,F)-L_1(\rho,G_\sigma)-L_2(\rho,F).
$$
First replace $p,\rho$ by their dyadic polynomials. The verifier evaluates $R_2$ exactly, retaining all signs. On $[0,144]$, the two polynomial norms are below $0.008$ and $0.093$ and their derivative norms below $0.012$ and $0.126$. To bound the replacement error, split the Gaussian input interval at 20. Below 20 use the polynomial ODE defect and its derivatives. For example, with $a=3v^2/b$, the error $e$ for the divisor $b$ satisfies $e'+ae=-D/256$ in the physical variable. Apply the product rule up to order four. Above 20 bound the Gaussian derivatives and the exact Chebyshev norms of the polynomial derivatives separately on $[20,144]$. With the polynomial log multipliers and the factors $|q|\le1/4$, $|1-2x|\le1$, the resulting error in $R_2$ is below $1.8\times10^{-13}$ in both parities. The code also checks the quadratic split formula on monomial pairs by interpolating the actual discrete arcsine moments. [Exact residual and input errors](verify_second_split.py)

A separate whole-interval Lean proof bounds the Gaussian replacement error by $3\times10^{-7}$. It differentiates the bridge ODE defect three times and proves $|e^{(r)}(v)|\le2\times10^{-22}1000^r$ for $0\le r\le4$ and $0\le v\le144$. Using this larger allowance in the rational spatial certificate gives retained errors below $0.130897$ and $34.119263$. The three full-period margins still exceed $0.064280$, $1.864280$ and $119.273359$ in the order of the rows above. [Gaussian derivative bounds](CentralUnimodality/GaussianReplacementJets.lean) · [Transfer to the second residual](CentralUnimodality/SecondResidualTransfer.lean)

Lean also computes the two signed polynomials directly from the checked trial rows. Its factorial-weighted integer multiplication evaluates the beta integrals after the input exponents are shifted by the quadrature weights. Python uses ordinary coefficient sums. All 1,015 coefficients from degree zero through degree 1,014 agree as rational numbers for each parity, and the additional high slots of both representations vanish. [Exact Lean evaluator](CentralUnimodality/SecondResidualRows.lean) · [Independent calculation](verify_second_split.py)

For the cellwise bounds, round the exact Chebyshev coefficients of $R_2$ to the nearest multiple of $2^{-120}$. If the polynomial has $d+1$ coefficients, this costs at most $(d+1)2^{-121}$ on the entire interval. Shift that polynomial to each half-unit cell and bound it by the sum of the absolute shifted coefficients. For $G_\sigma$ combine the signed coefficients of the trial and its drift *before* bounding derivatives on a cell. This preserves their cancellation.

Lean also permits truncating the symmetric dyadic row. The proof converts physical monomials with $v=128(1-x)$, rounds at scale $2^{-120}$, and charges each discarded Chebyshev mode its absolute coefficient. Both dyadic rows have 611 modes after trimming trailing zeros. Keeping modes 0 through 255 costs less than $2\times10^{-9}$ in either parity. Lean checks the prefixes on 57 intervals of width two. Python independently recomputes all 114 parity bounds. Using the uniform first residual bound $3\times10^{-12}$ and a combined Gaussian, rounding, and truncation allowance of $303\times10^{-9}$ gives retained errors below $0.136932$ and $35.611802$. The three full-period margins exceed $0.058245$, $1.858245$, and $117.780819$. The remaining hypothesis in the Lean cell estimate identifies each saved dyadic row with the output of the factorial evaluator. [Change of basis](CentralUnimodality/PhysicalChebyshevRows.lean) · [Rounding and truncation](CentralUnimodality/RoundedQuadraticRows.lean) · [Checked cells](CentralUnimodality/CertifiedQuadraticCells.lean)

After subtracting $R_2$, the cubic error has seven terms, in addition to the free cubic symbol error. Let $E_\rho$ denote the cubic bridge error per unit $\tau^3$. In each product evaluate the left and right factors in their respective split cells. Use $D_r(A,B)$ for the local sum of absolute derivative products. The seven bounds, per unit $\tau^3$, are

- $E_\rho(|F|+s|G_\sigma|)+|\rho_2G_\sigma|$ for the bridge product.
- $v[D_2(\rho_2,F)+D_2(\rho_1,G_\sigma)]/8$ for the order-two products sampled to zeroth order.
- $v[D_3(\rho_1,F)+D_3(\rho,G_\sigma)]/24$ and $v^2[D_4(\rho_1,F)+D_4(\rho,G_\sigma)]/128$ for the order-one products sampled through first order.
- $vD_4(\rho,F)/96$, $v^2D_5(\rho,F)/192$, and $v^3D_6(\rho,F)/1440$ for the leading product sampled through second order.

The verifier maximizes each of the seven terms separately over admissible cell pairs. In particular the fourth, fifth, and sixth derivatives of the leading product can reach their upper bounds on different pairs. Gaussian monomials are bounded at their extrema. At $j=0$ the split evaluates the factors at zero and its quadrature error vanishes. The theorem `quadratic_split_residual` applies this error budget to the actual last-return convolution throughout $N\ge10000$, $N\tau\le114$. [Lean proof](CentralUnimodality/QuadraticSplitResidual.lean)

## Return inversion and reproduction

Price the bounds on $R_2$ and the cubic remainder separately using the first-return inverse. For early returns use the largest bound in the preceding five percent of elapsed time. For a later return $j>N/20$ one has $j\ge501$ even at $N=10000$. The point-mass and first-return Fourier bounds from the earlier certificate therefore apply. In current cell $i$ and remaining-time cell $k$, use the discount $\min(1,125\cdot2^{-\lfloor(i-k-1)_+/10\rfloor})$. The early weights grow at most as $\sqrt N$, and the late weights decrease with $N$. Their products with $(u/N)^2$ or $(u/N)^3$ are bounded at $N=10000$. Lean proves this inversion step for the actual signed amplitude, with separate prices for the second residual and the cubic remainder at the return time. It also proves the Gaussian error polynomials and the identity for the combined correction before taking derivatives. [Amplitude inequality](CentralUnimodality/QuadraticAmplitude.lean) · [Return-time pricing](CentralUnimodality/QuadraticInversePricing.lean) · [Gaussian bounds](CentralUnimodality/QuadraticGaussianCosts.lean) · [Signed derivatives](CentralUnimodality/CombinedCorrectionJets.lean) [Inverse bound](CentralUnimodality/DiscountedInverse.lean) · [Late-bin weights](CentralUnimodality/BinnedInverseAllowance.lean) · [Fourier discount](CentralUnimodality/ReturnFrequencyBins.lean)

On $114\le u\le144$ use $100e^{-.186u}$ for the true signed amplitude and check the polynomial trial against $10^{-14}$. From $\xi=1728$ to $0.008(2N)^{3/2}$ integrate the existing $.157$ exponential bound. On the final arc the block estimate is bounded by $144e^{-N/67}$ since $.0078\cdot216-.0078(63/64)(2N-\delta)\le2-N/67$. The contribution through the full lattice period is below $.001$, even for difference order two. Integrate the resulting errors with the two frequency weights and subtract them from the three compact polynomial margins. The table at the start gives the remainders. [Moderate frequencies](CentralUnimodality/ModerateFrequencyTail.lean) · [Outer frequencies](CentralUnimodality/SpatialOuterTail.lean) · [Exact spatial sign test](verify_polynomial_integral.py)

~~~sh
python3 -B verify_second_split.py
python3 -B verify_quadratic_peak.py
python3 -B verify_quadratic_peak.py --lean-gaussian-bound
python3 -B verify_quadratic_peak.py --lean-cheb-prefix
lake env lean --run research/ExportSecondResidual.lean | python3 -B verify_second_split.py --check-lean-rows
lake env lean --run research/ExportQuadraticCells.lean | python3 -B verify_quadratic_peak.py --check-lean-cells
~~~
