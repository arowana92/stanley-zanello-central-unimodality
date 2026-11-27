# Certifying a central interval by sampled Fourier inversion

Let $m=2n$ or $2n+1$ be the ballot length, $D=\lfloor m^2/4\rfloor$, $b_k=a_{D-k}$ and $P_m(k)=b_k/\binom mn$. Thus $k$ counts missing cells. Write $m+1=2N+\delta$, $s_0=(2N)^{3/2}$ and $d=(m+1+\lceil m/2\rceil)/2$. The strict walk of length $m+1$, conditional on no return to zero, has signed half-area $Y=\pm(K+d)$, where $K$ has probabilities $P_m$. Both signs occur with equal probability. At $N=n$ the odd-part staircase uses $\delta=1$. At $N=n+1$ the even-part staircase uses $\delta=0$. [Ballot bijection](README.md#exact-coefficient-checks) · [Signed-area identity](return-expansion.md#splitting-at-zero)

The finite certificate concerns the sequence at
$$
 \lfloor .1366m^{3/2}\rfloor\le k\le\lceil .6m^{3/2}\rceil,
 \qquad 2049\le N\le300000 .
$$
Its sign tests prove weak unimodality on this interval. A Fourier calculation in the length variable first encloses the area transform simultaneously at many sizes. A second Fourier calculation tests its spatial derivatives. Bounds on the omitted frequencies and on the error between spatial grid points cover **every integer corank** in the interval.

## Periodizing the lattice law

Use an integer power of two $Q\ge5s_0$ and the frequencies $\theta_j=2\pi j/Q$ on one full period, represented in $[-\pi,\pi]$. Write $\Phi_N^\delta(\theta)=\mathbb E\cos(\theta Y)$. For the sites $y=k+d$ the discrete inversion gives the sum of the probabilities at $y+vQ$, $v\in\mathbb Z$. This follows from the finite geometric sum since $Y-y$ is integer, including when $d$ is a half-integer. Doubling the result recovers $P_m(k)$ plus contributions from the aliases. In unnormalized units the self-test inverts every coefficient of both families through $n=12$.

For $|k+d|\le .63s_0$, an alias at this site or either neighbor requires $K\ge4.3s_0$, since $d/s_0<.012$. Under unrestricted fair signs the rank sum is $Z=\sum_{r=1}^m rX_r$ for independent Bernoulli halves, with $\mathbb EZ=m(m+1)/4\ge D$. Hoeffding's inequality and the survival probability at least $1/(2\sqrt m)$ give
$$ \Pr(K\ge4.3s_0)\le2\sqrt m\exp[-5.99(4.3)^2]. $$
Indeed $2s_0^2/\sum r^2\ge6/((1+1/m)(1+1/(2m)))>5.99$. In a difference of order $r=1,2$, the absolute sum of its multipliers is $2^r$. Even after multiplication by $2^{r+1}s_0^{r+1}$, the tail probability is below $10^{-12}$ at $N\le300000$. [Rational bounds](verify_fourier_grid.py)

Retain $j=1,\ldots,J$ and their negatives with $s_0\theta_J\ge2048$. The constant mode cancels in differences. In units $s_0^{r+1}$ the omitted difference of order $r$ is bounded by
$$
 \frac{2}{\pi}\Delta\xi\sum_{j>J}(s_0\theta_j)^r |\Phi_N^\delta(\theta_j)|,
 \qquad \Delta\xi=2\pi s_0/Q .
$$
The sum ends at $Q/2$ and bounds the single Nyquist term by counting it twice. On $0<\theta\le.008$ use $100e^{-.157|\xi|^{2/3}}$, $\xi=s_0\theta$. The two [first-hit block tests](size-descent.md#lattice-estimates-at-the-three-cutoffs) give rates $.1895,.16$ before keeping a prefix of length $\lfloor m/64\rfloor$. Its survival-probability ratio to the full walk is less than 16 by Wallis, also at $m\ge4097$. Rounding down the count of whole blocks is included in the prefactor 100. Here $.16(63/64)m/(2N)>.157$. The weighted envelope decreases from 2048, so the right-endpoint sum is at most its integral from 2048. Substitute $u=\xi^{2/3}$ and use $2048^{2/3}>161$.

For the two outer arcs use the following uniform estimates on the maximum absolute row sum of a killed block. Rates are per walk step.

| Lower frequency $t$ | Block length $L$ | Block norm at every $t\le\theta\le\pi$ |
| ---: | ---: | ---: |
| .008 | 216 | $<e^{-.0078L}$ |
| .032 | 112 | $<e^{-.0155L}$ |

To prove them, take $l=\lfloor b/2\rfloor$ for an unrestricted block of $b$ steps. Pair the outer positions in its even prefix. Conditional on each pair's total displacement the endpoint is fixed. The product of $(1+|\cos((2h-1)\theta/2)|)/2$ over $1\le h\le l$ bounds the absolute row sum, since each pair is mixed with probability $1/2$. A leftover final step costs at most one. The product is at most $\exp(-T/4)$, where
$$ T=\sum_{h=1}^l\sin^2((2h-1)\theta/2)=l/2-\sin(2l\theta)/(4\sin\theta). $$
Through $\theta=\pi/(2l)$ the sum increases. In the central interval $[\pi/(2l),\pi-\pi/(2l)]$ one has $\sin\theta\ge1/l$. In the remaining upper interval $\sin(2l\theta)\le0$ and the endpoint $\pi$ follows directly. Thus use the smaller of $l/4$ and the sine-square sum at $\min(t,3/(2l))$ as a lower bound, using $\sin x\ge x(1-x^2/6)$ there. Denote the resulting unrestricted upper bound by $\rho_b$, including $\rho_0=\rho_1=1$.

At distance $a$ from the killing site, a first hit at $j$ has probability $p_{a,j}=a\binom{j}{(j-a)/2}/(j2^j)$ for $j\ge a$ on the compatible parity. Subtract first-hit paths from the unrestricted transform and bound the remaining suffix after the hit by $\rho_{L-j}$. The absolute killed row sum is at most
$$ \min\left(1-\sum_j p_{a,j},\; \rho_L+\sum_j p_{a,j}\rho_{L-j}\right). $$
The rational verifier takes the maximum over $1\le a\le L$ and the unrestricted bound for $a>L$.

On each arc $[t,t']$ use the applicable rate $c$, the prefix survival ratio 16 and at most one incomplete block. Before the overall factor $2/\pi$, its contribution is at most
$$
 16e^{cL-c(63/64)(2N-1)}\big((t'-t)s_0+2\pi/5\big)(t's_0)^r .
$$
These bounds decrease from $N=2049$ since $2c(63/64)N>3(r+1)/2$. Together with the inner arc they give errors below $.00025$ and $.949$ for the first and centered second differences. Including aliases we use $.00026$ and $.95$.

## A posteriori verification of the signed transforms

At fixed $\theta$, let $P_j^\delta,R_j,U_j^\delta$ be the transforms of the free walk of length $2j+\delta$, the paths returning at $2j$, and the paths with no return by $2j+\delta$. These transforms include the event probabilities. In the half-length convolution,
$$ P^\delta=R*U^\delta,\qquad R^{-1}=\mathbf1_0-H,\qquad
 \sum_{j\ge1}|H_j|\le1,\qquad U_N^\delta=r_N\Phi_N^\delta,\quad r_j=4^{-j}\binom{2j}j. $$
Here $H$ restricts to first returns. Splitting at the last or the first zero proves the identities. In particular, if an approximate $U$ satisfies $|P_j-(R*U)_j|\le e$ through index $M$, then $|U_j-U_j^{\rm true}|\le2e$ **at every one of those indices**. This bound permits a fast numerical proposal followed by an independently computed residual. [Input products and last-return proof](return-expansion.md#splitting-at-zero)

Put $\omega=\theta/2$, $c_j=\cos(j\omega)$ and $s_j=\operatorname{sinc}(j\omega)$. The free transform is the product of $\cos(l\omega)$ through the walk length. The bridge product from the Gaussian binomial gives
$$ R_0=1,\qquad R_j=R_{j-1}\frac{c_j}{2}
       \left(c_{j-1}+c_j\frac{j-1}{j}\frac{s_{j-1}}{s_j}\right). $$
This follows by canceling the consecutive sine products and using the sum formula for $\sin((2j-1)\omega)$. The code uses $2c_jc_{j-1}-c_1$ and $2c_j^2-1$ for the odd and even cosine factors. An upper bound on the unrestricted norm of a prefix of $2j$ steps is the product of $(1+|\cos((2h-1)\omega)|)/2$. Once this bound falls below $2^{-75}$, all later free and bridge inputs may be set to zero with this absolute error. For a bridge, taking a single entry of the longer unrestricted block only reduces its bound. Until truncation the code checks $j\omega\le1.5$ to within the fixed-point error.

The routine proposes both sequences $U$ using Newton division of formal power series, storing the two parities in the real and imaginary components. It then pads the candidate and the real bridge to length at least $2M+1$ and multiplies them afresh. The checked FFT therefore evaluates **linear convolution** at every index used. For each frequency it records the largest residual over both components and every $0\le j\le M$. The next two paragraphs justify the reserves added to that residual. [C++ verifier](verify_fourier_window.cpp)

### Input arithmetic

Fixed-point units are $h=2^{-96}$. A product uses two base-$2^{48}$ limbs and rounds down with absolute error below $h$. Integer addition is exact. All signed 128-bit intermediate products fit. In the trigonometric and reciprocal calculations the fixed-point operands have absolute value below 4, and scalings by the half-length use integers below $2^{20}$. The angles are exact dyadic multiples of a bracketed value of $\pi$ before the fixed-point product. The Python verifier checks the floor of $2^{96}\pi$ using Machin's formula and alternating arctangent bounds.

For an argument up to $\pi/2$, evaluate the cosine and sinc series through degree 28 at half the argument by Horner's rule, then use the double-angle formulas. At the half-angle the modulus is below $.8$, and the omitted term is below $h$. Each stored coefficient has error at most $2h$ by its division recurrence. The squared argument has error below $6h$. Bounding the absolute derivative of the Horner polynomial there by $(1-.64)^{-2}$ and its accumulated coefficient and product errors by $3h/(1-.64)$ gives error below $64h$ for each half-angle value. Doubling gives absolute errors below $512h$. The rounded-up prefix norm allows $2^{16}h$ in each pair factor and one unit after the product.

The sinc reciprocal is checked by multiplication to within $2^{-81}$, and the true sinc exceeds $.62$. Its absolute error is below $2^{-79}$. In the bridge ratio the error is below $2^{-78}$: the reciprocal contribution is multiplied by factors of modulus at most one, and all cosines and sincs contribute together less than $20\cdot512h$. The free product has smaller per-step error. Before truncation the true bridge ratio has modulus at most one, by $0\le (j-1)\omega\le j\omega<\pi/2$. Consequently the accumulated absolute input error before conversion to binary64, including truncation, is at most $(M+1)2^{-77}$ for $M\le300000$. This follows by summing the per-step losses with multiplier at most $1+2^{-78}$. The sequence $r_j$ is computed by its fixed-point ratio $(2j-1)/(2j)$ with absolute error at most $jh$ before conversion.

### Convolution arithmetic

Let $u=2^{-53}$ and let $l$ be the number of FFT stages, at most 20. We use binary64 round-to-nearest with fast-math and contraction disabled. Each root of unity is rounded from the preceding fixed-point trigonometric calculation. The complex absolute error in a stored root is below $3u$. A complex product of exact floating inputs has absolute rounding error at most $4u|a||b|$ up to an additive underflow allowance. Indeed each component uses two products and a sum, and the Euclidean norm of the two sums of absolute products is at most $\sqrt2|a||b|$.

An unnormalized radix-two transform on $L$ points has Euclidean error at most $\eta\sqrt L\|a\|_2$, $\eta=13lu$. Each butterfly multiplies its second input by a stored unit complex number and adds and subtracts it from the first. The rotation contributes at most $8u$ times the second modulus. The pair of sums contributes at most $2u$ times the ideal output norm after allowing for the rotation. Since the ideal butterfly divided by $\sqrt2$ is unitary, the resulting relative stage error is below $12u$ in norm. Iterate $(1+12u)^l-1\le13lu$. For an individual output the error is also at most $\eta\sum|a_j|$. At each stage the corresponding absolute sum over inputs to that output is the sum of those of its two children. The same rotation and addition bounds propagate it by at most $1+12u$ per stage. Division by $L$ in the inverse is a binary scaling.

For convolution divided by $L$ after the inverse, Cauchy–Schwarz bounds the product spectrum's average absolute value by $(1+\eta)^2\|a\|_2\|b\|_2$ before pointwise rounding. Using the two forward norm errors, the product error and the individual inverse-output error gives absolute error at most
$$
 ((1+\eta)^3(1+4u)-1)\|a\|_2\|b\|_2 <59lu\|a\|_2\|b\|_2 .
$$
The code charges $60lu(\sqrt{\text{sum of squares of }a\;\text{sum of squares of }b}+.001)$. Each sum has at most $2(M+1)$ positive additions. Rounding these sums costs less than a factor $1+10^{-9}$. Subnormal outputs in these bounds may be charged $2^{-1022}$ additively per real operation. With $L\le2^{20}$, input magnitudes below 2, and at most three transforms and one pointwise product, even $10^4L^8\,2^{-1022}<10^{-240}$ dominates the propagated absolute allowances. In detail one transform amplifies an additive per-butterfly error by at most $4L^2$ including both components and all stages, each spectral product input has modulus below $3L$, and the normalized inverse has at most the same amplification. The displayed absolute reserve covers also the spatial transforms below.

The program checks each candidate component has magnitude at most $1.01\widehat r_j$. Thus at most $2.022\sqrt{M+1}$ multiplies the absolute bridge-input error in one component, by $r_j\le1/\sqrt{j+1}$. The relative binary64 rounding of the bridge costs at most $1.011u\sum r_i r_{j-i}=1.011u$. The free input costs one more conversion. A reserve of $2^{-47}$ covers these errors, the fixed-point errors and underflow, as the rational verifier checks. A factor $1.00001$ covers the binary64 subtraction in the observed residual. The resulting bound $e$ applies to the exact residual; replacing $2/r_N$ by $2.0001/\widehat r_N$ and adding $10^{-14}$ covers conversion to the conditional transform and the linear interpolation arithmetic below.

## Signs on entire size and corank intervals

Choose $Q$ as the least power of two at least $5(\lfloor s_0\rfloor+1)$, and group consecutive half-lengths $A\le N\le B$ with common $Q$ and $B\le1.01A$. Put $S=\lfloor(2A)^{3/2}\rfloor$, $x=(k+d)/S$, and $J=\lceil2048Q/(6.28S)\rceil$. This gives $S\le s_0\le1.016S$ and $s_0\theta_J\ge2048$ for the whole group. At any retained frequency interpolate its two *computed* real conditional transforms at $A,B$ linearly in $N$. The program measures the absolute difference from this interpolation at **every** $N$ and adds the certified transform error using the smallest survival, $\widehat r_B$. Call the bound $e_j$ for a given parity. A single-size group uses its sole endpoint.

For either endpoint let $T(x)$ be the real trigonometric polynomial with positive-frequency terms $(4S/Q)\widehat\Phi_j\cos(2\pi j Sx/Q)$. The constant term is irrelevant. At each intermediate $N$ use the same convex combination of the two endpoint polynomials. For differences of order $r$, the interpolation error in units $S^{r+1}$ is at most
$$
 (4S/Q)\sum_{j=1}^J (2\pi j S/Q)^r e_j.
$$
This follows from the bound by $|2\pi j S/Q|^r$ for the scaled lattice multiplier. The truncation and alias reserves above also apply because $S\le s_0$.

At each endpoint, evaluate $T',T''$ on the equally spaced grid $x_i=iQ/(32768S)$ by a radix-two transform. Its input frequencies lie below the Nyquist index. The checked sum of the absolute derivative coefficients is below $10^6$. The individual-output FFT bound, including binary64 evaluation of the real amplitudes, costs less than $.00001$ at each grid point. Between two points, linear interpolation of derivative order $r$ costs at most $(Q/(32768S))^2\sup|T^{(r+2)}|/8$. Bound that supremum by the sum of the absolute Fourier coefficients at order $r+2$. All positive error sums in this step and the length interpolation receive a factor $1.00001$, covering binary64 summation and multiplier rounding. Intervals in the code extend the mesh-point membership tests by $.00001$ in position.

The following inequalities are required after all the preceding error deductions, at both endpoints of **each** group and in both parities.

| Interval in $x$ | Sign required |
| --- | --- |
| $[.1359,.339]$ | $T'>0$ |
| $[.333,.404]$ | $T''<0$ |
| $[.398,.631]$ | $T'<0$ |

Convex combinations preserve each strict margin. Integrating $T'$ over one lattice spacing, or $T''$ against the centered triangular kernel of mass one in scaled difference units, transfers the corresponding sign to the lattice difference. On the asserted corank window one has $.1364<x<.623$ and $1/S<.000004$. Thus forward steps with $x\le.338$ increase, those with $x\ge.399$ decrease, and consecutive forward differences decrease strictly between these regions, including the joins. This proves unimodality on the entire window.

## Reproduction

From this checkout run

~~~sh
python3 -B verify_fourier_grid.py
clang++ -std=c++17 -O3 -fno-fast-math -ffp-contract=off verify_fourier_window.cpp -o /tmp/sz_fourier_window
/tmp/sz_fourier_window --self-test
/tmp/sz_fourier_window 2049 16384
/tmp/sz_fourier_window 16385 71156
/tmp/sz_fourier_window 71157 112954
/tmp/sz_fourier_window 112955 179303
/tmp/sz_fourier_window 179304 284627
/tmp/sz_fourier_window 284628 299998
/tmp/sz_fourier_window 299999 300000
~~~

The two integer arguments are inclusive half-lengths. Each of the seven runs above completed in both parities. The entries below round the smallest margins in each run down, after the frequency, length interpolation, spatial interpolation, alias and arithmetic errors have all been deducted. For the middle and right intervals the margin is measured in the negative direction.

| First $N$ | Last $N$ | Left first difference | Middle second difference | Right first difference |
| ---: | ---: | ---: | ---: | ---: |
| 2049 | 16384 | .0800 | 103.3 | .929 |
| 16385 | 71156 | .0801 | 102.8 | .941 |
| 71157 | 112954 | .0799 | 102.4 | .942 |
| 112955 | 179303 | .0797 | 101.9 | .942 |
| 179304 | 284627 | .0793 | 101.3 | .942 |
| 284628 | 299998 | .0788 | 101.1 | .941 |
| 299999 | 300000 | .1427 | 101.9 | 1.711 |

The seven intervals cover 297,952 consecutive half-lengths. A single invocation with arguments `2049 300000` also requests the entire range. Changing the division into runs recomputes the bounds for the resulting groups. The proof uses the convolution residual and the three margin tests at every group, with the analytic estimates above controlling the exact coefficients.
