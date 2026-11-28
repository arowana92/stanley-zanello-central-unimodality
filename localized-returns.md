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

For $0\le v\le256$ there is a rational certificate for five specific polynomials. Their coefficients are integers in units of $2^{-120}$ in the basis $T_i(1-2v/256)$. The free and bridge trials $P,B$ have degree at most 600. The amplitude trial $F$ and the first-correction trials $M_0,M_1$ have degree at most 420. The candidates came from cosine interpolation of the elementary exponentials, and of the moment and Airy approximations in the return expansion. All bounds below are verified from the stored integers. [Coefficient table](research/gamma-polynomials.json) · [Independent standard-library verifier](verify_gamma_polynomials.py)

The two input polynomials approximate $p(v)=e^{-v^3/24}$ and $\rho(v)=e^{-v^3/96}$ uniformly within $10^{-21}$. To check this, put $z=v/256$, $V=256$, let $D=24$ or $96$ and compute the defect $A'(z)+(3V^3/D)z^2 A(z)$. Its maximum absolute value plus $|A(0)-1|$ bounds the solution error on $[0,1]$ by the integrating factor formula. For the corrections put $D_{P,\sigma}(v)=P(v)\big((7-2\sigma)v^2/32-v^5/120\big)$ and $D_B(v)=B(v)(v^2/24-v^5/1920)$. Exact rational bounds over the full interval are

| Polynomial | Absolute value | Absolute $v$ derivative |
| --- | ---: | ---: |
| $P-B\star F$ | $2\times10^{-15}$ | $4\times10^{-13}$ |
| $D_{P,\sigma}-B\star M_\sigma-D_B\star F$, either parity | $3\times10^{-14}$ | $6\times10^{-12}$ |

The verifier expands the convolution in monomials, converts back to Chebyshev coefficients, and sums their absolute values. The derivative uses the exact Chebyshev differentiation recurrence. It also evaluates the split independently at 33 combinations of size and step for a pair of test polynomials. Run `python3 -B verify_gamma_polynomials.py` from the checkout. These bounds certify the polynomial residual on a continuum of frequencies. Transferring them to the lattice input errors and then to adjacent coefficient signs requires further estimates.

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

## The density at 125000 pairs

For $N\ge125000$ take $U=85$, $\tau_* = .0007$ and use the same half-unit bins and input polynomials. All cosine and sinc arguments still have modulus below $.8$. Enlarge the gamma windows to $W=[\max(0,.88a-1),1.12b+1]$. At tilt $\lambda=.12$ the probability of $|\tau(T-j)|>.12v+1$ is at most $3\exp(-.004j-.12/\tau)$, since $.12\lambda-\lambda^2/(2(1-\lambda))>.004$. In the Cauchy–Schwarz exceptional bound replace $.015/\tau_*$ by $.06/\tau_*$ and use the new $\tau_*$. The result is still below $10^{-16}$. For late returns $j>N/20\ge6250$ the Wallis and segment estimates still give factors $1.01$ and $240$, as checked at the lower endpoint.

In removing the final gamma average take derivative suprema on $[.95a,1.05b]$. Tilt $\pm.04$ gives probability at most $3e^{-N/1000}$ outside that window, since $.05(.04)-(.04)^2/(2(1-.04))>.001$. The previous exceptional cost is at most $2\cdot10^6e^{-N/2000}<N^{-2}$. The sum of the averaging and return errors in the density integral, including $2/\pi$, is below $.05656$.

Only the order-zero tail is needed. The existing $100e^{-.162u}$ bound for both laws costs at most $.01190$ beyond $U$. For the lattice arc past $|\theta|=.001$ integrate $8e^{-u/101}$ from $v=2N/100$. Its contribution including $2/\pi$ is at most
$$ \frac{24\sqrt v\,e^{-v/101}}{\pi(1/101-1/(2v))}<.000001. $$
This uses $\sqrt{v+t}\le\sqrt v\,e^{t/(2v)}$. Together the errors are below $.069$. All terms decrease as the size exceeds the stated lower bound, or are uniformly bounded there by the same fixed integral. The [verifier](verify_local_returns.py) uses rational enclosures for all three terms. The application to coefficients uses this density estimate at two separated sites. [Odd-part reflected comparisons](type-b-transfer.md#from-a-failed-comparison-to-an-odd-part-valley)
