# Descent to fewer than 300,000 rows

**Theorem.** If either central staircase fails unimodality at some $n\ge300000$, then the odd-part staircase fails at some $33000<h<300000$. In particular Conjecture 3.4 for both families is equivalent to unimodality in both families for $2049\le n<300000$. The [existing finite certificate](certified-window.md) covers the smaller sizes. A [moment argument](moment-comparisons.md) restricts the coranks needed at these sizes. The [finite Fourier certificate](fourier-window.md) verifies that interval in both families.

The single-step statement is stronger. A failure at $n\ge300000$ forces an odd-part failure at $.11n<h\le n$, with $h<n$ if the starting row is odd-part. The strict decrease in row count comes directly from Stump's recurrence. For comparison, it already gives a cutoff of one million by using the earlier [reflected comparisons and peak bounds](type-b-transfer.md) in the same argument. Neither descent theorem needs the conjectural type $B$ diagonal coinvariant specialization.

## Descent in the two recurrences

Use corank $k$, the number of missing cells, and write $B_n,O_n$ for the odd- and even-part polynomials. Their ballot lengths are $m=2n$ and $2n+1$ respectively. Write $C_l$ for the ordinary Dyck area polynomial and $B_0=C_0=1$. We use
$$
 B_n=C_n+\sum_{h=0}^{n-1}q^{2h+1}B_h C_{n-h},
 \qquad O_n=\sum_{h=0}^n q^h B_h C_{n-h}. \tag{1}
$$
The first identity is Stump's area recurrence. The second follows by cutting a ballot path at its last zero. [Stump, Theorem 3.1](https://arxiv.org/pdf/0808.2822#page=9) · [Derivation for both staircases](README.md#catalan-recurrences-for-the-two-families)

For the one-million cutoff there is a short way to see why the same comparison works in both recurrences. At a decreasing step before the known suffix, $2k+1<D_{\rm mix}(n)$ in the notation of the [earlier proof](type-b-transfer.md#a-descent-in-the-even-part-row). The term $C_n$ has endpoint sums at least $D_A(n)\ge D_{\rm mix}(n)$. In the sum for $B_n$ the monomial shift $2h+1$ exceeds the shift $h$ in the sum for $O_n$. Thus the same telescoping test forces a failed comparison with index sum at most $D_B(h)$, at some $h>n/8$. The earlier density lemma turns this into an odd-part failure. Equation (1) has excluded $h=n$ on the odd-part side, so repetition terminates below one million. The estimates that follow lower that cutoff.

Three estimates proved below will be used. Write $s=m^{3/2}$.

1. For $n\ge300000$ the part of either row from $\lceil .1375s\rceil$ onward is unimodal and contains all global maxima.
2. A unimodal $B_h$ satisfies $[q^i]B_h\le[q^j]B_h$ for $0\le i<j$ with $i+j\le .32(2h)^{3/2}$ whenever $h\ge32000$.
3. At $h\ge47500$ a unimodal $B_h$ satisfies those same comparisons through $i+j\le (2h)^{3/2}/2$.

Each $C_l$ is a sum of intervals $q^u+\cdots+q^v$ with endpoint sum at least $D_A(l)\ge c l^{3/2}-2l$, where $c=2\sqrt2/3$. This follows from the type $A$ diagonal coinvariant theorem and the minimum sum of degrees of $l$ distinct bivariate monomials. [Interval proof and attribution](excursion-centers.md#ordinary-excursions-and-two-variable-characters)

If the row at $n$ fails, take its first strictly decreasing corank step, from $k$ to $k+1$. By estimate 1, $k<\lceil .1375s\rceil$. Put $D=2k+1$. The isolated $C_n$ in (1) has nonnegative difference, since $D<D_A(n)$. Every other summand is a sum of $q^\sigma B_h(q)(q^u+\cdots+q^v)$ with $\sigma=2h+1$ or $h$. Some difference is negative, so telescoping gives
$$
 [q^i] B_h>[q^j] B_h,\qquad
 i=k-\sigma-v\ge0,\quad j=k+1-\sigma-u>i,\quad
 i+j\le D-2\sigma-D_A(n-h). \tag{2}
$$
Coefficients at negative indices are zero. The following bounds hold for $n\ge300000$ in both parities:

* For $h\le .11n$ one has $D_A(n-h)>D$. This also proves the assertion for the isolated $C_n$.
* For $.11n<h\le .16n$ one has $D_A(n-h)+.32(2h)^{3/2}>D$.
* Throughout $0\le h\le n$ one has $D_A(n-h)+(2h)^{3/2}/2>D$.

For the first two bounds divide by $n^{3/2}$ and use $D/n^{3/2}<.275(2+1/n)^{3/2}+n^{-3/2}$. For the first use $c(.89)^{3/2}-2/\sqrt n$. For the second the function $c(1-y)^{3/2}+.32(2y)^{3/2}$ decreases over $0\le y\le .16$ by differentiation, so evaluate it at $.16$ and subtract $2/\sqrt n$. For the third minimize $c(1-y)^{3/2}+\sqrt2 y^{3/2}$ on $[0,1]$. Its minimum is $(c^{-2}+1/2)^{-1/2}=\sqrt{8/13}$. Subtract $2/\sqrt n$ again. The [rational verifier](verify_size_descent.py) checks the three comparisons at $n=300000$, the worst endpoint.

Thus $h>.11n\ge33000$. At $h\le .16n$ apply estimate 2 to (2). At $h>.16n$ one has $h>48000$ and estimate 3 applies. In either case $B_h$ must fail unimodality. In the first recurrence $h\le n-1$. After at most one transfer from $O_n$ to $B_n$, the row counts decrease strictly while they are at least 300000. On the final such step the target still has more than 33000 rows. This proves the theorem.

## Lattice estimates at the three cutoffs

We sharpen the [last-return inversion](localized-returns.md) for the signed walk of length $m+1=2N+\delta$. Set $s_0=(2N)^{3/2}$, $d=(m+1+\lceil m/2\rceil)/2$, $z_k=(k+d)/s_0$. Let $P$ be the corank probability, $F$ the density of half the area of the unit Brownian meander. The entries bound the absolute difference between $s_0 P,s_0^2\Delta P,s_0^3\delta^2P$ and $F,F',F''$ at $z_k$. The first difference is forward, the second centered. Only the density is needed in the first two rows.

| Minimum $N$ | Density | First difference | Second difference | Cutoff $U$ in $u=|\xi|^{2/3}$ |
| ---: | ---: | ---: | ---: | ---: |
| 32000 | .38 | | | 62 |
| 47500 | .12 | | | 69 |
| 300000 | .003 | .121 | 13.6 | 124 |

**Split probabilities.** Keep the free and bridge symbol estimates, convolution inverse, and late first-return estimates of the cited proof. Use bins of width $\Delta=1/4$ and $\tau=u/N$. At time $j$ the convolution splits at $r$ with exact weight $r_r r_{j-r}$, where $r_b=4^{-b}\binom{2b}{b}$. Pair the split with its reversal and let $a$ be the bin of the smaller of $r\tau,(j-r)\tau$. If $j\tau$ is in bin $i$, the larger time is at least $L=\Delta\max(i/2,i-a-1)$ and its bin $b$ is $i-a-1$ or $i-a$. For one orientation, the probability mass in bin $a>0$ is at most
$$ \frac{\Delta+\tau_*}{\pi\sqrt{a\Delta L}} $$
by Wallis and the bound $\Delta/\tau+1$ on the number of indices. At $a=0,i>0$ use $2\sqrt{\Delta+2\tau_*}/(\pi\sqrt L)$. Indeed $\sum_{r=0}^t r_r=(2t+1)r_t\le2\sqrt{(t+2)/\pi}$, using Wallis for $t\ge1$ and checking zero separately. Include the two orientations at each possible $b$ before taking the maximum. Counting the central split twice only increases this upper bound on absolute errors. Use the smaller of the resulting sum and the previous worst-split estimate, which also covers $i=0$.

**Removing the final gamma average.** In the notation of the last-return proof let $f(u),e(u)$ be the meander and excursion cosine transforms at frequency $u^{3/2}$ and $Q_0=(e-f)/(2u)$. For $T$ of gamma shape $N+1/2$ and rate one we compare $\mathbb E(f+\tau V_\delta)(\tau T)$ to $f(u)$. Taylor expand $f$ through degree two at $u=N\tau$ and keep the signed constant $\tau V_\delta(u)$. The total first-order correction is
$$
 \tau\left[(1/12+\delta/2)f'(u)-u f''(u)/30+(\delta/2-3/20)Q_0(u)\right]. \tag{3}
$$
This follows by inserting $V_\delta=-8(uf''+f'/2)/15+(\delta/2-3/20)(f'+Q_0)$ and the first two gamma moments. In addition to (3), charge $3\tau^2|f''(u)|/8$, $u^3\|f'''\|/(3N^{3/2})$, $1.001\,\tau u\|V_\delta'\|/\sqrt N$, and $N^{-2}$. The first term is the constant part of the second moment. For the next two, $\mathbb E|T-N|^3\le2N^{3/2}$ by Cauchy–Schwarz with the second and fourth moments, and $\mathbb E|T-N|\le1.001\sqrt N$. The suprema are over the enlarged final bin for the gamma time. On the exceptional event the bounded values of $f,V_\delta$, and the degree-two Taylor polynomial at $u$, cost at most $2\cdot10^6 e^{-N c_*/2}<N^{-2}$ by Cauchy–Schwarz. Here $u\le124$, $|f'|\le.75\sqrt u$, $|f''|\le.75u$, $\|V_\delta\|\le205$, and the event has probability at most $3e^{-Nc_*}$.

For the needed derivatives use $|Q_0'|\le u/4$ from $Q_0'=\int_0^1 t(e''-f'')(tu)\,dt/2$ and the two second-moment bounds. Differentiation of $\cos(u^{3/2}Y)$ three times gives $|f'''|\le30/32+(27/8)u^{3/2}$ using $\mathbb E Y^2<1/4$, $\mathbb E Y^4<1$ and $|\sin z|\le |z|$. The same two moment inequalities hold for the excursion. At $u\ge4$ differentiate the absolutely convergent [Airy transforms](return-bounds.md#bounds-from-the-brownian-area-transforms) instead and use the better estimate. For the $p$th weighted Airy sum use the previous bound with $p=0,1,2,3$. At $p=3$ its required monotonicity follows from $1/(1+b)+3/b<1$ for $b=3.837$. In bounding $e'$ the unweighted sums are at most the corresponding $(1+a_i)$-weighted sums divided by $1+2.337$. Bound $V_\delta'$ by differentiating its displayed formula.

The intermediate gamma windows have relative width $r$ and additive width $b_0$, meaning $|\tau(T-j)|\le rj\tau+b_0$. The final window has relative width $r_*$. Here are all parameters for the shared rational input and inversion routines:

| $N$ | $\tau_*$ | $r$ | $b_0$ | intermediate tilt | $r_*$ | final tilt | $c_*$ |
| ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| 32000 | .002 | .20 | 2.2 | .19 | .10 | .09 | .004 |
| 47500 | .0015 | .16 | 1.75 | .15 | .08 | .07 | .0025 |
| 300000 | .00042 | .11 | .86 | .074 | .035 | .028 | .0005 |

All cosine and sinc arguments on the retained arc have modulus below one. The sixth-order log remainders $.05x^6,.001x^6$ still hold there by the same Euler-product bound. The gamma checks give the same $10^{-16}$ intermediate exception allowance as before. The late-return bounds $1.01$ and $240$ hold down to $j>N/20\ge1600$. The retained arc lies inside $|\theta|\le.001$, where that return estimate applies.

**Tail beyond $U$.** For the lattice take $L=\lceil9|\theta|^{-2/3}\rceil$ and subtract paths stopped at their first hit of $-1$ from an unrestricted block. On $0<|\theta|\le.001$ take $L_{\min}=900$, sine-square factor $v=.93$, point bound $p=.50$ and rate $\gamma=.1895$. On $.001<|\theta|\le.008$ use $225,.74,.53,.16$ respectively. The unrestricted row norm over $j\le L$ steps is at most $\exp[-v(j^3-j)\theta^2/96]$ by the [opposite-position pairing](prefix-clock.md#a-fourier-block-stopped-at-its-first-hit). This uses $\sin^2x\ge x^2(1-x^2/6)^2$ up to $|x|\le L|\theta|/2$. At a hit time $j>L/10$ one has $\sup_a a\Pr(S_j=a)<p$ by the parity binomial bound in that proof. Hence the first-hit probability is at most $p/j$ on a single parity.

Set $c=9^3v/96$, $d_0=2/L_{\min}$ and $x_+=\max(x,0)$. For late hits integrate on the disjoint cells $[(j-2)/L,j/L]$ of width $2/L$. At a point $w$ therein, $j\ge wL$ and $(L-j)/L\ge(1-w-d_0)_+$. Thus the block norm is bounded by
$$
 e^{L\theta^2/96}\left(e^{-c}+e^{-c(.9)^3}
      +\frac p2\int_{.1-d_0}^1 \frac{e^{-c(1-w-d_0)_+^3}}{w}\,dw\right)
 <e^{-\gamma L|\theta|^{2/3}} .
$$
The second term charges all hits through $L/10$. The verifier bounds the integral on 400 equal intervals, using the left endpoint for $1/w$ and the right endpoint for the exponential. Keeping the initial survival segment of length $\lfloor m/64\rfloor$ as before gives $100e^{-.186u}$ and $100e^{-.157u}$ on the two arcs. The limiting transform also satisfies the first bound by the limit at fixed frequency. On $|\theta|>.008$ use the [full-period lattice bound](peak-rate.md#fourier-inversion-for-lattice-differences) $8e^{-u/101}$.

At order $j$, set $v_j=3(j+1)/2-1$. After the substitution $u=|\xi|^{2/3}$, integrate $300u^{v_j}e^{-.186u}$ from $U$, $150u^{v_j}e^{-.157u}$ from $2N/100$ and $12u^{v_j}e^{-u/101}$ from $2N/25$, with the usual overall factor $2/\pi$. The continuum multiplier error is the previous Airy integral. These estimates and the quarter-unit sums give the table. In each row the bounds are uniform above the indicated $N$, by the fixed bounds on $\tau$ and the negative powers of $N$ in the inverse and removal estimates.

## From density to signs and comparisons

We need derivative information slightly farther to the right in the [cubic Airy contour formula](cubic-tilt.md#a-cubic-contour-for-the-derivative). Its normalized excited-state remainder is below $.01$ up to $x=.29$ for the density and first derivative. To see this take $b=3.837$, $a=a_1$, $x_0=.29$. On each excited term the radial factor relative to the ground, including $|c_i|/c_1$, is bounded by
$$
 W(y)=\frac{1+y}{1.57}(y/2.337)^6
       \exp[-(y^3-2.339^3)/(54x_0^2)],\qquad y=a_i.
$$
The logarithmic derivative of $W$ is below $-7$ for $y\ge b$. At most one energy belongs to $[b,b+1)$. Indeed, consecutive energies up to $b+1$ differ by at least $\pi/\sqrt{b+1}>1$. Translating the Airy eigenfunction at its first interior zero gives the preceding half-line energy by Sturm oscillation. The distance to that zero is at least $\pi/\sqrt{a_i}$ by the Dirichlet Poincaré inequality. The number in $[b+l,b+l+1)$ is at most $1+(b+l+1)^2/3\le10\cdot4^l$ for $l\ge1$. Multiply $W(b)(1+10\sum_{l\ge1}(4e^{-7})^l)$ by the absolute Gaussian moment bound $\mathbb E(1+V^2)^3$ from the contour formula at its worst variance. The verifier gives the stated remainder.

The same Gaussian lower bound for $F'$ with this remainder proves $F'>0$ through $.29$, hence $x_* >.29$ for its mode. The derivative exceeds $.121$ on $[.1375,.25]$. On $[.253,.29]$ its integral exceeds $.26$, by splitting at $.26,.27,.28,.285$. The radial function $r^6e^{-ar^2/6}$ has its minimum at an endpoint of each interval. The previous [peak argument](cubic-tilt.md#the-peak-interval) now applies from $k\ge\lceil .1375s\rceil$. Indeed $z_k\ge k/s$ for $k\le .6s$ and $z_k<.602$ there. The forward-difference error $.121$ is smaller than the left derivative bounds and the right flank bound $1.78e^{-6(.602)^2}$. In the middle the curvature bound $F''<-15.5$ dominates the centered second-difference error $13.6$. The all-size flank inequalities cover $k\ge .6s$. Before the indicated suffix, $z_k<.147$, the density is more than $.10$ below the mode, rounding the mode costs less than $.001$, and the two density errors sum to less than $.006$. This proves estimate 1, including at most two consecutive maximizers.

Finally assume $B_h$ unimodal and use $s_h=(2h)^{3/2}$, $z_i=(i+(3h+1)/2)/s_h$. For a comparison $i<j$ it suffices to find $t\ge j$ with $b_t>b_i$. Use the first grid point at or past $\max(z_j,x_*)$. This site is in the support, since $x_*\le.65$. Rounding adds at most $.0001$ to its squared argument and costs less than $.001$ in density at $h\ge32000$. Use Gaussian regression $F(y)\ge1.78e^{-6(y^2-x_*^2)}$ for $y\ge x_*$ and the [small-area density upper bound](type-b-transfer.md#from-a-failed-comparison-to-an-odd-part-valley).

* If $h\ge32000$ and $i+j\le .32s_h$, then $z_i+z_j<.326$ and $z_i<.163$. The density upper bound at $.163$ plus $2(.38)$ is smaller than $1.78e^{-6(.326^2-.29^2+.0001)}$.
* If $h\ge47500$ and $i+j\le s_h/2$, then $z_i+z_j<.505$ and $z_i<.253$. When $z_j\le.29$ the choice of $t$ rounds the mode. Integrating $F'$ as above gives $F(z_t)-F(z_i)>.26-.001>2(.12)$. For $.29<z_j\le.35$ use $z_i<.215$ and for $z_j>.35$ use $z_i<.155$. In each case the small-area upper bound plus $2(.12)$ is below the regression lower bound using $.35$ or $.505$ as the upper endpoint of $z_j$.

These strict density margins survive both lattice errors. Unimodality gives $b_j\ge\min(b_i,b_t)=b_i$, proving estimates 2 and 3.

## Reproduction

The first command checks all numerical margins above by rational bounds and compares (1) coefficient by coefficient with direct enumeration and the ballot recurrence in the 24 shapes through $n=12$. The other commands reproduce the underlying return and Airy bounds. The range $2049\le n<300000$ in the theorem is a sufficient verification target. The subsequent [proof](proof.md) combines a verification on this target with the analytic estimate above.

~~~sh
python3 -B verify_size_descent.py
python3 -B verify_local_returns.py
python3 -B verify_type_b_transfer.py
python3 -B verify_cubic_tilt.py
~~~
