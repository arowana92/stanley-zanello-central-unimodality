# A shorter walk controls the clock error under an area tilt

**Theorem.** For every $n\ge10^{17}$, the odd staircase $(2n-1,2n-3,\ldots,1)$ and the even staircase $(2n,2n-2,\ldots,2)$ in Stanley and Zanello's Conjecture 3.4 have unimodal rank sequences. Together with the [finite certificates](certified-window.md) this leaves $2049\le n<10^{17}$ open.

Put $m=2n$ or $2n+1$, $s=m^{3/2}$ and $\epsilon=m^{-1/2}$. A surviving simple walk has corank $K=\sum_{i=1}^m\lfloor H_i/2\rfloor$. Write $b_k$ for its number of paths of corank $k$. We use two estimates. Splitting lost Fourier mass at the first hit of the wall gives cancellation on the remaining steps. A shorter walk bounds the Brownian area weight on exceptional clock events, so the clock error can be tested at a smaller displacement. The [rational checks](verify_prefix_clock.py) use $m\ge 2\cdot10^{17}$ throughout.

## A Fourier block stopped at its first hit

Let $\theta$ be the absolute lattice frequency and $L=\lceil9\theta^{-2/3}\rceil$ for $0<\theta\le10^{-9}$. Under independent signs with up probabilities in $[.4999,.5001]$, the sum over endpoints of the absolute unrestricted transforms of a block of $d\le L$ steps is at most
$$ \rho_d=\exp[-.99(d^3-d)\theta^2/96]. $$
Pair the first and last positions, then the second and penultimate positions, and continue inwards. Fixing the sum in each pair fixes the endpoint. For a mixed pair with probabilities $A,B$ and separation $v$, its two phases differ by $v\theta$. The loss in modulus is at least $2AB\sin^2(v\theta/2)/(A+B)$. Since $L\theta<.01$, this is at least $.99v^2\theta^2/16$. Averaging the pair moduli and multiplying gives the assertion by $\sum v^2=d(d^2-1)/6$. The phase computation holds for both the down-label sum and the symmetric edge area of the [walk transfer](effective-small-area.md#real-transfer-operator). Terms depending only on the endpoints have constant phase there.

Start the block at height $b\ge0$ and let $\tau$ be the first hit of $-1$. Subtract from the unrestricted transform the paths with $\tau\le L$. Conditional on the first hit and prefix, the remaining unrestricted steps have row bound $\rho_{L-\tau}$. Thus the killed row norm is at most $\rho_L+\mathbb E[1_{\tau\le L}\rho_{L-\tau}]$. For the fair law, and also for any homogeneous upward bias,
$$ \rho_L<.00055,\qquad \mathbb E[1_{\tau\le L}\rho_{L-\tau}]<.171. \tag{1} $$
Indeed reflection at the wall gives $\Pr_b(\tau=j)=a\Pr(S_j=a)/j$ on the compatible parity, where $a=b+1$ and $S_j$ is the fair sum. One can count a first hit by reflecting the paths violating the barrier in the first $j-1$ steps and appending the last down step. At up-bias parameter $u\ge0$ the likelihood on a first hit is multiplied by $e^{-ua}/\cosh^j u\le1$.

For $j\ge200$ one has $\sup_a a\Pr(S_j=a)<.49$. Successive parity masses have ratio $(j-a)/(j+a+2)\le e^{-2(a+1)/(j+1)}$. The central binomial bound therefore gives
$$ \Pr(S_j=a)\le \sqrt{2/(\pi(j-1))}\exp[-(a^2-1)/(2(j+1))]. $$
Maximizing $a e^{-a^2/(2(j+1))}$ proves the claim. To check (1), write $c=.99\cdot9^3/96$. For $j\le L/10$ use $\rho_{L-j}\le e^{10^{-6}-c(.9)^3}$. In each of the ninety bins $j/L\in(v,v+.01]$, $.10\le v\le.99$, use probability at most $.49(.005+10^{-6})/v$ and suffix norm at most $e^{10^{-6}-c(1-v-.01)^3}$. Here $L>10^6$, only one parity occurs and the linear term of $d^3-d$ costs less than $10^{-6}$ in the exponent.

Put $\beta=|h|/s$ for real continuum tilt $h$. The following bounds are for the characteristic function of the normalized surviving area law with weight $e^{-hK/s}$, at scaled frequency $\xi=s\theta$. The continuum law inherits them by convergence at fixed tilt. For positive tilt we use $B=\min(h/2,1.31h^{2/3})$.

| Tilt | Condition | Envelope |
| --- | --- | --- |
| Fair | All $\xi$ in the block's frequency range | $100e^{-.19\lvert\xi\rvert^{2/3}}$ |
| $-18\le h<0$ | $\theta/\beta\ge40$ | $300e^{-.17\lvert\xi\rvert^{2/3}}$ |
| $13\le h\le7^3$ | $\theta/\beta\ge40$ | $100e^{B-.15\lvert\xi\rvert^{2/3}}$ |
| $13\le h\le7^3$ | $\theta/\beta\ge60$ | $100e^{B-.16\lvert\xi\rvert^{2/3}}$ |

For positive tilt write the symmetric real edge weight in one block as $e^{-\beta Lb/2+\beta L/4}\exp(\sum u_i X_i)$ for signs $X_i$ and $u_i=-\beta(L-i+1/2)/2$. Its outside factor is at most $e^{.001}$. The sign tilt gives probabilities in the displayed near-fair interval. Its unrestricted mass is at most $e^{V/2}$ with $V=\sum u_i^2\le \beta^2 L^3/12$. The first-hit contribution, including the real normalization, is bounded by $\mathbb E_0[e^{\sum u_iX_i}1_{\tau\le L}\rho_{L-\tau}]$. This follows by first conditioning the independent tilted signs at $\tau$. Hölder with exponent $p$ bounds this by $e^{pV/2}(.171)^{1-1/p}$, since the suffix norm lies in $[0,1]$.

For negative tilt use the [independent down-label law](mode-comparison.md#fourier-tails-for-the-two-signs-of-tilt). Its natural up parameters decrease by $\beta/2$ per step. Compare each block to homogeneous up bias at the average parameter $\bar u\ge0$. For the normalized likelihood $W$ relative to that law,
$$ (\mathbb E_{\bar u} W^p)^{1/p}\le e^{(p-1)V/2},\qquad
 V=\sum_i(u_i-\bar u)^2\le\beta^2 L^3/48. $$
For each coordinate this follows from $(\log\cosh)''\le1$, by comparing its values at $\bar u$, $u_i$, and $\bar u+p(u_i-\bar u)$ using the second divided difference. The true probabilities obey the same near-fair pair bound. Apply Hölder to the first-hit term under the homogeneous reference, using (1). Thus for both signs the entire block norm is at most
$$ e^{.001}\left(.00055e^{V/2}+.171^{1-1/p} e^{pV/2}\right). $$
Use $p=10,14$ in the two positive rows and $p=19$ in the negative row. The fair row uses (1) directly.

Retain a prefix of $\lfloor m/64\rfloor$ steps and bound the remaining complete blocks by multiplication. The incomplete block and terminal factor cost at most one in the respective real laws. Since $L\theta^{2/3}\le9.01$, a block norm at most $e^{-c_0\cdot 9.01\cdot64/63}$ gives rate $c_0$ with floor cost at most $e^{c_0\cdot 9.01\cdot64/63}$. The prefix-to-total mass ratio is at most 16 in the fair case and $2(|h|+8)$ in the negative case by the [prefix survival bounds](peak-overlap.md#the-signed-comparison-on-the-peak-scale). At positive tilt the prefix mass is at most $8\epsilon$. The denominator exceeds $.7\epsilon I_h(0)$ by the clock mass test below, with $I_h(0)>.7e^{-B}$. This proves the table independently of Fourier inversion. For $\theta>10^{-9}$ the [full-period bounds](mode-comparison.md#fourier-tails-for-the-two-signs-of-tilt) suffice. Even half the weakest decay exponent there exceeds $m\,10^{-6}/8000$.

## Shortening the walk before testing a clock failure

Let $X_t=1+B_t$ for standard Brownian motion, $C_t$ its survival above zero through time $t$, and $Y_t=\int_0^t X_v\,dv/(2t^{3/2})$. At the successive times $\tau_i$ of unit displacements, the signs generate the walk of heights $H_i$ from zero. The durations $D_i=\tau_i-\tau_{i-1}$ are independent of all signs and are i.i.d. with $\log\mathbb E e^{v(D_i-1)}\le v^2$ for $|v|\le.001$. Use the [radial normalization](localized-mode.md#positive-tests-under-the-random-clock) $Z_*=\epsilon I_h(0)$ and $R=\max(50,r,\sqrt{\log m})$, $r=(\max(h,0))^{1/3}$. We need $h\in[-18,-7]$ or $13\le h\le60^3$.

Take $X_f=41$, $V_f=2\sqrt{mX_f}$, $t_\pm=m\pm V_f$, and the larger duration tolerance $V_c=2\sqrt{mX_c}$ with
$$
 X_c=\begin{cases}
 B+\tfrac12\log m+44,& h>0,\\
 2(1+.084h^2+\tfrac12\log m+44),&h<0.
 \end{cases}
$$
The height bound $M$ is $\lceil10\sqrt m\rceil$ for $h>0,\ r<21$ and $\lceil U\sqrt m/r\rceil$ for $21\le r\le60$, where $U=(60\log m)^{2/3}$. At negative tilt take $M=\lceil\sqrt{2.01mX_c}\rceil+3$.

We first bound the cost of discarding paths above $M$ under the full surviving discrete measure and the Brownian measure at $t_+$. At $0<r<21$ the area weight decreases under pointwise ordering of paths. The fair surviving walk has positive association. Indeed, conditional on survival to the specified time it is Markov, and its one-step laws are stochastically ordered in the current height. Two possible heights differ by at least two and their one-step supports are ordered. Iterating the inverse distribution functions represents the heights as increasing functions of independent uniforms. The product-measure association inequality now applies to maximum and area. The same association holds for Brownian motion from one conditioned to survive to a fixed $t>0$, by taking a finer simple-walk mesh. Donsker convergence applies to the maximum and area, survival has positive probability, and the Brownian minimum has no atom at zero. Thus positive tilting can only lower the upper tail of the maximum.

Under either fair surviving law this tail at $M$ is at most $5e^{-44}$. First hit height $\sqrt m/2$ (rounded up on the lattice) before absorption, of probability at most $2\epsilon$ by gambler's ruin. The remaining climb exceeds $9.49\sqrt m$ and has probability at most $\exp[-9.49^2/(2\cdot1.001)]$ by the exponential maximal inequality. Survival has probability at least $.5\epsilon$ by the central binomial bound on the lattice or Brownian reflection. At $21\le r\le60$ use the [weighted running maximum estimate](tilted-height.md#a-height-estimate-for-each-weighted-law). Its proof applies since $H=\sqrt m/r>7\cdot10^6$, $U>175$, the two excess potential coefficients still exceed $.22,.21$, $5r^2/H<.01$, and $H^2U^2/8192>m/10^7>1.30r^2+10\log m$. Each discarded cost is below $\epsilon^8Z_*$. At $h<0$ the unconditioned Gaussian or walk maximum exceeds the indicated cap with probability at most $4e^{-X_c}$ by the maximal inequality. Cauchy–Schwarz and the [second weight moment](variation-overlap.md#bandwidth-and-error-bounds-outside-the-central-interval) bound the cost in units of $Z_*$ by $3e^{-44}$. This moment estimate uses the Gaussian area at $t_+$ and the independent label sum on the lattice.

Here are the two clock comparisons. For $l\le m$ and $V=2\sqrt{mX}$ with $X=X_c$ or $X_f$, require
$$ |\tau_l-l|\le V,\qquad
 \left|\sum_{i=1}^l [H_{i-1}]_{M+4}(D_i-1)\right|\le V(M+4).
$$
The brackets clamp to $[-(M+4),M+4]$. Given **all $m$ signs**, failure has probability at most $4e^{-X}$ by the centered duration bound at arguments of magnitude at most $V/(2m)<.001$. This conditional estimate holds for every sign configuration.

Write $j=m-\lceil V_c\rceil$ and $K_l=\sum_{i=1}^l\lfloor H_i/2\rfloor$. For $l=m,j$, let $F_l$ be the unconditioned mass of surviving paths through $l$ with heights at most $M+2$, weighted by $e^{-h K_l/s}$. The common denominator $s$ is used at both lengths. We claim
$$ F_l/Z_*\le 1.01e^{|h|d_c},\qquad d_c=4\epsilon+4V_c(M+4)/s. \tag{2} $$
Given any of these sign paths, the two clock comparisons at $(l,V_c)$ succeed with probability at least $1-4e^{-X_c}$. On success $t'=l-V_c\le\tau_l$, hence $C_{t'}$ holds. Also $|K_l/s-Y_{t'}|\le d_c$. For detail, $2K_l=\sum H_{i-1}+H_l-\lceil l/2\rceil$, and $X$ during a crossing differs by at most two from its starting walk height. The duration comparison bounds the error in $\sum H_{i-1}D_i$. Moving the terminal time costs at most $|\tau_l-t'|(M+4)/(2s)$ and changing the denominator costs at most $.76|t'-m|(M+4)/s$, by differentiation for times within $.001m$ of $m$. These bounds also give $d_c$ when $l=j$, $t=t_+$ on a Brownian surviving path capped through $t_+$, provided the $(j,V_c)$ comparisons hold. Indeed $\tau_j\le m\le t_+$, $|\tau_j-t|\le3.01V_c$, and $|t-m|\le2.01V_c$ in all these uses.

At $t'$ the unconditioned Brownian surviving weight divided by $Z_*$ is at most $e^{|h|\epsilon+3\epsilon R^2}+\epsilon^8$. This is the radial starting-point comparison with test one. Its change of time still fits in the exponent because $5V_c/\sqrt m<R^2$, using $X_c\le2R^2$, $R\ge50$. The same comparison at $t_\pm$ applies to arbitrary nonnegative tests using displacement $\epsilon$, with discarded error at most $\epsilon^8$ times the test supremum. Applying this mass bound at $t'$ and dividing by $1-4e^{-X_c}$ proves (2).

For the upper test comparison retain the capped surviving $m$-step walk and discard failure at $(m,V_f)$. The discarded clock weight is at most $4e^{-41}F_m$. For the lower comparison start with $C_{t_+}$ and its cap. First discard failure at $(j,V_c)$. Its unweighted probability is at most $4e^{-X_c}$, giving relative weight cost below $6e^{-44}$ by $I_h(0)>.7e^{-B}$ at positive tilt or by the second-moment bound at negative tilt. On what remains, survival through $j$ and its cap are automatic and $e^{-hY_{t_+}}\le e^{|h|d_c}e^{-hK_j/s}$. Consequently the additional loss from failure at $(m,V_f)$ is at most
$$ 4 e^{-41+|h|d_c} F_j . \tag{3} $$
Here we enlarged the event after comparing the weights and conditioned only on signs. This step is what permits $X_f$ to be held fixed even for small $I_h(0)$.

On success at $(m,V_f)$, $\tau_m\in[t_-,t_+]$. The upper comparison uses $A_m\subset C_{t_-}$ and the lower one uses $C_{t_+}\subset A_m$ on this event. The area calculation above now gives
$$ |K_m/s-Y_t|\le\eta=3\epsilon+2.27 V_f(M+4)/s $$
for the respective time $t$. The three coefficients of $V_f(M+4)/s$ are $.5$ for the duration sum, one for the terminal interval and $.76$ for scaling. The upper cap controls heights through $\tau_m$ and the lower cap through $t_+$.

It follows that the [positive test bounds](variation-overlap.md#testing-displacements-by-total-variation) hold with $d=\eta+\epsilon$, $u=|h|d+3\epsilon R^2$, $E=100e^{-38}$. In detail, sandwich each nonnegative test by its infimum and supremum on a displacement interval and apply the radial comparison at the two deterministic times. The verifier gives $2|h|d_c<2$ and $(|h|+3R^2)\epsilon<.0006$. Thus (2) bounds each $F_l$ by $3Z_*$. In the association estimate the full discrete mass is at most $F_m/(1-5e^{-44})$ for that range of tilts. Equations (2)–(3), both cap bounds, and the discarded radial terms, allowing a factor $e^u<1.16$, fit in the stated $E$. The mass test now puts the full discrete mass in $(.7,1.4)Z_*$. No Fourier estimate enters this derivation.

## Adjacent signs on the peak scale

Let $x=k/s$, let $f$ be the density of half the unit Brownian meander area, and put $g=\log f$. Its tilt $f_h\propto e^{-hx}f$ has its maximum at $x$ when $h=g'(x)$. The [small-corank theorem](variation-overlap.md#a-uniform-interval-in-corank) already proves $b_{k+1}>b_k$ for $k\le s/70$ at every $n\ge10^{17}$. For $1/70\le x\le1.5$ the existing slope and mode bounds give $-18\le h<60^3$. We check the signs throughout that interval.

In the fair comparison set $z=x+(m+\lceil m/2\rceil)/(2s)$. The [centered crossing-clock estimate](centered-clock.md#fourier-inversion-and-the-peak) costs $10^4(1+|t|)^2/m$ for either parity in the shifted characteristic function. Invert with cutoff $T=1250$. Above it both fair transforms satisfy the first-hit envelope up to $\theta=10^{-9}$, and the continuum satisfies it on the whole line. For derivative order $i=0,1,2$, put $b=3(i+1)/2$ and $w=.19T^{2/3}$. The two tails in the inversion integral cost at most
$$ \frac{300}{\pi}(.19)^{-b}\frac{e^{-w}w^{b-1}}{1-(b-1)/w} $$
apart from the lattice tail above $\theta=10^{-9}$. That tail and the lattice difference multiplier errors cost below $10^{-10}$ by the [fair full-period envelope](peak-rate.md#fourier-inversion-for-lattice-differences). Adding the integral below $T$ gives absolute errors below $.000013,.012,12.6$ in $sP_m(k),s^2\Delta P_m(k),s^3\delta^2P_m(k)$ relative to $f(z), f'(z), f''(z)$.

For $1\le h\le13$, $f'(x)\ge h e^{-h/2}\sqrt{6/\pi}$. Subtracting $3300000\epsilon$ for the shift leaves $f'(z)>.012$. At $1\le q=-h\le7$, the [Gaussian regression and slope argument](variation-overlap.md#the-central-interval-and-bounded-negative-tilts) gives $-f'(z)\ge1.78q\exp[-.65q-q^2/24-12(1.501)\epsilon-6\epsilon^2]>.012$. Each minimum occurs at a range endpoint. At $|h|<1$, $g''\le-12$ puts $x$ within $1/12$ of the mode, where $f$ is at least $1.78$. Integrating the slope gives $f''(x)\le-11\cdot1.78 e^{-1/12}$. The shift costs at most $10^9\epsilon$, leaving $f''(z)<-12.6$. These are, respectively, strict growth, strict decline, and negative centered second difference for the lattice coefficients.

For other tilts let $\mu_k=2^{-m}b_k e^{-hk/s}/Z_*$. The sign test is $s\mu_k+As^2(\mu_{k+1}-\mu_k)>0$ with $A=[s(1-e^{-h/s})]^{-1}$. Expanding the weights shows that the left side is a positive multiple of $(b_{k+1}-b_k)/(1-e^{-h/s})$. Its limiting counterpart is $f_h(x)+Af_h'(x)=f_h(x)$. The [signed Fourier kernel](variation-overlap.md#testing-displacements-by-total-variation) tests this inequality at bandwidth $T$. The positive test estimate just proved bounds its relative loss by
$$
 \sinh(u)(1.76+1.63|A|T)+e^u dT(1.63+1.69|A|T).
$$
Take $T=(25/.17)^{3/2}$ at $h\le-7$. For $13\le h<7^3$, take $T=((27+B)/c)^{3/2}$ with $c=.16$ through $r=4$ and $c=.15$ thereafter. At and above these cutoffs all the frequency-ratio requirements in the first-hit table hold. The weighted tail integrals cost below $.003$ together up to $\theta=10^{-9}$, including both laws. To see this, substitute $w=c|\xi|^{2/3}$ into the envelope integral with weight $1+1.001|\xi/h|$. Bound the two resulting incomplete gamma integrals by $e^{-w}(w+1)/\sqrt w$ and $e^{-w}(w^2+2w+2)$ at the cutoff. The verifier uses the highest polynomial value and lowest exponential margin in each tilt range. The full-period estimate adds less than $.001$.

For $7\le r\le60$ use the [intermediate-frequency bands and end blocks](variation-overlap.md#bandwidth-and-error-bounds-outside-the-central-interval), with the following cutoffs.

| $r$ | $T/r^3$ | $r$ | $T/r^3$ |
| --- | ---: | --- | ---: |
| $[7,8)$ | 35 | $[15,21)$ | 8 |
| $[8,9)$ | 25 | $[21,30)$ | 4.5 |
| $[9,12)$ | 20 | $[30,42)$ | 3 |
| $[12,14)$ | 12 | $[42,54)$ | 2 |
| $[14,15)$ | 10 | $[54,60]$ | 1.5 |

The additional cutoff at $r=8$ follows by summing the same bands starting at 25. Their total above each cutoff through $|\xi|/h=150$ is below $.022 f_h(x)$. All uses of the real grid estimate and boundary factors apply at $H>7\cdot10^6$. In particular the real energy comparison at the shifted heights costs less than $.00001$ in height-block units by the [grid error at real tilt](airy-grid.md), the $1.48/H^2$ gap holds there, and the harmonic spacing satisfies $100\cdot150/H<\pi$. The previous two bounds beyond 150 each cost less than $.001 f_h(x)$, using $N=n/H^2\ge.49r^2$.

Across the cutoffs $u<.14$, $T<500000$, $T/|h|<500$, and the relative loss displayed above is below $.95$. The checks bound the terms separately on closed rational intervals. All size-dependent upper bounds needed here are decreasing in $m$ at fixed tilt after multiplication by $\epsilon$. For example, $\epsilon\sqrt{X_c}U$ has total logarithmic degree at most $7/6$ and $\log m>39$. The verifier uses $\log(2\cdot10^{17})<40$ and $U<180$ at the lower endpoint. The remaining errors are bounded as in the signed kernel proof: $2ET(1+|A|T)<.001$, the difference multiplier costs less than $.001$ by $4(2T)^3/s$, and the continuum tail carries a factor at most $\cosh u<1.01$. Because $f_h(x)\ge\sqrt{6/\pi}>1$, the signed functional is strictly positive. This gives $b_{k+1}>b_k$ for positive $h$ and $b_{k+1}<b_k$ for negative $h$.

As $k$ increases, $g'(k/s)$ decreases. The two strict first-difference signs, with strictly decreasing differences in the intervening $|h|<1$ interval, allow at most one change from growth to decline. At the outer ends these intervals join the small-corank theorem and the [first-passage and lower-half inequalities](rising-window.md). This proves unimodality in the stated range for both parities. The first-hit estimates and clock comparisons here are analytic bounds with rationally checked constants. The exact small-shape check and the separate finite certificates do not interpolate across the outstanding size gap.

~~~sh
python3 -B verify_prefix_clock.py
python3 -B verify_variation.py
python3 -B verify_centered_clock.py
python3 -B verify_airy_powers.py
python3 -B verify.py --max-n 64 --direct-n 12 --upper-curvature
~~~
