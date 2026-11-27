# Both central staircases are unimodal from $10^{22}$ rows

**Theorem.** For $n\ge10^{22}$ both staircase rank sequences in Conjecture 3.4 are unimodal. The [finite certificate](certified-window.md) covers $1\le n\le2048$. The outstanding gap is $2049\le n<10^{22}$.

Write $m=2n+\delta$, $s=m^{3/2}$ and $b_k=a_{D-k}$. The [transfer-power theorem](airy-powers.md) gives strict increase in $k$ through $.01s$. For the next part of the row use $x=k/s$, the density $f$ of half the unit Brownian meander area, $g=\log f$ and $h=g'(x)$. The normalized tilted density $f_h$ has its mode at $x$.

## The peak and its decreasing side

For $m\ge2\cdot10^{22}$ the [centered-clock inversion](centered-clock.md#fourier-inversion-and-the-peak) gives uniform error below $.000012$ in the scaled forward difference compared with $f'(z)$, $z=x+c_m/s$, $c_m=(m+\lceil m/2\rceil)/2$. Take cutoff 4000. The low frequencies cost $10^4\int_0^{4000}t(1+t)^2\,dt/(m\pi)$, and the two high-frequency tails are bounded there by the incomplete gamma estimate with $.12T^{2/3}>30.23$. The remaining lattice errors cost less than $10^{-12}$.

Write $x_*$ for the mode. We have $f(x_*)\ge1.78$ and $x_*\le.65$ by the [finite mode bounds](mode-bounds.md) and the uniform density approximation and convergence of the modes. When $h\le-1$ and $x\le1.5$, $z$ lies to the right of the mode and $g'(z)\le-1$. The [Gaussian regression inequality](airy-overlap.md#the-decreasing-side-in-corank) gives $f(z)\ge1.78e^{-6z^2}$. Through $z=1.37$ this suffices. From there to $1.501$, use $-g'(z)\ge12(1.37-.65)$ by strong log-concavity. In both ranges $-f'(z)>.000012$, so $b_{k+1}<b_k$.

For $1\le h\le20$, [the tilted-mode estimate](airy-overlap.md#the-decreasing-side-in-corank) gives $f'(x)=h f(x)\ge\sqrt{6/\pi}\,e^{-10}$. The shift to $z$ costs at most $3300000/\sqrt m$ using the bound on $\|f''\|_\infty$ there. This gives $f'(z)>.000012$ and strict corank growth. At $|h|<1$, $f''(x)<-12.3$. Using $\|f'''\|_\infty<10^9$, the shift costs below $.01$, and the centered second-difference error is below $2.3$. Thus the centered second difference is strictly negative.

## Positive tilts needed after the transfer-power interval

At $h=r^3$, $r\ge100$, the mode of $f_h$ is below $a/(3r)+7/r^2$. To see this, take the auxiliary-length limit in the [tilted concentration proof](tilt-concentration.md#width-of-the-continuous-tilted-law) with $\beta=r^3/s$ and $N=nr^2/m\to r^2/2$. For shifts $w=\pm1/r$ the amplitude ratio is below $1.06$ by [the real amplitude estimate](airy-powers.md#real-boundary-amplitude). At all three real tilts the ratio of the mass to its principal term lies between $.999$ and $1.001$, since $N\ge.49r^2$ eventually and both shifted heights tend to infinity. Relative to $v=-np'(\beta)/s$, the exponential moments at $\pm r^2$ are thus at most $(1.001/.999)1.06\exp(.34N/r^2)<8$. The grid slope gives $v\to a/(3r)$. Pass to the limit by truncation. The interval of radius $5/r^2$ about this center contains mass at least $1-16e^{-5}$, with mean density above $.089r^2$. A mode at distance at least $7/r^2$ would force density at least that average on the next interval of length $2/r^2$, by monotonicity, contradicting total mass one. Since $a<2.60$, the mode lies below $.01$ for every $r\ge100$. Hence after $k=.01s$ it is enough to consider $r<100$.

For $h\ge20$ use the [two positive tests for the signed kernel](holder-blocks.md#a-kernel-for-the-adjacent-coefficient-sign) with these cutoffs. The frequency variable $\xi$ is dual to $k/s$.

| Tilt | Bandwidth $T$ |
| --- | ---: |
| $20\le h<(4.5)^3$ | $((55+h/2)/.115)^{3/2}$ |
| $4.5\le r<11$ | $((55+1.31r^2)/.115)^{3/2}$ |
| $11\le r<15$ | $20r^3$ |
| $15\le r<20$ | $15r^3$ |
| $20\le r<30$ | $10r^3$ |
| $30\le r<50$ | $4.5r^3$ |
| $50\le r<100$ | $225r^2$ |

Put $B=h/2$ in the first row and $B=1.31r^2$ thereafter. The Brownian normalization satisfies $I_h(0)>.35e^{-B}$. In the first row use Jensen. From $r=4.5$ the [limiting normalization proof](airy-overlap.md#positive-tilts-between-the-peak-and-the-saddle) gives $I_h(0)\ge.08r e^{-ar^2/2}$. Indeed in the auxiliary-length limit the warm-boundary error $20000\exp[-1.48(r^2/2-2.01)]$ is already below $.20$, and $c>.1/H$. Thus in the first two rows the [fair suffix estimate](peak-overlap.md#the-signed-comparison-on-the-peak-scale) has prefactor at most $100e^B$. The tail integral including weight $1+1.001|\xi|$ and both laws costs less than $.001$ by the [earlier gamma bound](verify_airy_overlap.py), since $.115T^{2/3}-B=55$ and $55+B<350$. The additional lattice frequencies above $s/1024$ cost below $.001$ using the full-period envelope there. The lattice-to-continuum mass factor is bounded by $1.4$ below.

## Tilted Fourier blocks at intermediate frequencies

For the third through fifth rows put $H=\sqrt m/r$, $N=nr^2/m$, $y=\xi/r^3$. Peel $\lceil H^2\rceil$ pairs at both ends. In units $c\lambda^n$ their norm product relative to the removed ground powers is at most $100 e^{2\cdot2.61(1+H^{-2})}<20000$. For a block of $l=\lfloor c_0H^2\rfloor$ pairs, take exponent $p_0\ge2$ in the [Hölder block proof](holder-blocks.md#a-block-inequality), and conjugate exponent $b=p_0/(p_0-1)$. Using $(\cos u)_+^{p_0}\le\cos^{4p_0}(u/2)$ gives a binomial average over harmonics $-2p_0,\ldots,2p_0$. At $|y|\ge Y$ its moment factor before taking the $p_0$th root is at most
$$ M=2^{-4p_0}\sum_{j=-2p_0}^{2p_0}\binom{4p_0}{2p_0+j}
      \exp[-j^2(.999c_0)^3Y^2/16]. $$
Here $2p_0 l|\theta|\le\pi$ throughout $|y|\le10^4$, $\theta=\xi/s$, since $H>10^9$. The comparison of real energies by [the grid estimate](airy-grid.md) costs at most $\exp(c_0[a(1-b^{-1/3})+.00001])$ per block. Indeed the linear correction cancels, the quadratic correction is nonpositive and the remaining errors are below $.00001$ at these heights. The following values give relative norms at most $e^{-c_0 C}$.

| $Y$ | $c_0$ | $p_0$ | $C$ |
| ---: | ---: | ---: | ---: |
| 20 | .45 | 2 | .72 |
| 15 | .50 | 2 | .50 |
| 10 | .70 | 3 | .28 |
| 45 | .25 | 2 | 1.60 |

At least $(N-3)/c_0$ whole blocks fit after the two ends, since $c_0\le.70$. In the three intermediate cutoff rows, up to $|y|=45$ the weighted tail costs at most
$$12\cdot20000\,r^3\cdot45(1+1.001\cdot45)e^{-C(.49r^2-3)}<.001.$$
The factor 12 covers both laws, both signs, the ratio to the actual ground mass and the lattice normalization. Each bound decreases from the row's lower endpoint. From 45 to $10^4$ replace 45 in the volume by $10^4$ and use $C=1.60$. Beyond $10^4$ the middle of at least $1.93n$ steps gives $2\cdot20000e^{-N|y|^{2/3}/80}$ by the [full-period estimate](harmonic-small-area.md#comparing-two-frequencies). Extract $e^{-460N/160}$ and integrate $(1+1.001y)e^{-y^{2/3}/4}$, since $N/160>1/4$. These last two tails each cost below $.001$. The continuum inherits the same bounds at each fixed tilt by the auxiliary-length limit.

For the last two rows use the [longer boundary blocks](airy-overlap.md#positive-tilts-between-the-peak-and-the-saddle). At $r\ge30$ the range $|y|\ge4.5$ already has combined cost below $.002$. In the final row integrate also from $225r^2$ to $4.5r^3$. Use $v=|\xi|/r^2$, $c_1=.00093(.49-42/50^2)$, and the envelope $e^{-c_1v^2}$. The combined cost is at most $12\cdot100^2(1/225+1.001/50)e^{-c_1 225^2}/(2c_1)<.001$ by Gaussian integration. All these costs are absolute in the signed inversion units, where $f_h(x)\ge\sqrt{6/\pi}>1$.

## Positive-test error and the integer join

Write $\epsilon=m^{-1/2}$. In the positive-test clock comparison take
$$ X=B+\tfrac12\log m+38,\qquad V=2\sqrt{m X},\qquad R=\max(50,r,\sqrt{\log m}).$$
Every discarded good-clock event of probability at most $8e^{-X}$ costs at most $(8/.35)e^{-38}$ after division by $Z_*=\epsilon I_h(0)$ since the surviving weights are at most one. For $r<15$ take $\eta=9.36\epsilon X$ as in the [unweighted-clock proof](holder-blocks.md#positive-tests-before-normalization). For $r\ge15$ take $\eta=\epsilon(3+4.81U\sqrt X/r)$, $U=(60\log m)^{2/3}$, by the [height-capped clock proof](tilted-height.md#the-clock-error-for-the-retained-paths). Its discarded height probabilities in units $Z_*$ remain below $\epsilon^8$ each. Indeed $U>210$, $H>10^9$, $H^2U^2/8192>m/10^7$, $5r^2/H<.01$ and $m/10^7>1.3\cdot100^2+10\log m$. These give the two excess-potential bounds $.22,.21$ and absorb the discarded Gaussian tails as in that proof.

The analog of the [unnormalized test inequality](holder-blocks.md#positive-tests-before-normalization) has the same exponent $u_L=(h+L)(\eta+\epsilon)+3\epsilon R^2$. For clarity, its additive error on each side is at most $100e^{-38}\|v\|_\infty$: the clock, capped-height and radial-endpoint discarded terms obey the preceding bounds and $\epsilon^8$ bounds of the positive-test proof, even after multiplication by $e^{u_L}<1.1$ for $L\le3T$. Also $V/m<.001$ and $2V/m+2\epsilon R^2+2\epsilon^2\le3\epsilon R^2$. This argument uses the normalization lower bound before taking any Fourier integral.

The [rational verifier](verify_power_overlap.py) bounds $u_0<.02$, $u_{3T}<.08$ and
$$ \sinh(u_{3T})(2.81+4.06\cdot1.001T/h)<.94. $$
It subdivides the first two rows into intervals of length at most one in $h$ or $.05$ in $r$ respectively, and the other rows into unit intervals in $r$. On each interval it uses upper bounds for $T,h,\eta$ and $T/h$ separately. At fixed $r$, the factors $m^{-1/2}$ times logarithmic powers through degree $7/6$ decrease with $m$ in this range. Thus the endpoint $m=2\cdot10^{22}$ controls the suprema, with $\log m<52$ and $U<215$ there. The mass test gives mass in $(.7,1.4)$ for the lattice law in units $Z_*$. Also $T<2300000$, $T/h<1000$, so the total additive error for the two signed tests is below $.001$ after multiplying by $T$. The lattice multiplier error is below $.001$ by $4(2T)^3/s$. Applying the [signed kernel inequality](holder-blocks.md#a-kernel-for-the-adjacent-coefficient-sign), whose continuum target is $f_h(x)>1$, leaves a positive margin after both Fourier tails. Hence $b_{k+1}>b_k$ at these positive tilts.

The small-corank theorem covers every integer $k\le .01s$. For $x\ge .01$ the positive-tilt cap and the increasing, strictly concave and decreasing regions just proved apply through $x=1.5$. The decreasing function $g'$ orders these regions. In the middle the centered second difference at $k$ says that the forward difference at $k$ is strictly smaller than at $k-1$. Consequently the forward differences cannot turn positive after becoming negative. Beyond $1.5s$ the [first-passage inequality](rising-window.md) and the [lower-half rank inequality](monotonicity.md#1-lower-half-for-all-sizes) continue weak decrease in corank, including the middle step in odd degree. This proves the theorem for both parities.

~~~sh
python3 -B verify_airy_powers.py
python3 -B verify_power_overlap.py
python3 -B verify_airy_grid.py
python3 -B verify_airy_overlap.py
~~~
