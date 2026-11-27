# Unimodality at every size from $10^{28}$ rows

Both central staircases have unimodal rank sequences for every $n\ge10^{28}$. Together with [the finite verification](certified-window.md), this restricts a possible counterexample to $2049\le n<10^{28}$. The argument uses the [centered clock estimate](centered-clock.md) near the peak, a shorter oscillatory cutoff at moderate tilt, and the following overlap with the small-corank saddle.

Use $m=2n+\delta$, $\delta\in\{0,1\}$, $s=m^{3/2}$ and $k=D-j$. In the peak argument $h=(\log f)'(k/s)$, $r=\max(h,0)^{1/3}$ and $\epsilon=m^{-1/2}$. In the small-corank argument choose the real saddle $k=-np'(\beta)$ and put $H=\beta^{-1/3}$, $N=n/H^2$. The definitions of the transfer and its energy constant $1.65\le a<2.60$ are in [the two-harmonic estimate](two-harmonics.md).

## The signed comparison on the peak scale

Keep the [positive-test inequality and the two signed tests](holder-blocks.md#a-kernel-for-the-adjacent-coefficient-sign). The cutoff $T$ for their Fourier multiplier is now as follows.

| Tilt range | $T$ |
| --- | ---: |
| $h<0$ | $20000$ |
| $h\ge0$, $r\le4$ | $22000$ |
| $4<r<7$ | $110000$ |
| $7\le r<15$ | $190000$ |
| $15\le r<50$ | $45r^3$ |
| $50\le r<500$ | $500r^2$ |
| $500\le r<1900$ | $170r^2$ |

For the first four ranges apply the [two-frequency row bound](centered-clock.md#fourier-inversion-and-the-peak) after $\lfloor m/64\rfloor$ prefix steps. At positive tilt any retained path has real weight at most one. Use the fair unrestricted block as the reference probability. At negative tilt use the [independent label probabilities](mode-comparison.md#fourier-tails-for-the-two-signs-of-tilt), all in $[.499,.501]$. For $\theta=|\xi|/s\le1/1024$ and $l=\lceil3.25\theta^{-2/3}\rceil$ the unrestricted block at each frequency $d\theta$, $d=1,2$, has modulus row sum at most
$$ \rho_d=\exp[-.24 l\sin^2(dl\theta/2)].$$
For each pair a mixed assignment of its signs has two masses $A,B$, and loses at least $2AB\sin^2(dl\theta/2)/(A+B)$ after its endpoint is fixed. The coefficient exceeds $.24$ for the displayed range of probabilities. Independence gives the bound. Now $l\theta<.33$ and $\sin^2 v\ge.95v^2$ for $|v|\le.33$. Thus $3/8+\rho_1/2+\rho_2/8<e^{-.80}$. Multiplying the block bounds gives $e^{.80-.115|\xi|^{2/3}}$ on the suffix, since $l\theta^{2/3}\le3.26$. The bound at zero follows directly.

At negative tilt prefix survival is at most $(|h|+8)\epsilon$ by the homogeneous drift bound and full survival at least $\epsilon/2$. At positive tilt the prefix costs at most $8\epsilon$, divided by at least $.7\epsilon I_h(0)$ for normalization, justified below by the mass test. Consequently the prefactor on the exponential envelope is at most $8(|h|+8)$ or $32/I_h(0)$ respectively. The limiting law satisfies the same estimates by convergence at each fixed $h$. For $r<7$ use $I_h(0)\ge.7e^{-h/2}$ and for $7\le r<15$ use $I_h(0)\ge e^{-1.31\cdot225}$. Integrating the tail with weight $1+1.001|\xi|$ at $T$ costs less than $.001$ including both laws, both frequency signs, and a possible factor $1.4$ for the unnormalized mass. The elementary bound for the check is $12P(z^2+2z+2)e^{b-z}/(.115)^3$, where $z=.115 T^{2/3}$ and $Pe^b$ bounds the appropriate prefactor. For the additional lattice tail above $s/1024$, the [full-period rates](mode-comparison.md#fourier-tails-for-the-two-signs-of-tilt) $1/4000$ and $1/150$ apply. Even after extracting half the exponential, its exponent in magnitude is at least $m/(8000\cdot 1024^{2/3})$. The last three cutoff rows use the [existing two-harmonic and Hölder tail bounds](tilted-height.md#comparing-the-adjacent-signs-near-the-peak). Their spectral conditions hold here since $\sqrt m/r>7\cdot10^{10}$ and $n r^2/m\ge.49r^2$. In particular the real energy and block estimates hold at this height, and the wider spectral contour applies from height $10^7$.

In the [maximum-height comparison](tilted-height.md#a-height-estimate-for-each-weighted-law) put $U=(60\log m)^{2/3}$. For $m\ge2\cdot10^{28}$ we have $U>240$. With $H=\sqrt m/r$ at $15\le r\le1900$, the two climb-cost coefficients $.22$ and $.21$ still follow using $1/4-1/(4H)-1.305/U>.22$ and $.45/2-1.30(1.001)/U>.21$. Also $H^2 U^2/8192>m/10^7$ and $5r^2/H<.01$. These are the threshold-dependent inputs to the two height tails. The Gaussian discarded cost is again below $\epsilon^8 Z_*/2$ since $m/10^7>1.30(1900)^2+10\log m$. The two maximum-height estimates thus hold with the original $\epsilon^8 Z_*$ bounds. The remaining clock factors in [the comparison](tilted-height.md#the-clock-error-for-the-retained-paths) are bounded at the lower endpoint because $m^{-1/2}(\log m)^c$ is decreasing for all the powers $c\le 7/6$ used there. At that endpoint $\log m<66$ and $U<251$. The bounds $\eta\le2150\epsilon$ for $r\ge15$ and $\eta\le1530\epsilon$ for $r\ge50$ apply when evaluating the endpoint. For $0\le r<15$, $\eta=9.36\epsilon X$ with $X=1.31\cdot225+5\log m+4$.

For the test loss
$$ u_L=(|h|+L)(\eta+\epsilon)+3\epsilon\max(50,-h,r,\sqrt{\log m})^2,$$
these bounds give $u_0<.10$ throughout the table. In particular the mass lies between $.7$ and $1.4$ by using just the positive test $1$, independently of the Fourier estimates. For $|h|\ge1$ the verifier gives
$$ u_{3T}<.10,\qquad
 \sinh(u_{3T})(2.81+4.06\cdot1.001T/|h|)<.50.$$
For negative tilts use $|h|\le1250$, $X=2(|h|+h^2/4+5\log m+4)$. Evaluate $u$ and $u/|h|$ separately. In the last positive range $u$ and $u/r$ both increase in the upper bounds obtained after substituting $1530\epsilon$, so use the right endpoint there. The additive test error and the forward-difference multiplier error are below $.001$ each since $T<7\cdot10^8$. The [signed inversion inequality](holder-blocks.md#a-kernel-for-the-adjacent-coefficient-sign) gives the sign of $b_{k+1}-b_k$ equal to the sign of $h$ whenever $|h|\ge1$ in the stated ranges.

For $|h|<1$ we need the centered second difference at the *unshifted* argument $x=k/s$. Here $f''(x)\le-11 e^{-1/12}\sqrt{6/\pi}<-12.3$. The [centered clock comparison](centered-clock.md#fourier-inversion-and-the-peak) approximates it at $x+c_m/s$ with error below $2.3$. Integrating the limiting Fourier envelope gives $\sup|f'''|\le (60/\pi)(.12)^{-6}\Gamma(6)<10^9$, so replacing the shifted argument by $x$ costs less than $.001$ at the sizes considered. The required second difference is strictly negative.

## The small-corank saddle

Take $x_0=(a/3+.004)/1900$. We prove strict growth at each saddle with $9n\le k\le x_0 s+2$ (and strict log-concavity there). We have $H>4$. The bounds in the middle column use $n\ge10^{28}$ except in the last row, where the slope gives the bound.

| Height $H$ (lower endpoint included) | Lower bound on $N$ | Inversion |
| --- | ---: | --- |
| $4$ to $3000$ | $10^{21}$ | [Flat pairs](flat-pairs.md#inversion-with-a-uniform-number-of-blocks) |
| $3000$ to $2\cdot10^4$ | $2.5\cdot10^{19}$ | Short blocks at $200\le |y|\le400$ |
| $2\cdot10^4$ to $2\cdot10^5$ | $2.5\cdot10^{17}$ | [Previous cubic estimate](tilted-height.md#the-small-area-estimates-at-the-new-size) |
| $2\cdot10^5$ to $2\cdot10^6$ | $2.5\cdot10^{15}$ | Cubic bound $610H^7$ |
| $2\cdot10^6$ to $2\cdot10^7$ | $2.5\cdot10^{13}$ | Cubic bound $130H^7$ |
| $2\cdot10^7$ to $3\cdot10^8$ | $10^{11}$ | [Wider contour](holder-blocks.md#signed-inversion-at-the-small-area-saddle) |
| $3\cdot10^8$ to $2\cdot10^{10}$ | $2.5\cdot10^7$ | Energy comparison through $|y|=.04$ |
| $2\cdot10^{10}$ and above | $1.7\cdot10^6$ | Energy comparison through $|y|=.08$ |

Here $y=\theta/\beta$ and $d=\beta\sqrt{np''(\beta)}$. Use the [shorter centered transform](holder-blocks.md#signed-inversion-at-the-small-area-saddle) for $b=\lceil400H^2\rceil$ pairs and set $x=dy$. Throughout the changed moderate-height rows $d^2/N\in(.0084,116)$. As in the [short-transform estimate with the flat contour](tilted-height.md#the-small-area-estimates-at-the-new-size), $|S(iy)-1|<.001+1600|y|$ and $|S(iy)|\le1.001$. Its real estimate $|S(\pm.04)|<e^{54}$ uses the height-four curvature bound at the shifted scale, the two boundary blocks and $c>.05/H$, all valid from $H=3000$.

For the second row the $l=\lfloor H^2/10\rfloor$ block from [the flat-pair proof](flat-pairs.md#inversion-with-a-uniform-number-of-blocks) has relative norm at most $.8$ for $200\le|y|\le10^4$ by the spacing condition. With at least $9N$ blocks, integer multiples give a Fourier loss in the exponent of at least $.00004Ny^2$ through $|y|=.2$ and at least $.0000017 N$ from $.2$ to $10^4$. In the two changed rows with $H\ge2\cdot10^5$ use the previously established $.003Ny^2$ through $.2$ and $.00008N$ above it through $10^4$. These estimates allow the boundary prefactor $e^{20}$. In these two rows the $1.5H$ nodal cut gives gap $1.48/H^2$ already at $H\ge2\cdot10^5$, giving the spectral disk of relative radius $.16$. Hence the scaled energy error on $|w|\le.04$ is at most $2(12/H)^{.68}$. Cauchy's inequality on $|w|\le.01$ gives the two tabulated cubic bounds. The complementary term on $|w|\le.08$ costs at most $e^{20-.16b/H^2}$ at the shorter length and similarly at the full length. In the second row use the flat complementary bound through $|y|=1.5\cdot10^{-6}$.

For these three rows take $(C,y_0)=(4600,1.5\cdot10^{-6}),(610,10^{-5}),(130,5\cdot10^{-5})$. On $|x|\le3$ the cubic error is at most $27C/(6\cdot.0084d)$. In the [short-transform inversion](holder-blocks.md#signed-inversion-at-the-small-area-saddle) this gives real centered integrand at least $.80e^{-x^2/2}$ for the principal term. For $|x|>3$, $|y|\le y_0$, its modulus is at most $1.002e^{-.35x^2}$, with integral less than $.50$ with weight $1+x^2$. From $y_0$ through $10^4$ the integral is below $.001$ using $2(1+10^4\sqrt{116N})^3\exp(20-cNy_0^2)$, with $c=.00004$ or $.003$ as appropriate. The complementary and high-frequency tails together cost less than $.01$ by the same bounds as in that inversion. Each signed integral exceeds $.5$, including the one with multiplier $4\sigma^2\sin^2(x/(2\sigma))$, $\sigma=d/\beta$.

For the last two rows the real and semidisk energy bounds hold also at the shifted heights needed for the real amplitude. Starting at $2.9\cdot10^8$ or $1.9\cdot10^{10}$ respectively they give
$$
 .34<p''/H^4<.61,\quad |p'''|/H^7<16\quad(|w|\le.02);
 \qquad
 .35<p''/H^4<.60,\quad |p'''|/H^7<1.1\quad(|w|\le.01).
$$
The variance bounds are at real tilt. For both rows $|S(\pm.08)|<e^{11}$ by the [two boundary blocks](two-harmonics.md#signed-inversion-after-twenty-million-blocks-on-the-height-scale) and $p''<.69H^4$ along the shifted segment (in units of the initial height). Thus $|S(iy)-1|<.001+160|y|$. Write $P(iy)=p(\beta(1+iy))-p(\beta)-iy\beta p'(\beta)$.

* In the penultimate row the cubic estimate gives $H^2\Re P(iy)\le-.11y^2$ through $|y|=.02$. This bound continues through $.04$ because the energy error is at most $.0000193$ there and $\Re(1+iy)^{2/3}\ge1+.109y^2$. On the core $|x|\le3$ the real principal term exceeds $.70e^{-x^2/2}$. Beyond three use $1.002e^{-.42x^2}$ through $|y|=.01$, then $1.002e^{-.18x^2}$ from $|x|>29$ to $|y|=.04$. Their total weighted cost is below $.24$.
* In the final row the energy error is at most $.00000112$ on radius $.04$, $2\sqrt{12/H}$ on radius $.065$ and $2(12/H)^{.40}$ on radius $.08$. The first gives $H^2\Re P(iy)\le-.12 y^2$ at $.01\le |y|\le.04$. The next two give $H^2\Re P(iy)\le-.05 y^2$ from $.04$ to $.065$ and from $.065$ to $.08$, respectively. In each comparison add $12/H$ for the energy error at zero. On the core $|x|\le3$ the real principal term exceeds $.35e^{-x^2/2}$. Outside the core use $1.002e^{-.49x^2}$ through $|y|=.01$, then $1.002e^{-.199x^2}$ from $|x|>7.7$ to $|y|=.04$, as in the [earlier integral](holder-blocks.md#signed-inversion-at-the-small-area-saddle). Beyond $.04$ the weaker $1.002e^{-.083x^2}$ starts at $|x|>30$ and costs less than $.001$.

In both rows the $.0034Ny^2$ block estimate controls the Gaussian integral from the last local cutoff through $.2$ with weighted cost below $.001$. The larger frequencies and the complement give the same bounds as in the [Hölder-block inversion](holder-blocks.md#signed-inversion-at-the-small-area-saddle). These estimates again put both signed integrals above $.5$. In each changed row the integral of the absolute transform times $|x|$ is below ten. On the core the principal modulus is below $1.002 e^{e_3}$ where $e_3=27C/(6(d^2/N)d)$, with the Gaussian factor $e^{-(1-b/n)x^2/2}$ retained. The remaining integrals have the weighted bounds just given. Thus the relative change of tilted mass is below $20/\sigma<\beta/4$, while its centered second difference is negative. Undoing the tilt proves strict growth and strict log-concavity at the integer saddle.

Finally the energy error on the $.04$ disk gives $-p'(\beta)/H>2a/3-.001$ in the last row by Cauchy's inequality. Thus $k\le x_0s+2$ implies $N>1700000$ by the [common-energy overlap](holder-blocks.md#the-join-in-corank). For $k<9n$ the [linear tail](finite-tail.md) gives strict growth. Between $x_0s$ and $4s$ the limiting slope satisfies $-1250<h<1900^3$, as in the same overlap. Its decrease with $k$ orders the two strict first-difference signs with negative centered second differences in between. The [first-passage](rising-window.md) and [lower-half](monotonicity.md#1-lower-half-for-all-sizes) inequalities continue the other side through the last corank. This proves global weak unimodality in the claimed size range.

~~~sh
python3 -B verify_peak_overlap.py
python3 -B verify_centered_clock.py
python3 -B verify_tilted_height.py
python3 -B verify_holder.py
~~~
