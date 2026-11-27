# Centering the duration weights in the tilted comparison

**Theorem.** Stanley and Zanello's two central staircases have unimodal rank sequences at every $n\ge10^{16}$. The [tilted pair-deletion proof](tilted-thinning.md) subsequently gives unimodality down to $10^{13}$ rows for both families. The [finite certificate](certified-window.md) covers $n\le2048$. Here $m=2n$ for odd parts and $m=2n+1$ for even parts.

We use the positive tests and Fourier tails of the [shorter-walk comparison](prefix-clock.md). Its fine duration comparison spent separate error allowances on the accumulated area, the terminal time and the time scaling. Subtracting half the permitted height from each duration weight cancels the random terminal-time contribution of that constant. The following calculation uses the signs of both deterministic time corrections.

## Which tilts need a comparison

Write $x=k/s$, $f$ for the density of half the Brownian meander area, $g=\log f$, $h=g'(x)$ and $r=h^{1/3}$ when $h>0$. It suffices to prove $b_{k+1}>b_k$ for $s/35<k<\lceil.18s\rceil$ by the [all-size small-corank theorem](folded-saddle.md) and [unimodality from $.18s$ onward](thinning.md). In this interval $x<.18$ and the limiting mode $x_*>.19$, so $h>0$. For $r\ge7$ the tilted mode satisfies $x<a/(3r)+2.7/r^2$ with $a<2.339$ by the [tilted concentration and real energy bounds](variation-overlap.md#normalization-at-all-positive-tilts-and-location-of-the-tilted-mode). At $r=31$ this lies below $1/35$ and the bound decreases thereafter. Thus $r<31$.

At $h\le13$ use $z=x+c_m/s<.181$, $c_m=(m+\lceil m/2\rceil)/2$. The tilted density $f_h\propto e^{-hy}f(y)$ has maximum at $x$ and maximum value at least $\sqrt{6/\pi}$ by strong log-concavity. Since $\mathbb E Y<1/2$, Jensen gives $f(z)\ge f(x)\ge\sqrt{6/\pi}\,e^{-13/2}>.002$. If $f(z)\ge.15$, then $f'(z)\ge .15\cdot 12(.19-.181)>.015$. Otherwise concavity gives $f'(z)\ge f(z)\log(1.78/f(z))/.65>.015$ since $v\log(1.78/v)$ is increasing here. The [fair first-difference error](thinning.md#inversion-and-signs-around-the-maximum) is below $.015$. This covers every such step, also at the smaller threshold $n\ge10^{13}$.

## A centered displacement estimate

Let $D_i$ be the independent times between successive unit displacements of a standard Brownian motion and $\tau_j=\sum_{i=1}^jD_i$. The durations are independent of the signs of the displacements. For $|v|\le.001$,
$$ \log\mathbb E e^{v(D_i-1)}\le .336 v^2. \tag{1} $$
Indeed the [exit-time transform](mode-comparison.md#smaller-clock-error) gives $-v-\log\cos\sqrt{2v}$, interpreted by the real series for negative $v$. The cosine is at least $1-v+(1/6-.0001)v^2$, bounding its absolute remainder from degree three by $|v|^3/[90(1-|v|/28)]$. With $u=v-(1/6-.0001)v^2$, use $-\log(1-u)\le u+u^2/[2(1-|u|)]$ to get (1).

Put $\epsilon=m^{-1/2}$, $M=\lceil10\sqrt m\rceil$, $C=M+4$, $V=1.16\sqrt{41m}$ and $t_\pm=m\pm V$. Conditional on **any** set of $m$ signs, except on an event of conditional probability at most $4e^{-41}$,
$$
 |\tau_m-m|\le V,\qquad
 \left|\sum_{i=1}^m ([H_{i-1}]_{[0,C]}-C/2)(D_i-1)\right|\le CV/2 . \tag{2}
$$
The brackets clamp to the specified interval. Apply exponential Markov to the sums with weights $1$ and $2[H_{i-1}]_{[0,C]}/C-1$, each of absolute value at most one. The optimizing argument $V/(.672m)$ is less than $.001$ and $1.16^2\ge4(.336)$.

Let $X_u=1+B_u$ and $Y_t=\int_0^t X_u\,du/(2t^{3/2})$. In the upper comparison we have a surviving capped lattice walk, $t=t_-$ and $t\le\tau_m$ by (2). In the lower comparison Brownian motion survives under the cap through $t=t_+$ and $\tau_m\le t$. In either case the walk heights and Brownian heights on the intervals being used are in $[0,C]$. The Brownian path till $\tau_m$ differs by at most two from $H_{i-1}$ within crossing $i$. Thus replacing $2K_m$ by $\sum H_{i-1}D_i-\sum H_{i-1}(D_i-1)$ and then the first sum by $\int_0^{\tau_m} X$ costs at most $M+4+m+2\tau_m< 6m$ in all, using $2K_m=\sum H_{i-1}+H_m-\lceil m/2\rceil$.

In $2s(K_m/s-Y_t)$ the remaining terms are exactly
$$
 -\sum_{i=1}^m (H_{i-1}-C/2)(D_i-1)
 +\int_t^{\tau_m}(X_u-C/2)\,du
 +(C/2)(m-t)+[1-(m/t)^{3/2}]\int_0^t X_u\,du . \tag{3}
$$
The first two terms cost at most $CV/2$ and $CV$ respectively, using $|\tau_m-t|\le2V$. In the last two terms put $\bar X_t=t^{-1}\int_0^t X_u\,du\in[0,C]$. They combine as
$$ (t-m)(-C/2+\gamma_t\bar X_t),\qquad
 \gamma_t=\frac{t-m^{3/2}/\sqrt t}{t-m}\in[0,1.51]. $$
This bound follows by the mean value theorem since $|t/m-1|<.001$. The combined cost is at most $1.01CV$. Dividing by $2s$ therefore gives
$$ |K_m/s-Y_t|\le 3\epsilon+1.26VC/s . \tag{4} $$

## Positive tests at the new threshold

For $13\le h<31^3$ take $B=\min(h/2,1.31r^2)$, $X_c=B+\tfrac12\log m+44$, $V_c=2\sqrt{mX_c}$ and $R=\max(50,\sqrt{\log m})$. The height cap $M$ applies at **all** these positive tilts. In the [positive association argument](prefix-clock.md#shortening-the-walk-before-testing-a-clock-failure), an area tilt can only decrease the fair surviving probability of exceeding $M$. On either clock the fair probability is at most $5e^{-44}$, by first hitting $\sqrt m/2$ before absorption and then climbing a further $9.49\sqrt m$ by time $1.001m$. This argument is independent of the positive tilt magnitude.

Here are the parameters needed to reuse the coarse comparison, including the costs on the discarded events. In its notation $Z_*=\epsilon I_h(0)$ and $I_h(0)>.7 e^{-B}$. For the capped sign weights $F_l$ at $l=m$ or $m-\lceil V_c\rceil$, retain the original **uncentered** coarse comparison at tolerance $V_c$. It gives $F_l/Z_*\le1.01 e^{h d_c}$ with $d_c=4\epsilon+4V_c C/s$. This estimate uses $2.01V_c/m<.001$ and $5V_c/\sqrt m<R^2$, which continue to hold. For the upper test, conditional failure of (2) costs at most $4e^{-41}F_m$. For the lower test first discard coarse failure at the shortened length, of relative weight at most $6e^{-44}$ by $I_h(0)>.7 e^{-B}$. On the remaining event the Brownian weight is bounded by $e^{h d_c}$ times the shorter capped sign weight. Removing failure of (2) then costs at most $4e^{-41+h d_c}F_{m-\lceil V_c\rceil}$, using independence of durations from all signs before restricting the event. These are the same two uses of the shorter walk as in the original comparison. The change of fine duration weights only enters through (2) and (4).

The [radial starting-height comparison](localized-mode.md#positive-tests-under-the-random-clock) adds $\epsilon$ in displacement and $3\epsilon R^2$ in log weight, with discarded cost at most $\epsilon^8$ in units of $Z_*$. Its Gaussian tail is bounded by $4\exp(-R^4/100+16R^2)$, which is below $\epsilon^8$ for $R\ge50$, $R^2\ge\log m$. With
$$ d=4\epsilon+1.26VC/s,\qquad u=hd+3\epsilon R^2, $$
the [positive-test inequalities](variation-overlap.md#testing-displacements-by-total-variation) thus hold with additive error $E=100e^{-38}$ times the test supremum. Indeed $2h d_c<2$, $(h+3R^2)\epsilon<.0006$ and $u<.14$. The bounds just given on both $F_l$ and the fair cap tail then cover the discarded weights, including multiplication by $e^u$. Testing the constant function first places the lattice mass in $(.7,1.4)Z_*$. This justifies the normalization used in Fourier inversion.

Use the [signed adjacent functional](prefix-clock.md#adjacent-signs-on-the-peak-scale) at the mode $x$ of $f_h$, with $A=[s(1-e^{-h/s})]^{-1}$. Its strictly positive sign implies $b_{k+1}>b_k$. Use the same Fourier cutoff $T=((27+B)/c)^{3/2}$ at $r<7$, where $c=.16$ through $r=4$ and $.15$ thereafter. At $r\ge7$ the successive lower endpoints $7,8,9,12,14,15,21,30$ have respective cutoffs $T/h=35,25,20,12,10,8,4.5,3$. The relative loss for testing the truncated kernel is bounded by
$$ \sinh(u)(1.76+1.63|A|T)+e^u dT(1.63+1.69|A|T)<.963 . $$
The [rational verifier](verify_centered_displacement.py) bounds both the displacement and bandwidth on each interval of width $.01$ in $r$ below seven and $.05$ thereafter. At $m_0=2\cdot10^{16}$ we have $\log m_0<38$, $R=50$, $C/\sqrt m<10.00001$ and $|A|T\le1.001T/h$. For larger $m$ the bounds on $\epsilon\sqrt{X_c}$, $\epsilon R^2$ and $C/\sqrt m$ decrease or stay below these endpoint bounds. For the coarse time condition $5V_c/\sqrt m<R^2$, use $X_c\le1.31\cdot31^2+44+R^2/2$ and $R\ge50$.

For clarity, the Fourier tails use the same length-independent first-hit and intermediate-frequency estimates as at the former threshold. At $13\le h\le7^3$ the lattice and limiting tails above $T$ together cost below $.003$ through $|\theta|=10^{-9}$ by the [first-hit table](prefix-clock.md#a-fourier-block-stopped-at-its-first-hit), normalized by the mass test above. Beyond that frequency half the weakest lattice exponent exceeds $2\cdot10^6$, so the tail costs below $.001$. At $7\le r<31$ the height scale $\sqrt m/r$ exceeds $4.5\cdot10^6$. The harmonic spacing requirement $100\cdot150r/\sqrt m<\pi$ and the real energy error budget $.00001$ hold there (even $20r/\sqrt m<.00001$). The real gap, end blocks and $N=nr^2/m\ge.49r^2$ give the [intermediate-band costs](variation-overlap.md#bandwidth-and-error-bounds-outside-the-central-interval), with the [cutoff at eight](prefix-clock.md#adjacent-signs-on-the-peak-scale). The relative cost through $|\xi|/h=150$ is below $.022$ and the two tails above 150 each cost below $.001$. These estimates include both frequency signs and both laws. The continuum tail has an additional factor of at most $\cosh(u)<1.01$ in the signed comparison.

Finally $T<500000$, $T/h<500$ and $f_h(x)\ge\sqrt{6/\pi}>1$. The test error $2ET(1+|A|T)$ and the discrete multiplier error bounded by $4(2T)^3/s$ each cost less than $.001$. Even charging $.026$ for the Fourier tails leaves $.963+1.01\cdot .026+.002<1$. The positive signed functional gives strict growth at every remaining integer step. This completes the proof for both families from $10^{16}$ rows. The analytic inequalities hold uniformly between the parameter endpoints used by the verifier.

~~~sh
python3 -B verify_centered_displacement.py
python3 -B verify_thinning.py
python3 -B verify_prefix_clock.py
python3 -B verify_variation.py
~~~
