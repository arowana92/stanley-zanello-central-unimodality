# Local comparison at the peak of a tilted area law

For both central staircases the rank sequence is unimodal for **every $n\ge10^{61}$**. For **every $n\ge10^{118}$** it is strictly log-concave at every interior rank in the upper half. The [previous tilted-mode argument](tilt-concentration.md) reached these conclusions at $10^{78}$ and $10^{134}$ respectively. We compare the two area laws on positive functions concentrated near the rank being tested. This bounds the inversion error in units of the density at that rank.

Use $m=2n+\delta$ with $\delta=0,1$, $s=m^{3/2}$ and $k=D-j$ with $D=\lfloor m^2/4\rfloor$. Write $P_{m,h}$ for the surviving ballot area law weighted by $e^{-hk/s}$ and normalized, $f_h$ for the corresponding tilt of the density $f$ of half the Brownian meander area, and $g=\log f$. Take $x=k/s$ in $[4/(1.2\cdot10^6),4]$ and $h=g'(x)$. Then $x$ maximizes $f_h$, $f_h(x)\ge\sqrt{6/\pi}$ and $f_h''(x)\le-12 f_h(x)$. We have $h>-1250$. For positive $h$ put $r=h^{1/3}$, and use $r=0$ for $h\le0$. The [concentration lemma](tilt-concentration.md#width-of-the-continuous-tilted-law) gives $r<270000$. Indeed at $r\ge250$ it gives $x<(2.60/3+7/250)/r$.

## Positive tests under the random clock

Let $\epsilon=m^{-1/2}$ and $R=\max(50,-h,r,\sqrt{\log m})$. Assume $m\ge2\cdot10^{61}$. Use the [Brownian crossing-time construction](tilted-peak.md#the-random-clock-and-two-deterministic-times) and its [sharper duration bound](mode-comparison.md#smaller-clock-error). Define $V=cR\sqrt m$, $t_\pm=m\pm V$, and an area error $\eta$ by the following choices.

| Tilt range | $c$ | $\eta$ |
| --- | ---: | ---: |
| $r<50$ | 16 | $600\epsilon R^2$ |
| $r\ge50$ | 5 | $60\epsilon R^2$ |

On an event $G$ of failure probability at most $8e^{-V^2/(4m)}$, continuous survival $C_{t_+}$ implies discrete survival $A$, which implies $C_{t_-}$. On $G$, for either deterministic time,
$$ |K/s-Y_{t_\pm}|\le\eta,\qquad Y_t=(2t^{3/2})^{-1}\int_0^t(1+B_v)\,dv . $$
Indeed use the duration bound for the unweighted clock at threshold $V$ and for the clock weighted by the walk heights at threshold $V^2$. For the latter condition on the walk signs with all heights bounded by $V$. Brownian reflection handles the supremum up to $t_+$. Since $V/m<.001$, the centered duration generating function bound applies. In the doubled unscaled area, summing the rounding, clock, crossing and time-end errors gives at most $4m+3V^2+5V$. Changing the denominator adds at most $(1.51V/m)(m+V)(1+V)/(2s)$ in scaled units. Together these are below $2.34V^2/s$, which gives both entries.

Let $I_h(0)$ be the [radial normalizing integral](tilted-peak.md#relative-normalization-at-the-boundary) and $Z_*=\epsilon I_h(0)$. We use $I_h(0)\ge e^{-16R^2}$ in the first row. In the second row there is a sharper bound $I_h(0)\ge e^{-1.31r^2}$. To prove it, take a separate length $M=2b+\delta\to\infty$ at fixed $r$, with $H=\sqrt M/r$, $\beta=H^{-3}$ and $N=b/H^2\to r^2/2$. The real ground energy estimate gives $p(\beta)\ge-2.61/H^2$ eventually. The principal amplitude exceeds $.1/H$ and the relative complementary term is at most $e^{20-.5N}$, below $.01$ since $r\ge50$. The unconditioned surviving transform $F_b(\beta)$ is therefore at least $.099e^{-1.305r^2}/H$. By tilted weak convergence and the fair survival asymptotic, $\sqrt M F_b(\beta)\to I_h(0)$, giving the bound. [Energy and complementary term, (2) and (5)](linear-potential.md) · [Radial normalization](tilted-peak.md#relative-normalization-at-the-boundary)

Let $v>0$ be bounded by $b_0$, with $\log v$ Lipschitz of constant $L$. Write $B_v=\int v(y)f_h(y)\,dy$. For the cutoffs $T$ below and $L\le3T$, the comparison we need is
$$\left|\mathbb E_{m,h}v(K/s)-B_v\right|
 \le 3\eta(1+|h|+2T)\,B_v+12\epsilon^8 b_0 . \tag{1}$$
Here the first error multiplies the expectation of the test function. In particular it becomes small on functions supported mainly in a narrow interval.

To verify (1), first consider the unnormalized Brownian test at $t=t_\pm$. In the [endpoint-shift identity](tilted-peak.md#relative-normalization-at-the-boundary) its real weight is $a|W_1|^{-1}\exp(a W_1^{(1)}-a^2/2-hL_a)$, where $a=1/\sqrt t$ and $|L_a-Y^0|\le a/2\le\epsilon$. Insert $v(L_a)$ in this identity. On $\sup|W_u|\le R^2$ the log weight ratio to the limiting integral including $v(Y^0)$ is bounded in magnitude by
$$2V/m+2\epsilon R^2+2\epsilon^2+\epsilon(|h|+L)
 \le 3\epsilon R^2+\epsilon(|h|+L).$$
The discarded integrals in units of $Z_*$ cost together at most $4b_0 e^{-R^4/100+16R^2}<\epsilon^8 b_0$ by the Gaussian radial tail. For discrete survival and both deterministic Brownian times, discarding $G^c$ costs less than $\epsilon^8 b_0$ each in the same units. In the second row the real survival weights are at most one and $8e^{-6.25R^2+1.31r^2}/\epsilon<\epsilon^8$. In the first row apply Cauchy–Schwarz to the Gaussian area or the independent sum of down labels for $h<0$. The square root of the second exponential moment is at most $e^{R+R^2/4}$ by Hoeffding. For $h\ge0$ the survival weights are again at most one. The common bound $\sqrt8\,e^{-32R^2+R+R^2/4+16R^2}/\epsilon<\epsilon^8$ follows from $R^2\ge\log m$.

On $G$ the area shift costs a factor between $e^{-(|h|+L)\eta}$ and $e^{(|h|+L)\eta}$ for the positive weighted test. Sandwich its unnormalized discrete integral between the two deterministic-time integrals and use the preceding bounds. Divided by $Z_*$ it lies between $e^{-u_L}B_v-3\epsilon^8 b_0$ and $e^{u_L}B_v+3\epsilon^8 b_0$, where
$$u_L=(|h|+L)\eta+3\epsilon R^2+\epsilon(|h|+L).$$
The same inequalities with $v=1$ and $L=0$ bound the normalization. Here $u_0+u_L\le\eta(.1+2.002|h|+3.003T)<.05$ by the endpoint checks below. Dividing the two bounds and using $e^z-1\le1.03z$ for $0\le z\le.05$ yields (1).

## Localized Fourier inversion

Let $w(t)$ equal one on $[-1,1]$, decrease linearly to zero at $\pm2$ as $|t|$ increases, and vanish elsewhere. Its inverse Fourier transform is
$$K(z)=(\cos z-\cos(2z))/(\pi z^2),$$
with the continuous value at zero. Write $l(z)=1/(1+z^2)$. For $i=0,1,2,3$,
$$ |K^{(i)}(z)|\le d_i l(z),\qquad (d_0,d_1,d_2,d_3)=(2,2,5,11). $$
Indeed bound the unweighted derivative by $\|t^iw\|_1/(2\pi)$ and the derivative times $z^2$ by the total variation of the second distributional derivative of $t^i w$, divided by $2\pi$. The latter variations are at most $4,10,28,60$, including the jumps of $w'$ at $\pm1,\pm2$. The two bounds add.

Take $C_i=\max(d_i,d_{i+1})$ and apply (1) to
$$v_\pm(y)=2C_i\,l(T(x-y))\ \pm\ K^{(i)}(T(x-y)),\qquad i=0,1,2.$$
These positive tests have log Lipschitz constant at most $3T$ since $|l'|\le l$. Their average has integral under $f_h$ at most $2\pi C_i f_h(x)/T$ because $x$ is its mode. Subtract the tests and multiply by $T^{i+1}/2$. The difference between the discrete and continuous smoothed derivatives is bounded in absolute value by
$$6\pi C_i\,\eta(1+|h|+2T)T^i f_h(x)+36C_i\epsilon^8 T^{i+1}. \tag{2}$$

Use the following cutoffs from the [Fourier tail estimates](tilt-concentration.md#mode-comparison-at-smaller-sizes).

| Tilt | $T$ |
| --- | --- |
| $h<0$ | $10^9$ |
| $h\ge0,\ r<50$ | $4\cdot10^5\max(10,r)^3$ |
| $50\le r<200000$ | $10^4r^2$ |
| $200000\le r<270000$ | $60r^2$ |

The combined integral beyond $T$ with weight $1+\xi^2$ is below $.01$. The hypotheses used in those tail estimates hold here. For large positive tilts, $H=\sqrt m/r>10^{20}$ and $N=n/H^2\ge.49r^2$. For small positive tilts, the normalization bound at $v=1$ above gives $D(0)>Z_*/2$. Negative tilts use the nonnegative independent drift. Passing from the smoothed derivatives to $sP_{m,h}$, $s^2\Delta P_{m,h}$ and $s^3\delta^2P_{m,h}$ at $k$ costs the indicated tails and the lattice multiplier errors. Below $2T$ the latter integrands have bounds $\xi^2/(2s)$ and $\xi^4/(12s^2)$ for the forward and centered differences respectively. Thus the last term of (2), tails and multiplier errors together cost less than $.011$, as $T\le4\cdot10^{14}$ and $s\ge(2\cdot10^{61})^{3/2}$. The limiting comparisons are with $f_h(x),f_h'(x),f_h''(x)$.

## Signs and the remaining gap

Let $U_i=6\pi C_i\,\eta(1+|h|+2T)T^i$. Evaluating the preceding rational bounds gives
$$
\begin{array}{lll}
 n\ge10^{61}: & U_0<.74, & U_1/|h|<.024 \quad (|h|\ge1\text{ for the ratio}),\\
 n\ge10^{118}: & U_2<5. &
\end{array}$$
At fixed $h$ each $\epsilon R^a$ used here decreases with $m$ for $0\le a\le5$. For $h<0$ use $R^2/|h|\le2500$ at the size threshold when $|h|\ge1$. In the second row of the cutoff table, $T^2/h\le1.6\cdot10^{17}$ for $h\ge1$. In the last two rows write $T=Cr^2$. The bounds for $U_0,U_1/r^3,U_2$ increase with $r$ at fixed $C$. It suffices to check $(C,r)=(10^4,200000),(60,270000)$. The same endpoint argument checks the clock errors.

Since $f_h(x)>1$ and $f_h'(x)=0$, for $|h|\ge1$ the ratio $|\Delta P_{m,h}(k)|/P_{m,h}(k)$ is below $|h|/(4s)$. Removing the tilt gives strict increase in corank for $h\ge1$ and strict decrease for $h\le-1$. For $|h|<1$, [the untilted comparison](peak-rate.md#unimodality-between-large-coefficients) gives a strictly negative centered second difference. The cases occur in this order because $h=g'(k/s)$ decreases. At $n\ge10^{118}$, for every tilt, $f_h''(x)\le-12 f_h(x)$ and (2) give a strictly negative tilted centered second difference. This gives strict log-concavity on undoing the tilt.

The [flat-pair theorem](flat-pairs.md) gives growth through $10^{-5}n^{3/2}$ for $n\ge10^{61}$. This exceeds $4s/(1.2\cdot10^6)$ by more than two steps. Above $4s$ the [first-passage inequality](first-passage.md) and then the [lower-half inequality](monotonicity.md#1-lower-half-for-all-sizes) continue the decrease in corank. Near $4s$ the limiting slope is below $-1$, as in the [interval join](mode-comparison.md#joining-the-signs). This proves unimodality for both word parities. For the stronger claim, the [linear-potential estimate](linear-potential.md) and [sparse corank bound](paired-steps.md) supply strict log-concavity below the overlap at $n\ge10^{118}$.

The [finite verification](certified-window.md) reaches $n=2048$ in each family. The [two-harmonic extension](two-harmonics.md) lowers the large-size threshold to $10^{46}$. The checker uses rational upper and lower bounds on all numerical endpoints.

~~~sh
python3 -B verify_localized.py
~~~
