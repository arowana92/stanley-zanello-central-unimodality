# Concentration at a positively tilted mode

For the odd-part and even-part central staircases, unimodality holds at $n\ge10^{78}$. Strict log-concavity holds at every interior rank $j\ge D/2$ at $n\ge10^{134}$. The two improvements used here are a lower bound of order $h^{2/3}$ on the height of the positively tilted limiting density and the [finite-size estimate from flat pairs](flat-pairs.md).

## Width of the continuous tilted law

Keep the [mode comparison notation](mode-comparison.md). In particular $s=m^{3/2}$, $x=k/s$, $f$ is the density of half the Brownian meander area, and $f_h$ is its normalized tilt by $e^{-hx}$. At $4/r_*\le x\le4$ with $r_*=1.2\cdot10^6$, the choice $h=(\log f)'(x)$ gives $-1250<h<r_*^3$, $f_h'(x)=0$ and $f_h''(x)\le-12 f_h(x)$. In all cases $f_h(x)\ge\sqrt{6/\pi}$.

**Concentration lemma.** At $h=r^3$, $r\ge250$, the density $f_h$ at its mode is greater than $.089r^2$. Its mode differs from $a/(3r)$ by less than $7/r^2$, where $a$ is the ground energy of the Dirichlet operator with potential $x$.

To see this, first work with the lattice law at length $m$, holding $r$ fixed and sending $m\to\infty$. Put $\beta=h/s$, $H=\sqrt m/r$, $N=n/H^2$ and $v=-np'(\beta)/s$. Eventually $H>10^{20}$ and $.49r^2\le N\le r^2/2$. The centered exponential moments of $K/s-v$ at arguments $\pm r^2$ are ratios of $F_n(\beta(1+w))$ to $F_n(\beta)$ multiplied by $e^{-n\beta p'(\beta)w}$, for $w=\mp1/r$. These moments are each below eight. Indeed $|w|\le.004$ and the [principal amplitude bound](linear-potential.md#analytic-estimates-for-the-eigenvalue-and-amplitude) is five. After canceling the linear term in the exponent the real remainder is at most $.33N/r^2$, using $p''<.65 H^4$ on the intervening segment. The complementary term in (5) there costs at most $e^{20-.5N+4.2N/r}$ after centering. The real normalization divided by $c(\beta)e^{np(\beta)}$ exceeds $.99$. These bounds prove the moment claim.

The center $v$ tends to $a/(3r)$. Indeed $-p'(\beta)/H\to2a/3$ by the vanishing Cauchy error in (3) of the linear-potential proof, while $nH/s\to1/(2r)$. By [tilted weak convergence](tilted-peak.md#high-frequencies-under-either-sign-of-tilt) and truncation of the two nonnegative exponential functions, the limiting law has both moments about this center at most eight. Thus more than $1-16e^{-5}$ of its mass is within $5/r^2$ of $a/(3r)$. The average density there is greater than $.089r^2$. If the mode were at least $7/r^2$ from the center on either side, monotonicity toward the mode would put at least this average density on the intervening extension of length $2/r^2$. The two masses would sum to more than one. This proves both bounds. In particular when $x\ge4/r_*$ is the mode and $r\ge250$, $x<(2.60/3+7/250)/r<.9/r$, so $r<270000$.

## Mode comparison at smaller sizes

For $m\ge10^{78}$ set $\epsilon=m^{-1/2}$, $r=(\max(h,0))^{1/3}$ and
$$R=\max(50,-h,r,\sqrt{\log m}).$$
The [clock and common-survival estimates](mode-comparison.md#smaller-clock-error) give
$$|\Phi_{m,h}(\xi)-\phi_h(\xi)|\le10^7\epsilon R^2(R^3+|\xi|),\qquad |\xi|\le10^9R^3.\tag{1}$$
Here are the parameter checks for using that proof with this $R$. For $V=100R\sqrt m$, $V/(2m)<.001$, $2V/m\le\epsilon R^3$, and $R^3\eta=2\cdot10^5\epsilon R^5<5\cdot10^{-6}$, where $\eta$ bounds the area discrepancy. The weight comparisons $|e^u-1|\le2|u|$ used in normalization hold throughout this range. The coordinate tail satisfies $2(R+1)z\le z^2/12$ at $z\ge R^2$ and $4e^{-R^4/100+16R^2}<\epsilon$, since $R\ge50$ and $R^2\ge\log m$. Also $e^{-400R^2}<\epsilon^2e^{-16R^2}$ and $-R\le h\le R^3$. These are the estimates needed for the common-event and normalization errors leading to (1). At fixed $h$, each $\epsilon R^a$ with $0\le a\le5$ decreases with $m$ on this range.

Use the following values of $T$ when integrating (1).

| Tilt | $T$ |
| --- | --- |
| $h<0$ | $10^9$ |
| $0\le r<50$, $h=r^3$ | $4\cdot10^5\max(10,r)^3$ |
| $50\le r<2\cdot10^5$, $h=r^3$ | $10^4r^2$ |
| $2\cdot10^5\le r\le270000$, $h=r^3$ | $60r^2$ |

The combined integral above $T$ in absolute frequency with weight $1+\xi^2$ is below $.01$ for the lattice and limit transforms. The [previous Fourier tails](mode-comparison.md#fourier-tails-for-the-two-signs-of-tilt) apply to the first and third rows. For the third row their proof also works at $50\le r<100$ since $N\ge.49r^2>1000$, $10^4r^2\le200r^3$, and the loss in the middle frequency interval is at least $.7r^2\ge1750$. In the second row $T^{2/3}/300>18\max(10,r)^2$, which absorbs $\log 16+16\max(1,r)^2$. The same tail proof applies since $T\ge4\cdot10^8$.

For the fourth row set $y=\xi/r^3$. For the lattice transform $H=\sqrt m/r>10^{20}$ and $N\ge.49r^2$. At $|y|\le .02$ equations (4) and (5) of the [linear-potential estimate](linear-potential.md#analytic-estimates-for-the-eigenvalue-and-amplitude) and its full-disk amplitude bound give
$$|\Phi_{m,h}(\xi)|\le 8\cdot10^6 e^{-.0735 \xi^2/r^4}+2e^{20-.5N}.$$
The same estimate for the limiting transform follows by taking length to infinity at fixed $r$, with $N$ replaced by $.49r^2$. For $T<|\xi|\le.02r^3$, extract $e^{-.0735\cdot60^2/2}$ in the first term. The remaining Gaussian integral with weight $1+\xi^2$ is less than $200 r^6$ on the whole line. On $.02\le |y|\le10^4$, equation (7) there gives $2e^{20-5.88\cdot10^{-9}r^2}$. The exponent loss is already $235.2$ at $r=2\cdot10^5$, and the integration volume with weight $1+\xi^2$ is at most $2(1+10^4r_*^3)^3$. The complementary error in the first interval has the same volume bound and a larger exponential loss. At $|y|\ge10^4$ use the previous stretched-exponential tail. Together these bounds prove the asserted integral estimate.

As in the [lattice inversion](mode-comparison.md#lattice-differences-at-the-tilted-mode), errors for density, first forward difference and centered second difference in their scaled units are less than $A_j+.011$, where
$$A_j=10^7\epsilon R^2(R^3+T)T^{j+1},\qquad j=0,1,2.$$
This includes the error in the lattice multipliers since $s\ge10^{117}$ and $T<10^{15}$.

At $|h|\ge1$ the following bounds suffice for the adjacent coefficient ratio.

* For $h<0$, evaluate at $m=10^{78}$. Then $R^2/|h|\le2500$ and $R^3+T<3\cdot10^9$, giving $A_1/|h|<.075$ and $A_0<.001$. In the second row of the table with $h\ge1$, use $R\le50$, $T\le5\cdot10^{10}$ and $T^2/h\le1.6\cdot10^{17}$ to get $A_1/h<.201$ and $A_0<.001$. For $50\le r<250$ we have $R\le250$ and $T\le6.25\cdot10^8$, so $A_0,A_1<.2$ and $h\ge50^3$. In these cases $sP_{m,h}(k)>1$ and $|s^2\Delta P_{m,h}(k)|<.22|h|$.
* For $250\le r<270000$ evaluate at $m=10^{78}$ with $R=r$. At $T=Cr^2$ the two normalized bounds are
$$ A_0/r^2=10^7\epsilon C(r^5+C r^4),\qquad A_1/r^5=10^7\epsilon C^2(r^4+C r^3).$$
Both increase with $r$ at fixed $C$. Checking $(C,r)=(10^4,2\cdot10^5),(60,270000)$ gives $A_0/r^2<.034$, $A_1/r^5<.0017$. Including the tails and using the concentration lemma yields $sP_{m,h}(k)>.05r^2$ and $|s^2\Delta P_{m,h}(k)|<.002r^5$.

It follows that the tilted relative change has magnitude below $|h|/(4s)$. Removing the tilt gives strictly increasing steps in corank for $h\ge1$, strictly decreasing ones for $h\le-1$. For $|h|<1$ the untilted density exceeds one at $x$, by integrating its logarithmic slope to the mode as in the previous proof. The [untilted local bound](peak-rate.md) has $E_m<3.5\cdot10^{-11}$ at $m\ge10^{78}$. Inverting the fair envelope $8e^{-|\xi|^{2/3}/100}$ gives supremum bounds $4000,8\cdot10^6,4.5\cdot10^{10},5\cdot10^{14}$ for $f$ and its first three derivatives, using the same gamma integral as for the tails. In the [exact determinant identity](peak-rate.md#a-bound-for-the-largest-coefficients-before-global-unimodality-is-known), each scaled factor is within $e=E_m+5\cdot10^{14}/s<4\cdot10^{-11}$ of its limiting value at $x$. Thus the scaled determinant differs from $(f')^2-ff''$ by at most $e(2\|f'\|_\infty+\|f\|_\infty+\|f''\|_\infty+2e)<2$. The limiting determinant exceeds $12$. Thus strict log-concavity holds at these sites.

For $m\ge10^{134}$ the second-difference comparison applies everywhere in $4/r_*\le x\le4$. At $r<250$ including the negative tilts the bounds $R\le1250$, $T\le4\cdot10^{11}$ at the threshold give $A_2<.001$. At $r\ge250$ use
$$ A_2/r^2=10^7\epsilon C^3(r^9+C r^8)$$
at that threshold. The same two endpoints give $A_2/r^2<.54$. The total error is less than $12f_h(x)$ in both cases. Thus the tilted centered second difference is negative, and strict log-concavity follows after removing the geometric tilt.

## Consequence for both staircases

At $n\ge10^{78}$ the [flat-pair theorem](flat-pairs.md) gives strict increase through $10^{-5} n^{3/2}$, which overlaps $4s/r_*$ by more than two lattice steps for either parity. From there to $4s$ the tilt $h=(\log f)'(k/s)$ decreases, so the signs just proved allow a turn from growth to decline only once. Beyond $4s$ the [first-passage inequality](first-passage.md) and [lower-half rank inequality](monotonicity.md#1-lower-half-for-all-sizes) cover the rest, including the middle step for odd degree. This is the same [integer-interval join](mode-comparison.md#joining-the-signs) with the new size bounds. For $n\ge10^{134}$ strict log-concavity below $4s/r_*$ comes from the [linear-potential theorem](linear-potential.md) and the [sparse corank inequality](paired-steps.md), and the new centered comparison covers all intervening ranks up to the first-passage interval.

The [rational verifier](verify_flat_pairs.py) checks the odd-height two-step phases directly, the constants in the uniform saddle estimate, the cutoff errors and the mode bounds. Run it from the checkout with Python 3.

~~~sh
python3 -B verify_flat_pairs.py
~~~
