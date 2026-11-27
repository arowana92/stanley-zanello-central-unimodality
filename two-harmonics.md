# Two Fourier harmonics for the small-area saddle

For both central staircases the rank sequence is unimodal for **every $n\ge10^{46}$**. At **every $n\ge10^{88}$** it is strictly log-concave at every interior rank in the upper half. The argument improves two parts of the [localized mode proof](localized-mode.md). The first two Fourier harmonics of an unrestricted block control how much cancellation survives imposing a wall and a real tilt. The resulting small-area estimate reaches the peak comparison when the two estimates are expressed using the same Dirichlet ground energy.

Write $m=2n+\delta$, $s=m^{3/2}$, $D=\lfloor m^2/4\rfloor$ and $k=D-j$. Use the [ballot transfer operator](effective-small-area.md#real-transfer-operator) $K_z=(T_z/2)^2$ on even heights, $\beta=H^{-3}$, $\lambda=\|K_\beta\|$, $p=\log\lambda$, and $F_n(z)=2^{-m}\sum_k a_{D-k}e^{-zk}$. The principal amplitude is $c(\beta)=e_0\Pi_\beta W_\delta(\beta)$. Set $N=n/H^2$ and $y=\theta/\beta$.

## A bound for arbitrary retained paths

Consider a block of $2l$ unrestricted fair steps from one starting height. Suppose its endpoint rows have sums of Fourier moduli at most $\rho_1,\rho_2$ at frequencies $\theta,2\theta$, respectively. Give each path an arbitrary real weight in $[0,1]$. The sum of the resulting endpoint moduli at $\theta$ is at most
$$ \frac{\rho_1}{2}+\frac12\sqrt{\frac{1+\rho_2}{2}}. \tag{1} $$
For each endpoint choose a phase making its retained integral real and nonnegative. Subtract that phase from the original path phase to obtain $v$. The real retained contribution is bounded by $(\cos v)_+=(\cos v+|\cos v|)/2$. Under the unrestricted probability, $\mathbb E\cos v\le\rho_1$ and $\mathbb E\cos(2v)\le\rho_2$, because the endpoint phase is constant within each endpoint. Now use $\mathbb E|\cos v|\le\sqrt{\mathbb E\cos^2 v}$. A surviving path has real weight $e^{-\beta\,\mathrm{area}}\le1$, and a killed path has weight zero. Thus (1) applies to the complex transfer matrix. Its entrywise modulus is symmetric, so the uniform row bound also bounds its operator norm.

For $H\ge2\cdot10^{12}$ take $l=\lfloor H^2/4\rfloor$. Pair the labels in its first half with the labels $l$ positions later. The [unrestricted phase estimate](linear-potential.md#a-shorter-block-for-intermediate-frequencies) gives $\rho_d\le e^{-d^2l^3\theta^2/16}$ for $d=1,2$ provided $2l|\theta|\le\pi$. This holds through $|y|\le10^4$. The real [energy estimate (2)](linear-potential.md#approximation-of-the-real-ground-energy) gives $-pH^2<2.61$. For $45\le |y|\le10^4$ divide (1) by $\lambda^l$, using $l/H^2\ge.2499$. The relative block norm is at most
$$e^{2.61/4}\left(e^{-z}+\sqrt{(1+e^{-4z})/2}\right)/2<.815,\qquad z=.2499^3\,45^2/16.$$
For $0<|y|\le45$ apply the [integer-multiple inequality](harmonic-small-area.md#comparing-two-frequencies) at multiplier $\lceil45/|y|\rceil$. This gives relative block norm at most $1-.185y^2/(45+|y|)^2$. At $N\ge1000$, peeling the two boundary blocks of $\lceil H^2\rceil$ pairs leaves at least $3.99N$ of these shorter blocks. Using the [boundary norms](effective-small-area.md#complex-tilts-near-the-saddle) and $c(\beta)>.1/H$ gives, for $\Psi=F_n(\beta+i\theta)/(c(\beta)\lambda^n)$,
$$|\Psi|\le e^{20}\begin{cases}
 e^{-.000345Ny^2},& |y|\le1,\\
 e^{-.000345N},&1\le |y|\le10^4 .
\end{cases} \tag{2}$$
We also have $e^{20-.00009Ny^2}$ through $|y|\le45$ and $e^{20-.73N}$ on $45\le|y|\le10^4$. The [full-block bound](harmonic-small-area.md#inversion-for-hge20) beyond $10^4$ gives $e^{20-N|y|^{2/3}/80}$. Its proof uses $2n-4\lceil H^2\rceil\ge1.99n$, the paired-label row estimate and $-pH^2<2.61$. All lattice bounds are restricted to $|\theta|\le\pi$.

## A boundary identity for the real eigenvector

Let $S$ be the unilateral shift on the height basis and $q=e^{-\beta}$. The edge weights $q^{j/2}$ give the exact operator identity
$$ S^*T_\beta-\sqrt q\,T_\beta S^*=e_0 e_0^{\mathsf T}. $$
In row $j\ge1$ the two nearest-neighbor terms cancel separately. Row zero leaves the missing boundary term. For real unit eigenvectors $u,v$ with eigenvalues $\rho,\nu$ this yields $(\rho-\sqrt q\,\nu)\langle v,S^*u\rangle=v_0u_0$. In particular for the positive ground vector $u$,
$$2(1-\sqrt q)\lambda\ \le\ u_0^2
 =(1-\sqrt q)\rho\sum_{j\ge0}u_j u_{j+1}\ <\ \beta .$$
The lower bound uses $\rho=2\sum_j q^{j/2}u_j u_{j+1}$ and the upper uses Cauchy–Schwarz. This determines $u_0^2/\beta\to1$ at small $\beta$. We use the lower bound below to control the bounded-height saddle.

## Analytic control on a wider disk

Here $H\ge10^{12}$. The gap between $\lambda$ and its next eigenvalue exceeds $1.48/H^2$. In the [nodal cut](effective-small-area.md#real-transfer-operator), a cut after $l\le1.5H$ vertices bounds the second eigenvalue of $K_\beta$ by $\cos^2(\pi/(l+1))\le1-4.30/H^2$. We have $\lambda\ge1-2.60/H^2$ by the [sine trial](flat-pairs.md#estimates-down-to-height-scale-four). A cut farther out bounds the second eigenvalue by $\lambda e^{-1.5/H^2}$.

On the spectral circle of radius $.74/H^2$ around $\lambda$, the [form resolvent estimate](harmonic-small-area.md#real-and-complex-estimates-near-the-saddle) uses $M\le2+2.60/.74<5.52$. Its weight bound $\| (I-K_\beta)^{-1/2}(K_{\beta(1+w)}-K_\beta)(I-K_\beta)^{-1/2}\|\le |w|$ holds up to $|w|\le1/2$ by the same pathwise exponential inequality. Hence the simple eigenvalue and projection extend to $|w|\le.16$, with $H^2|p(\beta(1+w))-p(\beta)|<.75$ and $\|\Pi_z-\Pi_\beta\|\le |w|M/(1-|w|M)$.

Let $a$ be the ground energy of $-\partial_x^2+x$ on the Dirichlet half-line, so $1.65\le a<2.60$. Put $E(w)=H^2p(\beta(1+w))+a(1+w)^{2/3}$. The real energy estimate gives $|E|\le12/H$ on the real diameter. On the full disk $|E|<2$, by the preceding spectral circle and $|(1+w)^{2/3}-1|\le(2/3)(.84)^{-1/3}|w|$. The [semidisk harmonic-measure estimate](linear-potential.md#analytic-estimates-for-the-eigenvalue-and-amplitude) gives bounds $2(12/H)^{.68}<7.6\cdot10^{-8}$ and $2(12/H)^{.40}<8.6\cdot10^{-5}$ on radii $.04$ and $.08$, respectively. Cauchy's inequalities on the smaller disk imply
$$
 |-p'(\beta)/H-2a/3|<.001,\quad .35<p''(\beta)/H^4<.60,\quad
 |p'''(\beta(1+w))|/H^7<1\quad(|w|\le.01). \tag{3}
$$
For the third bound the error is at most $6(7.6\cdot10^{-8})/.03^3$. For $|y|\le.08$,
$$H^2\Re(p(\beta(1+iy))-p(\beta))\le-.12y^2. \tag{4}$$
Through $.01$ use Taylor's formula and (3). From $.01$ to $.04$ use $\Re(1+iy)^{2/3}\ge1+.109y^2$, by Taylor's formula through the imaginary cubic term with fourth derivative at most $56/81$, and error at most $7.6\cdot10^{-8}+12/H$. From $.04$ to $.08$ use the outer error $8.6\cdot10^{-5}+12/H$. Both losses are less than $(1.65\cdot.109-.12)y^2$.

For $|w|\le.08$ the norm on the complementary invariant space is at most $\lambda e^{-.16/H^2}$. Indeed the [squared norm comparison](harmonic-small-area.md#real-and-complex-estimates-near-the-saddle) bounds it before restriction by the quadratic form of $K_\beta^2+.24(I-K_\beta)$. On the lower spectrum the polynomial is at most $\lambda^2-1.97/H^2$ by convexity and the two endpoint values. At $\lambda$ it is at most $\lambda^2+.624/H^2$. A unit vector in $\ker\Pi_z$ has overlap at most $.08M/(1-.08M)$ with the real top vector. The weighted average of the two bounds is below $\lambda^2-.32/H^2$. Peeling the two boundary blocks therefore gives relative complementary error at most $e^{20-.16b/H^2}$ for $F_b$ at any $b\ge100H^2$, in units $c(\beta)\lambda^b$. Peeling the blocks around $\Pi_z$ also gives $|c(z)/c(\beta)|<10^6$ there, using $\|\Pi_z\|<2$, boundary norm product $10/H$, and $-H^2\log|\lambda_z|<2.61+.75$.

## Signed inversion after twenty million blocks on the height scale

Suppose $H\ge2\cdot10^{12}$, $N\ge2\cdot10^7$ and $k=-np'(\beta)$ is an integer. Set $\sigma^2=np''(\beta)$, $d=\beta\sigma$ and $x=\sigma\theta=dy$. Then $\sqrt{.35N}<d<\sqrt{.60N}$. We bound the principal amplitude using a shorter walk with $b=\lceil400H^2\rceil$ pairs. Use the same terminal parity as in $F_n$ and set
$$ S(w)=F_b(\beta(1+w))e^{-b\beta p'(\beta)w}/(c(\beta)\lambda^b). $$
The relative remainder gives $|S(0)-1|<.001$. The real values $S(\pm.08)$ are below $e^{11}$. To see this, at $\beta'=\beta(1\pm.08)$ peel the two boundary blocks for $H'=(\beta')^{-1/3}$. The prefactor relative to $c(\beta)$ is below $103e^{5.23}$, using $-p(\beta')(H')^2<2.61$. Along the intervening real segment, (3) at the shifted scale gives $p''<.68H^4$ since $H'>10^{12}$. After centering, the remaining exponent is at most $.34\cdot401\cdot.08^2$.

The positive transform $S(w)/S(0)$ is the Laplace transform of $Z=\beta(K+bp'(\beta))$ for the shorter tilted walk. Thus $\Pr(|Z|>t)\le\min(1,2e^{11}e^{-.08t}/S(0))$. Integration gives $S(0)\mathbb E|Z|<160$ and consequently $|S(iy)-1|<.001+160|y|$. At imaginary $w$ the centering leaves the complementary error unchanged. For $|y|\le.01$, the centered principal exponent for the shorter walk has modulus at most $401(.30y^2+|y|^3/6)$ by (3). Since $|S(iy)|\le S(0)$, isolating the principal term gives $|c(\beta(1+iy))/c(\beta)|<1.02$ on this interval. When $|x|\le6$, it also gives $|c(\beta(1+iy))/c(\beta)-1|<.37$.

For the full walk the centered principal exponent differs from $-x^2/2$ by at most $N|y|^3/6$ through $|y|\le.01$. This is less than $.039$ on $|x|\le6$. Thus the real centered principal transform exceeds $.57e^{-x^2/2}$ there. On $|x|>6$ through $|y|=.01$ its modulus is below $1.02e^{-.49x^2}$. On $.01\le|y|\le.08$, (4) gives $10^6 e^{-.2x^2}$ and $|x|\ge.01\sqrt{.35N}>26$. Each of these two outer principal integrals with weight $1+x^2$ costs less than $.01$.

For $.08\le |y|\le1$ put $C=.000345 N$, $v=.08$. The corresponding weighted integral in $x$ is, by (2), at most
$$ 2e^{20-Cv^2}\left[\frac{d}{2Cv}+d^3\left(\frac{v}{2C}+\frac{1}{4C^2v}\right)\right]<.001 .$$
This follows by integration by parts and the Gaussian tail bound. Substitute $d\le\sqrt{.60N}$ and evaluate at $N=2\cdot10^7$ since each polynomial times the exponential decreases. The remaining frequencies through $10^4$ cost at most $2e^{20}(1+10^4 d)^3 e^{-.000345N}$. The low-frequency complementary integral has the same bound with loss $.16N$. Beyond $10^4$ extract $e^{-N(10^4)^{2/3}/160}$ from the stretched exponential and integrate the remainder as in the [earlier saddle estimate](linear-potential.md#signs-at-the-saddle). These three costs together are below $.01$.

The signed integral of the centered transform, unweighted or with $4\sigma^2\sin^2(x/(2\sigma))$, exceeds one. On $[-6,6]$ the latter multiplier exceeds $.99x^2$ except at zero where both vanish, and both central Gaussian integrals exceed $2.4$. The integrated $|x\Psi|$ is less than ten by the same tail bounds and the central upper bound $1.37 e^{.039}e^{-x^2/2}$. Inversion gives strict negative centered second difference at the tilted saddle and a relative first difference of magnitude below $10/\sigma<\beta/4$. Undoing the geometric tilt proves **strict growth in corank and strict log-concavity** at this $k$.

## Matching the two area scales

Define $x_0=(a/3+.002)/6500$. For $n\ge10^{46}$ the small-area estimates give strict growth through $x_0s+1$ (at integer steps). Below $9n$ use the [linear tail bound](finite-tail.md). At $k\ge9n$ the saddle has $H>4$. When $H<2\cdot10^{12}$, $N>10^{21}$ and the [uniform flat-pair inversion](flat-pairs.md#inversion-with-a-uniform-number-of-blocks) applies. Otherwise (3) gives $k/n>(2a/3-.001)H$. For $k\le x_0 s+2$ this yields
$$ N\ge \frac{6500^2}{(2.001)^3}
       \left(\frac{2a/3-.001}{a/3+.003}\right)^2 >2\cdot10^7.$$
Here $m/n\le2.001$ and $2/s<.001/6500$. The ratio increases with $a$, so its value at $1.65$ suffices. This uses the same $a$ as the [limiting tilted-mode bound](tilt-concentration.md#width-of-the-continuous-tilted-law). That bound puts every mode of tilt $h=r^3$, $r\ge250$, below $(a/3+7/r)/r$. Consequently for $x_0\le x=k/s\le4$, the choice $h=(\log f)'(x)$ satisfies $-1250<h$ and $r<6500$ (take $r=0$ when $h\le0$).

For these tilts use the [localized kernel estimate (2)](localized-mode.md#localized-fourier-inversion) with the following cutoffs.

| Tilt | $T$ |
| --- | --- |
| $h<0$ | $10^6$ |
| $0\le r\le4$, $h\ge0$ | $2\cdot10^6$ |
| $4<r<50$ | $10^4\max(12,r)^3$ |
| $50\le r<6500$ | $2000 r^2$ |

Here is the Fourier-tail check at the new cutoffs. In each case the combined integral beyond $T$ of $(1+\xi^2)$ times the moduli of the two characteristic functions is below $.01$.

* At negative tilt the independent down probabilities before imposing the wall are in $[.499,.501]$, since $|h|/\sqrt m<.001$. The prefix/full survival ratio at $\lfloor m/2\rfloor$ is at most $2(|h|+2)$ by the [homogeneous survival estimate](mode-comparison.md#fourier-tails-for-the-two-signs-of-tilt). For $\theta=|\xi|/s\le1/8$ pair labels in the suffix at spacing $l=\lceil4\theta^{-2/3}\rceil$. The [mixed-pair bound](rising-window.md#fourier-bound-for-a-hit-after-the-cut) gives unrestricted row bound $e^{-.24l\sin^2(l\theta/2)}$, since $2AB/(A+B)>.24$ for the two mixed probabilities. As $\sin^2(l\theta/2)\ge.65(l\theta/2)^2$, the retained bound $(1+\rho)/2$ is less than $e^{-.61}$. At least $|\xi|^{2/3}/17-1$ blocks fit, giving $4(|h|+2)e^{-.035|\xi|^{2/3}}$. Beyond $s/8$ the earlier envelope with rate $1/4000$ suffices. The limit inherits the sharper envelope at every real frequency. Already $.035T^{2/3}=350$.
* At small positive tilt the [fair oscillatory suffix](tilted-peak.md#strict-increase-in-corank-under-a-larger-positive-tilt) gives $16e^{-|\xi|^{2/3}/150}/I_h(0)$ for both laws, using the clock normalization below. For $r\le4$, Jensen gives $I_h(0)\ge .7e^{-h/2}$ by the [first moment](finite-reduction.md#exact-area-moments). For $4<r<50$ use $I_h(0)\ge e^{-1.31\max(15,r)^2}$. In fact the [ground-energy normalization proof](localized-mode.md#positive-tests-under-the-random-clock) applies for $r\ge15$ by taking the auxiliary word length to infinity, since $N\to r^2/2\ge112.5$ in its real estimate (5). For smaller $r$ use monotonicity of this integral. With $z=T^{2/3}/150$, in the first range $z>105$ and $h/2\le32$. In the second, $z>3.09\max(12,r)^2$ and $z-1.31\max(15,r)^2>149$. Integrate the tail with the incomplete-gamma bound in the [fair peak estimate](peak-rate.md#unimodality-between-large-coefficients).
* For $r\ge50$ we have $H=\sqrt m/r>2\cdot10^{12}$ and $N\ge.49r^2$. The real normalization from the complementary estimate is at least $.99c(\beta)\lambda^n$. At $|y|=|\xi|/r^3\le45$, (2) and its extension give $2e^{20-.000044\xi^2/r^4}$. Extract $e^{-132}$ at $T$ and integrate the remaining Gaussian against $1+\xi^2$ over the real line, costing at most $10^8 r^6$ before the prefactors. In $45\le|y|\le10^4$ use $2e^{20-.73N}$ and volume at most $2(1+10^4r^3)^3$. Beyond this interval use the stretched exponential in (2), which after scaling is at most $2e^{20-|\xi|^{2/3}/170}$. The limiting bounds follow by taking word length to infinity at fixed $r$.

In the localized comparison write $\epsilon=m^{-1/2}$, $R=\max(50,-h,r,\sqrt{\log m})$ and $\eta=(600\text{ if }r<50,\ 60\text{ otherwise})\,\epsilon R^2$. The positive-test argument uses $u_0+u_L\le\eta(.1+2.002|h|+3.003T)<.05$, which holds already at $m\ge2\cdot10^{46}$ for the table above. Together with $V/m<.001$ this supplies the clock hypotheses there, including the $v=1$ normalization before using Fourier tails. The lattice multiplier errors for $|\xi|\le2T$ and the discarded-test term together cost less than $.001$, since $T\le2000\cdot6500^2$ and $s\ge(2\cdot10^{46})^{3/2}$.

Put $U_i=6\pi C_i\eta(1+|h|+2T)T^i$ with $(C_0,C_1,C_2)=(2,5,11)$. For $n\ge10^{46}$ the bounds are $U_0<.31$ and $U_1/|h|<.24$ when $|h|\ge1$. For $n\ge10^{88}$ we have $U_2<11.8$ for every tilt. To check the first-derivative bounds one can use $R^2/|h|\le2500$ at the minimal size for negative $h$ with $|h|\ge1$. In the two small positive ranges, $T^2/h\le1.25\cdot10^{13}$ for $h\ge1$. In the last row the three expressions, with $U_1$ divided by $r^3$, increase with $r$ at the size threshold. At fixed tilt $\epsilon R^a$ decreases with $m$ for the powers $a$ used here.

The localized inversion error at order $i$ is at most $U_i f_h(x)+.011$ at the mode of $f_h$. Since $f_h(x)>1$ and $f_h'(x)=0$, at $|h|\ge1$ these bounds put the relative forward difference of $P_{m,h}$ below $|h|/(2s)$ in magnitude. Undoing the tilt gives strict increase in corank for $h\ge1$ and strict decrease for $h\le-1$, using $|h|/s<1$. For $|h|<1$ the [untilted centered difference](peak-rate.md#unimodality-between-large-coefficients) is negative. The slopes $h=(\log f)'(k/s)$ decrease with $k$, so these steps can turn from increase to decrease only once. Near $4s$ the slope is already below $-1$. The [first-passage inequality](first-passage.md) continues the decrease to the midpoint, followed by the [lower-half rank inequality](monotonicity.md#1-lower-half-for-all-sizes). This proves unimodality at $n\ge10^{46}$.

At $n\ge10^{88}$ the order-two error is less than $12 f_h(x)$, so $f_h''(x)\le-12 f_h(x)$ gives a negative tilted centered second difference. This yields strict log-concavity on undoing the tilt. The saddle proofs already give it for $H\ge4$ below $x_0s+2$, and for $1\le k\le n/3$ it follows from the [sparse corank bound](paired-steps.md). To fill the remaining bounded-height saddles, use $1/64\le\beta\le8$, the upper endpoint following from $k>n/3$ and $-p'(8)<1/105$. In the [bounded-height inversion](harmonic-small-area.md#bounded-height-scales), $p''\ge 2e^{-\beta}u_0^4>2\cdot10^{-6}$ on this interval. The boundary identity and $\lambda\ge1/4$ give $u_0^2\ge\beta/8$ up to $\beta=1$ and $u_0^2>.19$ thereafter. With this variance, on $|\sigma\theta|\le16$ the cubic error $3\cdot10^{27}n|\theta|^3/6$ and amplitude error $4\cdot10^{17}|\theta|$ are both below $.001$ at $n\ge10^{88}$. This central interval lies inside $|\theta|\le10^{-39}$. For higher frequencies $|\theta|\ge10^{-39}$ use the [odd-height flat-pair norm](flat-pairs.md#a-norm-bound-on-odd-heights), which gives loss at least $10^{-5}n\theta^2$ in the exponent, since $q=e^{-\beta}\ge e^{-8}$ and $1-\cos\theta\ge2\theta^2/\pi^2$. This absorbs the full volume $10^{10}(1+\sigma)^3$ for $\sigma\le10^8\sqrt n$. The low-frequency complementary and Gaussian-tail bounds from the bounded-height proof now give its same positive sine-weighted integral. This completes upper-half strict log-concavity for both parities.

The [verifier](verify_harmonics.py) checks the two-harmonic estimate on small endpoint rows by direct enumeration, and checks the numerical inequalities in the analytic argument with rational bounds. The [finite coefficient verification](certified-window.md) reaches $n=2048$, leaving **$2049\le n<10^{46}$** unresolved.

~~~sh
python3 -B verify_harmonics.py
~~~
