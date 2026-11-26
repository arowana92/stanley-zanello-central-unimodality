# A finite-size bound on the increasing side

For either central family put $m=2n$ or $2n+1$, $D=\lfloor m^2/4\rfloor$ and $s=m^{3/2}$. The following implication has no unspecified size threshold.

**Theorem.** If $D/2\le j\le D-200s$, then
$$a_{j+1}\ \ge\ a_j\exp\!\left(\frac{5(D-j)}{m^3}\right)>a_j,
\qquad a_j^2>a_{j-1}a_{j+1}.$$

This proof gives 200 and first applies at $m=2{,}560{,}000$. The [first-passage proof](first-passage.md) gives the same inequalities from $D/2$ through $D-4s$, starting at $m=1024$. The paired-label and Bernoulli bounds below enter that proof and the tilted peak estimates.

## Tilt and survival

Use independent down indicators $X_r$ of probabilities $p_r=(1+e^{\alpha r/m})^{-1}$, read in descending label order. Put $S=\sum_{r=1}^m rX_r$. Write $H_t$ for the height and $E_t$ for survival through time $t$. Choose $\alpha$ so that $\mathbb ES=j$.

The hypotheses give $\sqrt m\ge1600$, since $200s\le D/2\le m^2/8$. The mean decreases strictly with $\alpha$ and at zero it is $m(m+1)/4>D$. At $\alpha=2$, concavity gives $\tanh(r/m)\ge (r/m)\tanh(1)>.76r/m$. Hence the mean is at most $m(m+1)/4-(.38/m)\sum r^2 < (m^2-1)/8\le D/2$ in this range of $m$. Thus $0<\alpha<2$. The absolute derivative of the mean is at most $\sum r^2/(4m)\le m^2/11$. In particular
$$\alpha\ge 11(D-j)/m^2,\qquad \gamma:=\alpha\sqrt m\ge2200.$$

Put $L=\lceil m/1024\rceil$, $h=\lceil m/2\rceil$, $M=m-L$, and $d=\alpha/5$. The first $h$ up-step drifts are at least $\tanh(\alpha/4)\ge d$. Coupling to a homogeneous walk of drift $d$ gives $\Pr(E_L)\ge 2d/(1+d)\ge d$ by the ruin formula.

We need a small *conditional* error from dropping the wall after $L$. Given $E_L$, crossing between $L$ and $h$ has probability at most $\mathbb E(e^{-dH_L}\mid E_L)$ by the same ruin formula. The event $E_L$ is increasing in the up indicators and $e^{-dH_L}$ is decreasing. Product-measure association and Hoeffding's exponential bound therefore give
$$\mathbb E(e^{-dH_L}\mid E_L)\le\mathbb E e^{-dH_L}\le e^{-d^2L/2}.$$
Given $E_L$, the probability of $H_h<dh/2$ is at most $e^{-d^2h/8}$ by association and Hoeffding again. From height at least $dh/2$, compare to a fair walk for the final $m-h$ steps. The exponential maximal bound gives crossing probability at most $\exp(-(dh/2)^2/(2(m-h)))\le e^{-d^2h/8}$. This bound follows by applying the maximal inequality to the exponential of the negative fair walk and optimizing the exponent. Consequently
$$\epsilon:=\Pr(E_m^c\mid E_L)\le e^{-\gamma^2/51200}+2e^{-\gamma^2/400}<10^{-40}.$$

## A local Gaussian estimate with the wall imposed through $L$

Let $V=\sum_{r\le M}rX_r$ be the independent suffix and $U=S-V$. Write $\sigma^2=\operatorname{Var}V$ and $\mu=\mathbb EV$. Since $p_r(1-p_r)\ge e^2/(1+e^2)^2>.1$ and $L\le m/1023$, we have
$$.18s\le\sigma\le s,\qquad m/\sigma\le 1/288.$$

With conditional probability at least $.95$ under $E_L$,
$$|U-\mathbb E U|\le 3m\sqrt L < .53\sigma. \tag{1}$$
Indeed, multiply the product law by $e^{tU}$ and normalize for $t=\pm 2/(m\sqrt L)$. This changes each log down/up odds by at most $2/\sqrt L$, so the changed prefix drifts are at most $\alpha/2+1/\sqrt L$ (use the Lipschitz bound for $\tanh$). A homogeneous walk with nonnegative drift $d'$ survives $L$ steps with probability at most $2d'+2/\sqrt L+2/L$. To see this, the fraction of paths to $x\ge0$ that survive is $(x+1)/((L+x)/2+1)$ by reflection, and $\mathbb E|H_L-\mathbb E H_L|\le\sqrt L$. Comparing with the largest allowed drift, capped at one, gives $\Pr_t(E_L)\le\alpha+6/\sqrt L$. As $\alpha\sqrt L\ge2200/32$, its ratio to $\Pr(E_L)$ is less than $5.5$. Hoeffding bounds $\mathbb E e^{t(U-\mathbb E U)}$ by $e^{1/2}$. Multiplying by the survival ratio and applying Markov's inequality for both signs proves (1), since $11e^{1/2-6}<.05$.

Write $g(v)=\Pr(V=v)$, $\Delta g(v)=g(v+1)-g(v)$ and $\delta^2 g(v)=g(v-1)-2g(v)+g(v+1)$. With $\varphi$ the standard normal density and $x=(v-\mu)/\sigma$, we claim uniformly in $v$ that
$$|\sigma g(v)-\varphi(x)|<.01,\quad
 \sigma^2|\Delta g(v)|<.8,\quad
 |\sigma^3\delta^2g(v)-\varphi''(x)|<.01. \tag{2}$$

Here are details for the numerical errors. For $|\theta|\le1/m$ each centered Bernoulli factor, of variance $w=r^2p_r(1-p_r)$, has modulus at most $e^{-.45 w\theta^2}$ by the exact squared modulus $1-4p_r(1-p_r)\sin^2(r\theta/2)$. The modulus of its difference from $e^{-w\theta^2/2}$ is at most
$$m w|\theta|^3/6+w^2\theta^4/8\le .2m w|\theta|^3.$$
This uses the third absolute centered moment bound $mw$ and Taylor's theorem. Telescope the product against the Gaussian factors. The omitted factor costs at most $e^{.45/4}$ in the modulus estimate, since $w\theta^2\le1/4$. For $t=\sigma\theta$ the resulting difference of centered characteristic functions is bounded by $.23(m/\sigma)|t|^3e^{-.45t^2}$.

For $1/m\le|\theta|\le2\pi/M$, the first $\lfloor M/2\rfloor$ factors have $\sin^2(r\theta/2)\ge r^2\theta^2/\pi^2$. For $2\pi/M\le|\theta|\le\pi$, summing cosines gives $\sum_{r\le M}\sin^2(r\theta/2)\ge M/2-\pi/(2|\theta|)\ge M/4$. The unrestricted suffix characteristic function is bounded by $e^{-m/2000}$ on both intervals by $p_r(1-p_r)>.1$.

In Fourier inversion, the scaled multiplier for $\delta^2$ is $-4\sigma^2\sin^2(t/(2\sigma))$. Its modulus is at most $t^2$ and its difference from $-t^2$ is at most $t^4/(12\sigma^2)$. For the zeroth and second differences the telescoping errors are bounded by $.23(m/\sigma)/\pi$ times the integrals of $t^3e^{-.45t^2}$ and $t^5e^{-.45t^2}$ on $[0,\infty)$, respectively. The integrals are $1/(2\cdot.45^2)$ and $1/.45^3$. Each error is less than $.003$. The multiplier error contributes at most $\int_0^\infty t^4 e^{-t^2/2}\,dt/(12\pi\sigma^2)$. The scaled outer Fourier integrals contribute at most $4\sigma^3 e^{-m/2000}$, and the Gaussian tail starts at $\sigma/m\ge288$. Each is below $.001$ since $m\ge2{,}560{,}000$ and $\sigma\le m^{3/2}$. For the first difference simply integrate $t e^{-.45t^2}/\pi$ on $[0,\infty)$ and include the outer Fourier bound. This proves (2).

## Restoring the wall without losing a lattice difference

Write $f$ and $f_L$ for the laws of $S$ conditional on $E_m$ and $E_L$, and $\Phi,\Phi_L$ for their characteristic functions. For $r=0,1,2$ use the three operators $I,\Delta,\delta^2$, denoted here by $D_r$. We prove
$$\sigma^{r+1}\sup_v|D_r(f-f_L)(v)|<.001. \tag{3}$$

First $|\Phi-\Phi_L|\le2\epsilon$ because the second law is a mixture with weight $1-\epsilon$ on the first. For the rest of the frequency interval we use the [paired-label argument](peak-window.md#a-bound-on-the-characteristic-function), with constants as follows. Among the labels after time $h$, both up and down probabilities are at least $1/9$ and up probabilities are at least $1/2$. Pair the first half of a block of $2l$ labels with its second half. In each pair the two mixed configurations have probabilities $u,v\ge1/18$. They give the same endpoint with relative phase $l\theta$. Thus the unrestricted absolute row-sum bound for the block is at most $\exp(-l\sin^2(l\theta/2)/18)$. Indeed $u+v-|u+ve^{il\theta}|\ge 2uv\sin^2(l\theta/2)/(u+v)$, and the independent pairs multiply after conditioning on the counts in each pair.

Take $l=\lceil2|\theta|^{-2/3}\rceil$ for $0<|\theta|\le1$, and $l=1$ otherwise. In the first range $l|\theta|\le3$ and $l\sin^2(l\theta/2)\ge l^3\theta^2/\pi^2\ge8/\pi^2$. In the second range $\sin^2(\theta/2)>.22$. For a killed row of survival probability $p$ the absolute row sum is at most both $p$ and $1-p+\exp(-.22/18)$ by subtracting the discarded paths from the unrestricted row. Hence each full block, killed or unrestricted, costs at most $(1+\exp(-.22/18))/2<e^{-1/200}$.

The prefix to $h$ has absolute row sum at most $\Pr(E_h)$ when killed and at most $\Pr(E_L)$ when killing stops at $L$. After normalization these cost at most $1/(1-\epsilon)$ and one. Since $m-h\ge m/3$ and $l\le3|\theta|^{-2/3}$, at least $m|\theta|^{2/3}/18-1$ full blocks fit. Thus both moduli are bounded by $3\exp(-m|\theta|^{2/3}/4000)$.

In the inversion for (3) the multiplier has modulus at most $|\theta|^r$. Split at $T/s$, $T=10^9$, or at $\pi$ if smaller. Since $\sigma\le s$, the normalized error is at most
$$\frac{2\epsilon T^{r+1}}{\pi(r+1)}+
 \frac6\pi\int_T^\infty x^r e^{-x^{2/3}/4000}\,dx < .001.$$
For the tail it suffices to take $r=2$. Substitution $u=x^{2/3}/4000$ bounds the integral by $\tfrac32\,4000^{9/2}\int_{250}^\infty u^4e^{-u}\,du$. Four integrations by parts give the claimed bound. This frequency estimate is what allows the fixed conditional error $\epsilon$ to control derivatives on a lattice of arbitrarily small rescaled spacing.

## Sign and curvature

Under $E_L$ the suffix is independent of the prefix. At $v=j-U$, its standardized argument is $(\mathbb EU-U)/\sigma$, within $.53$ of zero with probability at least $.95$ by (1). Since $\varphi(.53)>.34$, equations (2) and (3) give $f(j)>.30/\sigma$ and $|\Delta f(j)|<1/\sigma^2$. Also $\varphi''(x)=(x^2-1)\varphi(x)<-.24$ on $|x|\le.53$, while $|\varphi''|\le.4$ globally. Averaging (2) over the prefix and then applying (3) gives $\sigma^3\delta^2 f(j)<-.19$. Consequently $f(j)$ strictly exceeds the arithmetic mean of its two neighbors and $f(j)^2>f(j-1)f(j+1)$.

Conditional on survival, $f(j)$ is proportional to $a_j e^{-\alpha j/m}$. A geometric tilt preserves the log-concavity determinant's sign. The growth estimate follows from $f(j+1)/f(j)\ge1-4/\sigma$, $\log(1-4/\sigma)\ge-8/\sigma$ and $\alpha\sigma/m\ge.18\gamma\ge396$. The log coefficient ratio is at least $\alpha/(2m)\ge5(D-j)/m^3$, as asserted.
