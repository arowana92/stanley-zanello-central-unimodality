# Paired ballot steps and finite-size curvature

Let $b_{n,k}=a_{D-k}$ be the number of partitions missing $k$ cells from either central staircase with $n$ rows. For **every** $n$ and $1\le k\le n/3$,
$$b_{n,k}^2-b_{n,k-1}b_{n,k+1}>\frac{b_{n,k}^2}{40k}. \tag{1}$$
The proof uses exact rational polynomial bounds. The same inequality holds at $1\le k\le640$ for every $n\ge\max(9,\lceil k/2\rceil)$ by a separate Newton certificate. These results concern the high-rank tail. At large sizes the global peaks have corank of order $n^{3/2}$.

## An exact stabilization identity

Use $q$ to mark corank and take the forced first up-step of a surviving ballot word. Group subsequent steps into pairs. Let $u_{\ell,i}$ be the polynomial after $\ell$ pairs at height $2i+1$, starting with $u_{0,0}=1$. Below, $v_{\ell,i}=u_{\ell,i}/u_{\ell,0}$, so $v_{\ell,0}=1$ and out-of-range entries are zero. The two flat pairs from $2i+1$ contribute $q^{2i}(1+q)$, the ascending pair contributes $q^{2i+2}$, and the descending pair contributes $q^{2i-1}$ when $i\ge1$. Hence, with $d_\ell=1+q+qv_{\ell,1}$,
$$
 u_{\ell+1,0}=d_\ell u_{\ell,0},\qquad
 v_{\ell+1,i}=\frac{q^{2i}}{d_\ell}\left(v_{\ell,i-1}+(1+q)v_{\ell,i}+qv_{\ell,i+1}\right)\quad(i\ge1). \tag{2}
$$
For word length $2n+1$ (even-part staircase) the polynomial is $O_n=\sum_i u_{n,i}$. For length $2n$ (odd-part staircase) the last single step gives $B_n=(1+q)\sum_i q^i u_{n-1,i}$. This uses the area $\sum_t\lfloor H_t/2\rfloor$ at the actual vertex heights.

**Stabilization lemma.** There are formal series $d=1+q+O(q^2)$ and $C_\delta=1+O(q)$, with $\delta=m\bmod2$, such that each corank polynomial $Z_n$ satisfies
$$ Z_n(q)=C_\delta(q)d(q)^n-q^{2n+2}+O(q^{2n+3})\qquad(n\ge1). \tag{3}$$
In particular $P_{\delta,k}(n)=[q^k]C_\delta d^n$ is a polynomial in $n$ of degree $k$ with leading coefficient $1/k!$. It agrees with $b_{n,k}$ for $k\le2n+1$ and exceeds it by exactly one at $k=2n+2$. Through degree $2n+1$ the log coefficients of $Z_n$ are affine in $n$ with slopes independent of the family.

To prove (3), successive iterates in (2) satisfy
$$v_{\ell,1}-v_{\ell-1,1}=q^{2\ell}+O(q^{2\ell+1}),\qquad
v_{\ell,i}-v_{\ell-1,i}=O(q^{2\ell+2})\quad(i\ge2).$$
At $\ell=1$ the only positive-index entry is $q^2/(1+q)$. In the induction the inverse denominator changes by $O(q^{2\ell+1})$. The only leading term at $i=1$ is the previous change in $(1+q)v_{\ell,1}$ multiplied by $q^2/d_\ell$. The factors $q^{2i}$ at $i\ge2$ raise every change by at least four degrees. The limits $v_i,d=1+q+qv_1$ therefore exist coefficientwise. Sums over $i$ are locally finite because a path first reaching $2i+1$ costs at least $i^2$ area. In particular
$$v_1-v_{n,1}=q^{2n+2}+O(q^{2n+3}),\qquad d-d_n=q^{2n+3}+O(q^{2n+4}).$$
The product $u_{n,0}/d^n=\prod_{\ell=0}^{n-1}(d_\ell/d)$ differs from its infinite limit by $O(q^{2n+3})$. For $O_n/u_{n,0}=1+\sum_{i\ge1}v_{n,i}$ the infinite limit exceeds the finite expression by $q^{2n+2}+O(q^{2n+3})$. For the even word length use
$$\frac{B_n}{u_{n,0}}=1+\frac{q^2v_{n-1,1}+(1+q)\sum_{i\ge2}q^i v_{n-1,i}}{d_{n-1}}.$$
The leading change from replacing the iterates by their limits is again $q^{2n+2}$, from the $i=1$ term. This proves (3). Expanding $(1+(d-1))^n$ gives the polynomial claim. Taking formal logarithms gives the affine dependence.

## A zero-free disk for every size

Put $R=39/100$, $t=3/5$ and $s=|1+q|$. On $|q|\le R$ one has
$$|v_{\ell,i}|\le t^i R^{i(i-1)}\qquad(\ell,i\ge0).$$
Induct in $\ell$, starting at $\ell=0$. The denominator in (2) has modulus at least $s-Rt$. For $i\ge1$, dividing the numerator majorant by the proposed bound leaves at most $R^2/t+sR^{2i}+tR^{4i+1}$. This is smaller than $s-Rt$ already at $i=1$, since $R^2/t+tR^5+Rt<(1-R)(1-R^2)$ and $s\ge1-R$.

Each $d_\ell$ differs from one by at most $R(1+t)=.624$. The sum of the bounds on the positive-index $v_{\ell,i}$ is at most $t/(1-tR^2)<.67$. The formulas for $B_n,O_n$ now give nonvanishing on the disk. Choose $L_n=\log Z_n$ with zero constant term. Adding the logarithms of the successive factors gives $|L_n|\le2n$ for $n\ge2$: for $O_n$ use $n(-\log(1-.624))-\log(1-.67)$, and for $B_n$ replace one $d_\ell$ by $1+q$. Thus for $a_h=[q^h]L_n$ we have $|a_h|/n\le2R^{-h}$.

## A rational certificate on a continuum of tilts

Write $Q=9/25$, $w=nq$ and $M(q)=qL'_n(q)$, the mean corank after weighting by $q^k$. For $0<q\le Q$, $n\ge1920$, and $0\le\theta\le\pi$, the following bounds hold:
$$\begin{aligned}
 .70 &< \frac{L_n(q)-\Re L_n(qe^{i\theta})}{w(1-\cos\theta)} < 1.50,\\
 \left|\sum_{h\ge1}h^3 a_h q^{h-1}\cos(h\theta)/n\right|&<3
       \qquad(\cos\theta\ge15/16),\\
 M(Q)/n&>1/3. \tag{4}
\end{aligned}$$
At $\theta=0$ use the continuous extension. The [certificate](verify_paired.py) proves (4) with integers and rational numbers by the following steps.

1. Compute $g_h=ha_h$ through $H=432$ from the ballot recurrence at $n=433,434$ via $qZ_n'=Z_n\sum_h g_h q^h$. Equation (3) determines these coefficients for all $n\ge1920$. Each $g_h/n$ is affine in $1/n$, so it suffices to bound the two finite-size endpoints at $n=1920$ and their common $1/n=0$ limit. The script also checks stabilization at 435 and compares small corank rows with direct partition enumeration.
2. Use $D'=96$ terms for the first two expressions. For $D'<h\le H$ their tails are bounded using the actual $|g_h|/n$ at each size endpoint, multiplied by $hQ^{h-1}$ or $h^2Q^{h-1}$ respectively. For $h>H$ the Cauchy bound above gives a common error at most
$$\frac{(2/R)(H+1)^3(Q/R)^H}{1-(Q/R)((H+2)/(H+1))^3}.$$
For the mean $M(Q)/n$ use all $H$ exact coefficients and $Q$ times this last bound.
3. In the first expression the angular polynomial at degree $h$ is $h+2\sum_{j=1}^{h-1}(h-j)T_j(x)$ with $x=\cos\theta$. This is $(1-\cos(h\theta))/(1-\cos\theta)$ by the finite geometric sum. For the second use $T_h(x)=\cos(h\theta)$. On each rectangle in $(q,x)$ put the truncated polynomial in the tensor-product Bernstein basis of degree 96 in each variable. Its values are bounded by the smallest and largest coefficients because these basis functions are nonnegative and sum to one. The first rectangle dimension is $[0,Q]$. The second is split at multiples of $1/8$ from $-1$ to $1$ for the first bound, and is $[15/16,1]$ for the second bound. After each affine change to $[0,1]$, the $i$th Bernstein coefficient of the monomial of degree $j$ is $\binom ij/\binom{96}j$, zero for $i<j$. The verifier checks the inequalities after including all tails.

## Inversion at the finite mean

The limit of the first ratio in (4) at zero is the tilted variance divided by $w$. Since $qM'(q)$ equals that variance and $M(0)=0$, integration gives $.70w<M(q)<1.50w$. For $k>640$ with $k\le n/3$, we have $n\ge1923$. Choose $q\in(0,Q)$ with $M(q)=k$ using (4) and positive variance. In particular $w>641/1.50>427$.

Write the centered characteristic function as $\Phi=\exp(-A+iB)$, with $A=L_n(q)-\Re L_n(qe^{i\theta})$ and $B=\Im L_n(qe^{i\theta})-k\theta$. In $x=\sqrt w\,\theta\le4$ we have $\cos\theta\ge15/16$. The third derivative bound in (4) gives $|B|\le x^3/(2\sqrt w)$ since $B(0)=B'(0)=B''(0)=0$. In particular $\Re\Phi\ge0$ there. On $0\le x\le1.5$, $\cos B>.99$, $e^{-A}\ge e^{-.75 x^2}$ and $2w(1-\cos\theta)\ge.99x^2$ by Taylor's inequality.

Over the half period $0\le x\le\pi\sqrt w$ denote the integrals of $\Re\Phi$ and $2w(1-\cos\theta)\Re\Phi$ by $I_0,I_2$. The contribution from $[0,1.5]$ to $I_2$ exceeds $.99^2 e^{-.75(1.5)^2}(1.5)^3/3>.20$. For $4\le x\le\pi\sqrt w/2$ the absolute cost is below
$$\int_4^\infty x^2 e^{-.28 x^2}\,dx<.10,$$
using $1-\cos\theta\ge4\theta^2/\pi^2$ up to $\pi/2$. The last bound follows by integrating by parts and bounding $\int_4^\infty e^{-b x^2}\,dx\le e^{-16b}/(8b)$. The rest of the period costs at most $2\pi w^{3/2}e^{-.70w}<.001$. Thus $I_2>.099$. We also have $0<I_0<2$ by inversion at positive tilted mass and the absolute upper bound $\int_0^\infty e^{-.28x^2}\,dx+(\pi\sqrt w/2)e^{-.70w}$.

For the tilted masses $p_i$, Fourier inversion gives $(2p_k-p_{k-1}-p_{k+1})/p_k=I_2/(wI_0)>.049/w$. Hence by the arithmetic-geometric mean inequality,
$$\frac{b_{n,k-1}b_{n,k+1}}{b_{n,k}^2}
=\frac{p_{k-1}p_{k+1}}{p_k^2}
\le(1-.024/w)^2<1-.04/w<1-\frac1{40k},$$
using $k>.70w$. For $1\le k\le640$, $n\ge9$ and $k\le n/3$ apply the [fixed-corank Newton certificate](fixed-corank.md#certifying-a-corank-for-all-larger-sizes). Its verifier also checks $3\le n\le8$ directly. This completes (1).

Run both certificates from the checkout with Python 3.9 or later.

~~~sh
python3 -B verify_paired.py
python3 -B verify_corank.py --max-corank 640 --direct-n 12
~~~
