# An exact expansion in corank for both staircases

Write $Z_{n,0}=B_n$ for the odd-part staircase and $Z_{n,1}=O_n$ for the even-part staircase. The exponent of $q$ counts missing cells. For each $\delta\in\{0,1\}$ and $n\ge1$ there is a coefficientwise identity in $\mathbb Z[[q]]$
$$
 Z_{n,\delta}(q)=\sum_{r\ge0} A_{\delta,r}(q)d_r(q)^n. \tag{1}
$$
The $d_r$ are common to both families. The first degree of every summand, and its coefficient there, are explicit. Set
$$
 \alpha_{0,r}=2\lceil r/2\rceil,\qquad \alpha_{1,r}=2r.
$$
Then
$$
 d_r=q^{2r}\big(1+q^{r+1}+O(q^{r+2})\big),\qquad
 A_{\delta,r}=(-1)^r q^{\alpha_{\delta,r}}\big(1+O(q)\big). \tag{2}
$$
In particular, retaining $r=0,\ldots,R-1$ gives **every coefficient through corank $2Rn+\alpha_{\delta,R}-1$ exactly**. At the very next corank the true count minus that approximation is $(-1)^R$. Two terms suffice through $4n+1$ for the odd-part family and $4n+3$ for the even-part family.

For a fixed $r$ the contribution at $k=2rn+\alpha_{\delta,r}+h$ is a polynomial in $n$ of degree at most $\lfloor h/(r+1)\rfloor$ for $h\ge0$. When $h=(r+1)t$ its leading coefficient is $(-1)^r/t!$. Indeed, expand $(q^{-2r}d_r)^n$ in powers of $q^{-2r}d_r-1$ using binomial coefficients. Its $t$th power starts with $q^{(r+1)t}$. This gives an exact finite formula along every range $k\le cn$ with $c$ fixed, using at most $1+\lfloor c/2\rfloor$ summands.

## The common denominator and the two numerators

Haug's thesis, which credits this chapter to work with Christoph Richard, gives the Bernoulli meander generating function $M(x,v)$ as a sum of endpoint contributions over a common $q$-Airy denominator. Its area is $\sum_t H_t=2k+n+\delta$ because exactly $n+\delta$ of the heights are odd. Consequently $[x^{2n+\delta}]M(x,v)=v^{n+\delta} Z_{n,\delta}(v^2)$. We give the endpoint argument in the staircase variables below and collect the numerator by length in (3). Proposition 7.4.1 in the thesis gives a scaling limit of the generating function. [Haug and Richard, equations (7.7)–(7.8) and Proposition 7.4.1 in Chapter 7](https://webspace.maths.qmul.ac.uk/t.prellberg/haug.pdf)

Use $(q;q)_i=\prod_{j=1}^i(1-q^j)$, with empty product one. The ordinary generating function of Dyck excursions weighted by semilength $z$ and area $q$ is $C(z)=H(qz)/H(z)$, where
$$H(z)=\sum_{i\ge0}\frac{(-1)^iq^{i(i-1)}z^i}{(q;q)_i}.$$
This is the Carlitz–Riordan excursion series. Its first-return equation $C(z)=1+zC(z)C(qz)$ follows by cutting at the first return. The quotient solves it because $H(z)=H(qz)-zH(q^2z)$, as seen by comparing coefficients. [Haug and Prellberg, equations (6)–(8)](https://webspace.maths.qmul.ac.uk/t.prellberg/papers/pub100.pdf#page=3)

In a nonnegative walk ending at height $h$, separate the $h$ up-steps left unmatched by subsequent down-steps. There is one excursion slot at each height $0,\ldots,h$. Translating an excursion of semilength $l$ to height $j$ adds $jl$ to the area $\sum_t\lfloor H_t/2\rfloor$, since its $2l$ vertices after steps have alternating parity. The unmatched steps contribute $\sum_{j=1}^h\lfloor j/2\rfloor=\lfloor h^2/4\rfloor$. With $h=2p+\delta$, the unpaired climb uses $p$ units of the size parameter $n$. Its endpoint contribution to the generating function is therefore
$$
 z^p q^{p(p+\delta)}\prod_{j=0}^{2p+\delta}C(q^jz)
 =z^p q^{p(p+\delta)}H(q^{2p+\delta+1}z)/H(z).
$$
On summing over $p$, the powers of $q$ in numerator degree $l=p+i$ simplify to $l(l+\delta)$. Hence
$$
 \sum_{n\ge0} Z_{n,\delta}(q)z^n=\frac{N_\delta(z)}{H(z)},\qquad
 N_\delta(z)=\sum_{l\ge0}q^{l(l+\delta)}s_l z^l,\qquad
 s_l=\sum_{i=0}^l\frac{(-1)^i}{(q;q)_i}. \tag{3}
$$
For even $l$, $s_l=1+O(q)$. For odd $l$, $s_l=-q+O(q^2)$ because pairing terms $2j,2j+1$ gives $-q^{2j+1}/(q;q)_{2j+1}$.

## The roots as integer power series

Ismail and Zhang studied analytic representations and expansions of the large zeros of Ramanujan's entire function. Here we expand at $q=0$ for each root index and keep the residues of both staircase numerators to locate the first affected rank. [Ismail and Zhang, *Zeros of entire functions and a problem of Ramanujan*](https://www.sciencedirect.com/science/article/pii/S0001870806001605)

Fix $r\ge0$. Substitute $z=q^{-2r}x$ in $H$ and multiply by $q^{r(r+1)}$. This gives
$$
 h_r(x)=\sum_{i\ge0}\frac{(-1)^i q^{(i-r)(i-r-1)}}{(q;q)_i}x^i .
$$
Every coefficient of $q$ here is a polynomial in $x$. At $q=0$ it reduces to $(-1)^rx^r(1-x)$. Thus there is a unique $x_r=1+O(q)$ with $h_r(x_r)=0$. Successively equating coefficients determines the next integer coefficient of $x_r$, since the derivative at $x=1$ has constant term $(-1)^{r+1}$.

To find its first displacement, evaluate at $x=1$ and pair $i=r-t$ with $i=r+1+t$ for $0\le t\le r$. Their common explicit power is $q^{t(t+1)}$. The difference between the two reciprocal Pochhammers starts in degree $r-t+1$, because their extra factors begin with $(1-q^{r-t+1})^{-1}$. Hence the pair starts in degree $r+1+t^2$. The unpaired terms have degree at least $(r+1)(r+2)$. The $t=0$ pair gives $h_r(1)=(-1)^{r+1}q^{r+1}+O(q^{r+2})$. Therefore $x_r=1-q^{r+1}+O(q^{r+2})$ and $d_r=q^{2r}/x_r$ satisfies (2).

In the same coordinates the rescaled numerator is
$$
 u_{\delta,r}(x)=q^{r(r+1)}N_\delta(q^{-2r}x)
 =\sum_{i\ge0} q^{(i-r)^2+r+\delta i}s_i x^i .
$$
Define $A_{\delta,r}=-u_{\delta,r}(x_r)/(x_r h'_r(x_r))$. Its denominator is a unit with constant term $(-1)^{r+1}$. For $\delta=0$ and even $r$, only $i=r$ contributes at degree $r$, with coefficient one. For odd $r$ the three indices $r-1,r,r+1$ contribute $1,-1,1$ at degree $r+1$. For $\delta=1$ the explicit exponent is $(i-r)(i-r+1)+2r$. Its minimum is attained at $r-1,r$ among nonnegative indices when $r\ge1$. Exactly one index is even and gives coefficient one there. At $r=0$ the minimum comes from $i=0$. This proves the amplitude assertion in (2).

## Passing from finite fractions to the full coefficient

Truncate $H$ at $z^L$ inclusive and each $N_\delta$ at $z^{L-1}$ inclusive. The preceding simple-root construction gives $L$ roots $q^{-2r}x_{r,L}$ for $0\le r<L$. Their respective lowest powers $-2r$ are distinct, so these are all roots of the degree-$L$ denominator over $\mathbb Q((q))$. Partial fractions for the proper rational function give its $z^n$ coefficient as the sum of the $L$ corresponding terms $A_{\delta,r,L}(q^{2r}/x_{r,L})^n$. The partial fraction numerator at a simple root $z_0$ is $-N_\delta(z_0)/(z_0 H'(z_0))$ for the factor $(1-z/z_0)^{-1}$, using the truncated polynomials here.

At fixed $r$, every $q$-coefficient in the rescaled numerator, denominator and derivative is eventually independent of $L$. Recursive determination of the simple root and division by the unit derivative preserve this property for $x_{r,L}$ and $A_{\delta,r,L}$. Uniformly in $L>r$, the amplitude is divisible by $q^{\alpha_{\delta,r}}$. The same minimum-exponent bounds apply even if truncation omits an index attaining the minimum. Consequently only finitely many $r$ can affect a prescribed coefficient of $q$. For $L>n$, the left side is already $Z_{n,\delta}$, so taking the coefficientwise limit proves (1). For $n\ge1$ the initial degrees $2rn+\alpha_{\delta,r}$ increase strictly. This proves the sharp error assertion.

## Effect on adjacent coranks

For the principal term $P_{n,\delta}=A_{\delta,0}d_0^n$, the first errors are as follows for $n\ge2$. Each entry is $[q^k](Z_{n,\delta}-P_{n,\delta})$.

| Corank $k$ | Odd-part staircase | Even-part staircase |
| --- | ---: | ---: |
| $2n+2$ | $-1$ | $-1$ |
| $2n+3$ | $2$ | $2$ |
| $2n+4$ | $-n-4$ | $-n-5$ |
| $2n+5$ | $3n+8$ | $3n+11$ |

For the calculation above, division at $r=1$ gives $d_1/q^2=1+q^2-q^3+O(q^4)$, $A_{0,1}=-q^2+2q^3-4q^4+8q^5+O(q^6)$ and $A_{1,1}=-q^2+2q^3-5q^4+11q^5+O(q^6)$. Higher roots start after the table. The first two errors already have opposite signs, so the stabilized polynomial gives neither a uniform upper bound nor a uniform lower bound on the coefficients past its exact range. The expansion computes the signed corrections for both families. Proving that their sum preserves the required adjacent inequalities in the size gap remains open.

The [integer verifier](verify_modes.py) lifts the simple roots by Newton iteration modulo powers of $q$ and computes both amplitudes by series division. It reconstructs 10,809 coefficients for $1\le n\le48$ up to $\min(128,|\lambda|+8)$, compares them with the ballot recurrence, and compares the complete ballot rows with recursive enumeration of the strict partitions through $n=12$.

~~~sh
python3 -B verify_modes.py
~~~
