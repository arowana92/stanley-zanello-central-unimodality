# Stanley–Zanello central unimodality conjecture

**Work in progress.** Richard Stanley and Fabrizio Zanello posed this conjecture in 2013. It is Conjecture 3.4 in the published version of *Unimodality of partitions with distinct parts inside Ferrers shapes*.

For each positive integer $n$, consider the two shapes $(2n-1,2n-3,\ldots,1)$ and $(2n,2n-2,\ldots,2)$. For either shape $\lambda$, let $a_j$ count the partitions of $j$ into distinct positive parts that fit inside $\lambda$. This means the partition has at most $n$ parts and its $i$th largest part is at most $\lambda_i$. The empty partition contributes $a_0=1$.

The conjecture says that for each shape and every $n$, the sequence from $a_0$ through $a_{|\lambda|}$ rises weakly to a peak and then falls weakly. Equal adjacent counts are allowed.

[2013 preprint](https://arxiv.org/abs/1305.6083) · [Authors’ final paper](https://math.mit.edu/~rstan/papers/distinctparts.pdf)

## Asymptotic result and finite-size gap

The research draft gives an explicit finite reduction for **both central families**. Define $A_1=10$ and $A_{i+1}=10^{A_i}$. The proof gives unimodality for every $n\ge A_{16}$, and exact computation verifies every $1\le n\le256$. The outstanding sizes lie between 257 and $A_{16}-1$. The upper bound is far too large for exhaustive verification. [Proof of the finite reduction](finite-reduction.md)

At $n\ge A_{16}$ the coefficients satisfy the stronger inequality $a_j^2>a_{j-1}a_{j+1}$ at every interior upper-half rank $j\ge D/2$, where $D=|\lambda|$. At **every** size it holds when $1\le D-j\le n/105$. The proof uses a zero-free disk for the finite rank polynomial written in reverse order. [Upper-half curvature proof](upper-curvature.md)

Write $m=2n$ or $2n+1$ for the word length, $D$ for the degree and $k=D-j$ for the number of missing cells at rank $j$. For both families, every global peak has $k/m^{3/2}$ tending to the mode of half the area under a standard Brownian meander. The proof controls adjacent coefficients in four ranges.

| Range | Argument |
| --- | --- |
| $k/m$ bounded | Counting edges near the full shape and a fixed-tilt coefficient ratio give growth in corank. [Tail estimates, §3](monotonicity.md#3-decrease-near-the-top) |
| $k/m\to\infty$ and $k/m^{3/2}\to0$ | A transfer operator on blocks of length about $(k/m)^2$ gives an adjacent-difference estimate smaller than the shrinking tilt. [Small-area proof and conclusion](small-area.md) |
| $k/m^{3/2}$ in a compact subinterval of $(0,\infty)$ | Fourier bounds for paired steps give strict log-concavity, including throughout the peak window. [Peak-window proof](peak-window.md) |
| $k/m^{3/2}\to\infty$ | An independent Bernoulli tilt gives growth in rank past the midpoint. A parabolic Bruhat interval inequality covers the lower half. [Rising-side proof](rising-side.md) · [Lower-half argument](monotonicity.md#1-lower-half-for-all-sizes) |

There is an explicit result for the high-rank end. For both families and every $n\ge100$, the coefficients decrease strictly over the final $9n+42$ rank steps. A finite bridge calculation gives this infinite-size bound by concatenation. For any chosen integer $c>0$, the same method computes a cutoff for the final $cn$ steps. [Finite-tail theorem and verifier](finite-tail.md)

There is also an explicit bound on the increasing side. For both families the coefficients increase strictly and are strictly log-concave at every rank $D/2\le j\le D-200m^{3/2}$. This leaves at most $200m^{3/2}+O(1)$ ranks to examine at any size, before applying the linear tail bound. The constant is large enough that the new interval first becomes nonempty at $m=2{,}560{,}000$. [Finite-size proof with constants](effective-middle.md)

A separate uniform transfer estimate reaches the scale of the peak from the high-rank end. With $c_*=\exp(-10^{311})$, the corank coefficients increase strictly and are strictly log-concave for $2n\le k\le c_*n^{3/2}$. The constant makes this a theoretical improvement on the linear bound only at extremely large sizes. [Effective small-area proof](effective-small-area.md)

The [subsequence argument](small-area.md#consequence-and-finite-size-gap) gives a qualitative proof. The explicit version bounds the errors in the first two lattice differences on the interval containing the peak, using [exact finite-size area moments](finite-reduction.md#exact-area-moments).

## Literature check

I found no proof or counterexample covering either entire central family in the literature checked on 26 November 2026. Proposition 3.2 of the authors’ paper gives a ballot-word bijection. Theorem 3.7 settles both families for at most three rows. Their nonunimodal four-row example is $(9,7,5,3)$. The four-row shapes in Conjecture 3.4 are $(7,5,3,1)$ and $(8,6,4,2)$. [Stanley and Zanello, §3](https://math.mit.edu/~rstan/papers/distinctparts.pdf)

Alpoge’s *Proof of a conjecture of Stanley–Zanello* counts distinct parts with an upper bound on the largest part and on the number of parts. This gives consecutive row lengths with the largest length sufficiently large relative to the row count. Zbarsky explicitly discusses the small-final-part arithmetic progressions in the concluding section of his later paper. His Corollary 4 covers strict shapes with largest part at least half the total size, which excludes both central shapes for $n\ge4$. [Alpoge](https://arxiv.org/abs/1308.2358) · [Zbarsky](https://arxiv.org/abs/1408.3895)

I checked the publisher’s forward citations and searched for the central statement under both shifted-partition and ballot-path terminology. The cited 2016–2020 works treat Gaussian polynomials, their differences, or alternating gamma vectors. The 2026 citation studies reciprocals of products over subsets of the parts of a given partition. None supplies the missing implication for these rank polynomials. [Publisher’s citation list](https://www.sciencedirect.com/science/article/pii/S0195669815000682) · [Alternating gamma vectors](https://www.combinatorics.org/ojs/index.php/eljc/article/download/v23i2p40/pdf/) · [Gaussian coefficient asymptotics](https://math.mit.edu/~rstan/papers/asymptotics4.pdf) · [Bergeron’s problem](https://arxiv.org/abs/1709.06187) · [Reiner–Stanton generalization](https://arxiv.org/abs/1711.10033) · [Reciprocals of subsum polynomials](https://link.springer.com/article/10.1007/s11139-026-01419-0)

Koutschan, Uncu and Wong also prove two cases of a Stanley–Zanello conjecture. Their Theorems 12 and 13 treat $m=6,7$ in the authors’ 2020 conjecture about differences of Gaussian polynomials. [Koutschan, Uncu and Wong, §4](https://arxiv.org/pdf/2302.04067)

## Catalan recurrences for the two families

Let $B_n(q)$ and $O_n(q)$ be the **corank** polynomials for word lengths $2n$ and $2n+1$, respectively. Let $C_n(q)$ count the length-$2n$ walks that return to zero by the same area $\sum_t\lfloor H_t/2\rfloor$. All three initial values are one. First return to zero gives the Carlitz–Riordan recurrence $C_n=\sum_{i=0}^{n-1}q^i C_i C_{n-1-i}$.

Stump's type $B$ Catalan area polynomial is exactly $B_n$. The even-part staircase has the following additional convolution with $B_h$.
$$B_n=C_n+\sum_{h=0}^{n-1}q^{2h+1}B_h C_{n-h},\qquad
O_n=\sum_{h=0}^n q^h B_h C_{n-h}.$$
The first recurrence and its initial condition are Stump's Theorem 3.1. His Gaussian polynomial in Proposition 3.5 tracks the flag major index. The more recent asymptotic type $B$ Fuss–Catalan formula concerns a sufficiently large power of the alternating ideal. Neither result gives an all-size sign theorem for these area coefficients. [Stump, §3](https://arxiv.org/abs/0808.2822) · [Oblomkov](https://arxiv.org/abs/2609.11691)

To verify the identification and the second formula, cut a path at its last zero. An odd-length path consists of an excursion of length $2(n-h)$, the up-step from the last zero, and a translated even-length meander of length $2h$. Translation by one adds $h$ to its area, one for every odd time in the meander. This gives $O_n$. An even-length path either returns to zero or decomposes in the same way with an odd-length meander of length $2h-1$, so $B_n=C_n+\sum_{h=1}^n q^h C_{n-h}O_{h-1}$. For the ordinary generating series in $z$, these identities read $O(z)=C(z)B(qz)$ and $B(z)=C(z)(1+qzO(qz))$. Substitution and $zC(z)C(qz)=C(z)-1$ yield $B(z)=C(z)+q(C(z)-1)B(q^2z)$, which gives Stump's recurrence coefficient by coefficient.

## Exact coefficient checks

Use a word of length $m=2n$ for the odd-part shape and $m=2n+1$ for the even-part shape. Reading positions $m,m-1,\ldots,1$, take a down step for each chosen part and an up step otherwise. The $i$th down step occurs at time at least $2i$ precisely when the $i$th part is at most $m-2i+1$. Thus the admissible words are exactly the walks from zero staying nonnegative.

Let $P_{m,d}$ record the sum of parts for words with $d$ downs. Appending a final step increases every old part by one. A final down also contributes a new part of size one. In both cases the total increment equals the new number $d$ of downs. Hence
$$P_{m,d}=q^d(P_{m-1,d}+P_{m-1,d-1}),\qquad 0\le d\le\lfloor m/2\rfloor.$$
Start at $P_{0,0}=1$, use zero outside the admissible range, and sum over $d$ to obtain the rank polynomial.

```sh
python3 -B verify.py --max-n 256 --direct-n 12 --upper-curvature
```

All 512 rank sequences pass the weak unimodality test. The script checks every coefficient against recursive enumeration of the actual parts and the Catalan recurrences for $1\le n\le12$, verifies each total against $\binom{m}{n}$, and detects the published valley $17,16,17$ at ranks 16–18 of $(9,7,5,3)$. At $n=256$ the unique peaks are at rank 61456 of 65536 and rank 61697 of 65792, respectively. The calculation uses arbitrary-precision integers. Add `--verbose` for the peak ranks and sizes of every shape. These are finite checks.

The curvature scan finds $a_j^2>a_{j-1}a_{j+1}$ at every interior rank $j\ge D/2$ for both families and every $9\le n\le256$. At $n=8$ direct enumeration gives the triple $(448,465,483)$ centered at rank 44 in the odd-part shape and $(392,423,457)$ centered at rank 38 in the even-part shape. Their log-concavity determinants are $-159$ and $-215$, respectively, and both triples are increasing. Proving upper-half log-concavity for the outstanding sizes would suffice for Conjecture 3.4 by the lower-half increase and the direct checks for $n<9$.

At fixed corank $k=D-j$, the coefficient is polynomial in $n$ for $n\ge k$. Exact forward differences certify strict log-concavity for both families at all $1\le k\le256$ and all $n\ge\max(4,k+1)$. Together with the rank scan this covers every interior upper-half rank of corank at most 256 for all $n\ge9$. A counting argument proves the same strict inequality for every $k\ge1$ when $n\ge4(k+1)^2$. [Polynomial proof and certificate command](fixed-corank.md)
