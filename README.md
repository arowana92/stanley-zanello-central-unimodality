# Stanley–Zanello central unimodality conjecture

**Work in progress.** Richard Stanley and Fabrizio Zanello posed this conjecture in 2013. In *Unimodality of partitions with distinct parts inside Ferrers shapes* it is Conjecture 3.4 in the authors’ MIT PDF and Conjecture 3.3 in the journal text.

For each positive integer $n$, consider the two shapes $(2n-1,2n-3,\ldots,1)$ and $(2n,2n-2,\ldots,2)$. For either shape $\lambda$, let $a_j$ count the partitions of $j$ into distinct positive parts that fit inside $\lambda$. This means the partition has at most $n$ parts and its $i$th largest part is at most $\lambda_i$. The empty partition contributes $a_0=1$.

The conjecture says that for each shape and every $n$, the sequence from $a_0$ through $a_{|\lambda|}$ rises weakly to a peak and then falls weakly. Equal adjacent counts are allowed.

[2013 preprint](https://arxiv.org/abs/1305.6083) · [Authors’ MIT PDF](https://math.mit.edu/~rstan/papers/distinctparts.pdf#page=8) · [Journal article](https://doi.org/10.1016/j.ejc.2015.03.007)

## Asymptotic result and finite-size gap

The research draft proves unimodality for **both central families** whenever $n\ge N=10^{17}$. Both are also verified for **every $1\le n\le2048$**. The remaining size gap is $2049\le n<N$. Whole-row integer computation covers the first 384 sizes. A first-passage estimate and certified signs of adjacent-coefficient determinants extend the finite result to 2048. [Proof of the large-size threshold](prefix-clock.md) · [Finite sign certificate](certified-window.md)

At $n\ge10^{88}$ the coefficients satisfy the stronger inequality $a_j^2>a_{j-1}a_{j+1}$ at every interior upper-half rank $j\ge D/2$, where $D=|\lambda|$. At **every size**, writing $k=D-j$, the determinant $a_j^2-a_{j-1}a_{j+1}$ exceeds $a_j^2/(40k)$ for $1\le k\le n/3$. For every $n\ge9$ it also exceeds this bound through $k=\min(4096,2n)$ and is positive through $k=\min(4096,\lfloor D/2\rfloor)$. [Paired-step proof](paired-steps.md) · [All-size corank certificate](certified-window.md#a-fixed-corank-range-at-every-size) · [Upper-half curvature proof](two-harmonics.md#matching-the-two-area-scales)

Write $m=2n$ or $2n+1$ for the ballot word length, $D$ for the degree and $k=D-j$ for the number of missing cells at rank $j$. At **every $n\ge2$ in both families**, every global maximum satisfies $1/(6\sqrt6)\le k/m^{3/2}<13/20$. The lower constant is attained in $(5,3,1)$ at corank one. At $m\ge3136$ every rank reaching half the maximum lies in $1/15<k/m^{3/2}<3/4$. As $m$ grows, the scaled corank of any maximum tends to the mode of half the area under a standard Brownian meander. [Finite-size mode bounds](mode-bounds.md) · [Limiting mode](peak-window.md#consequences-for-the-coefficients)

The proof controls adjacent coefficients in four ranges.

| Range | Argument |
| --- | --- |
| $k/m$ bounded | Counting edges near the full shape and a fixed-tilt coefficient ratio give growth in corank. [Tail estimates, §3](monotonicity.md#3-decrease-near-the-top) |
| $k/m\to\infty$ and $k/m^{3/2}\to0$ | A transfer operator on blocks of length about $(k/m)^2$ gives an adjacent-difference estimate smaller than the shrinking tilt. [Small-area proof and conclusion](small-area.md) |
| $k/m^{3/2}$ in a compact subinterval of $(0,\infty)$ | Fourier bounds for paired steps give strict log-concavity, including throughout the peak window. [Peak-window proof](peak-window.md) |
| $k/m^{3/2}\to\infty$ | An independent Bernoulli tilt gives growth in rank past the midpoint. A parabolic Bruhat interval inequality covers the lower half. [Rising-side proof](rising-side.md) · [Lower-half argument](monotonicity.md#1-lower-half-for-all-sizes) |

There is an explicit result for the high-rank end. For both families and every $n\ge100$, the coefficients decrease strictly over the final $9n+42$ rank steps. A finite bridge calculation gives this infinite-size bound by concatenation. For any chosen integer $c>0$, the same method computes a cutoff for the final $cn$ steps. [Finite-tail theorem and verifier](finite-tail.md)

For both families and **every** $n$, the coefficients grow strictly at all ranks $D/2\le j\le D-\tfrac32m^{3/2}$. They are strictly log-concave throughout $D/2\le j\le D-2m^{3/2}$. The proof conditions on the first time a walk crosses the ballot boundary and bounds its contribution to the first two coefficient differences. Combined with lower-half growth, this confines a potential reversal to the final $\tfrac32m^{3/2}+O(1)$ ranks. For $k\ge4m^{3/2}$ the earlier argument also gives an explicit lower bound on the adjacent ratio. [Improved first-passage bounds](rising-window.md) · [Quantitative ratio bound](first-passage.md)

For **every $n\ge2$**, both families satisfy $b_{k+1}>b_k$ for all integer coranks $0\le k\le m^{3/2}/70$, where $b_k=a_{D-k}$. Splitting at unmatched up-steps expresses each family as a sum of products of ordinary Dyck area polynomials. The type-A diagonal coinvariant theorem gives a strict comparison on each row through an explicit corank of order $n^{4/3}$. This overlaps a transfer estimate at height 220 and gives the stated $m^{3/2}/70$ bound at all sizes. A possible reversal in the remaining size gap is confined to the interval between this cutoff and $3m^{3/2}/2$, up to the adjacent ranks at the endpoints. [All-size proof and exact comparison](excursion-centers.md) · [Rational verifier](verify_excursion_centers.py)

Every maximizing corank has the two-term expansion $k=x_*m^{3/2}-3m/4+O(\sqrt m(1+\log m)^6)$, where $x_*$ is the mode of half the Brownian meander area. Averaging the Brownian crossing durations and coupling consecutive Dyck excursions gives the second term for both parities. For $m\ge10^{19}$ all coefficients at least $.006\binom{m}{n}/m^{3/2}$ lie in one unimodal interval with at most two consecutive global maxima. At $m\ge10^{20}$ the level drops to $.001\binom{m}{n}/m^{3/2}$. Smaller coefficients can still reverse inside the outstanding size gap. [Peak expansion and finite bounds](centered-clock.md) · [Independent exact moments](finite-reduction.md#exact-area-moments)

## Literature check

I found no proof or counterexample covering either entire central family in the literature checked through 27 November 2026. In the MIT PDF, Proposition 3.2 gives a ballot-word bijection. Theorem 3.7 settles both families for at most three rows. Their nonunimodal four-row example is $(9,7,5,3)$. The four-row shapes in Conjecture 3.4 are $(7,5,3,1)$ and $(8,6,4,2)$. [Stanley and Zanello, §3](https://math.mit.edu/~rstan/papers/distinctparts.pdf)

The same two polynomials appear in Conjecture 3.5 of arXiv versions 1 and 2, Conjecture 3.3 of version 3 and the 2015 journal article, and Conjecture 3.4 on page 8 of the MIT PDF. A search under the journal numbering also found no all-size result for either polynomial. Zbarsky’s concluding reference to Conjecture 3.5 uses the earlier numbering. [Version 1, p. 8](https://arxiv.org/pdf/1305.6083v1#page=8) · [Version 2, p. 8](https://arxiv.org/pdf/1305.6083v2#page=8) · [Version 3, p. 9](https://arxiv.org/pdf/1305.6083v3#page=9) · [European Journal of Combinatorics, §3](https://doi.org/10.1016/j.ejc.2015.03.007) · [Zbarsky, §7](https://arxiv.org/pdf/1408.3895#page=14)

Alpoge’s *Proof of a conjecture of Stanley–Zanello* counts distinct parts with an upper bound on the largest part and on the number of parts. This gives consecutive row lengths with the largest length sufficiently large relative to the row count. Zanello identifies this consecutive-row statement as the one Alpoge solved in his 2015 conference abstract. Zbarsky explicitly discusses the small-final-part arithmetic progressions in the concluding section of his later paper. His Corollary 4 covers strict shapes with largest part at least half the total size, which excludes both central shapes for $n\ge4$. [Alpoge](https://arxiv.org/abs/1308.2358) · [Zanello, p. 24](https://pages.mtu.edu/~tonchev/absn#page=24) · [Zbarsky](https://arxiv.org/abs/1408.3895)

I checked the publisher’s forward citations and searched for the central statement under both shifted-partition and ballot-path terminology. The cited 2016–2020 works treat Gaussian polynomials, their differences, or alternating gamma vectors. The 2026 citation studies reciprocals of products over subsets of the parts of a given partition. None supplies the missing implication for these rank polynomials. [Publisher’s citation list](https://www.sciencedirect.com/science/article/pii/S0195669815000682) · [Alternating gamma vectors](https://www.combinatorics.org/ojs/index.php/eljc/article/download/v23i2p40/pdf/) · [Gaussian coefficient asymptotics](https://math.mit.edu/~rstan/papers/asymptotics4.pdf) · [Bergeron’s problem](https://arxiv.org/abs/1709.06187) · [Reiner–Stanton generalization](https://arxiv.org/abs/1711.10033) · [Reciprocals of subsum polynomials](https://link.springer.com/article/10.1007/s11139-026-01419-0)

Koutschan, Uncu and Wong also prove two cases of a Stanley–Zanello conjecture. Their Theorems 12 and 13 treat $m=6,7$ in the authors’ 2020 conjecture about differences of Gaussian polynomials. [Koutschan, Uncu and Wong, §4](https://arxiv.org/pdf/2302.04067)

Haug and Richard's Bernoulli meander generating function covers both central families. At length $m=2n+\delta$ their area is twice the corank plus $n+\delta$, the number of odd-time vertices. Their endpoint formula and scaling limit concern the same counts after this change of variables. The fixed-length adjacent inequalities remain to be shown throughout the size gap. [Haug's thesis, Chapter 7, particularly (7.8) and Proposition 7.4.1](https://webspace.maths.qmul.ac.uk/t.prellberg/haug.pdf) · [Parity extraction](formal-roots.md#the-common-denominator-and-the-two-numerators)

In the root-poset literature the odd-part coefficient $a_j$ counts the $j$-dimensional ad-nilpotent ideals of a Borel subalgebra of type $B_n$. The even-part coefficient counts the $j$-dimensional ideals in type $B_{n+1}$ that contain no simple root space. Indeed, in Shi's diagram model the cells in the shifted odd staircase are the positive roots, an ideal occupies a shifted subdiagram, and each selected root space has dimension one. In the diagram for $B_{n+1}$ the rightmost cell of each row is a simple root. Removing all such cells gives precisely $(2n,2n-2,\ldots,2)$. Cellini, Möseneder Frajria and Papi count the ideals by the number of contained simple root spaces. For the even family their zero-simple-root formula supplies the sum of the coefficients. It leaves the distribution by dimension open. [Cellini, Möseneder Frajria and Papi, §§1–2](https://arxiv.org/pdf/math/0401090#page=3)

## Catalan recurrences for the two families

Let $B_n(q)$ and $O_n(q)$ be the **corank** polynomials for word lengths $2n$ and $2n+1$, respectively. Let $C_n(q)$ count the length-$2n$ walks that return to zero by the same area $\sum_t\lfloor H_t/2\rfloor$. All three initial values are one. First return to zero gives the Carlitz–Riordan recurrence $C_n=\sum_{i=0}^{n-1}q^i C_i C_{n-1-i}$.

Stump's type $B$ Catalan area polynomial is exactly $B_n$. The even-part staircase has the following additional convolution with $B_h$.
$$B_n=C_n+\sum_{h=0}^{n-1}q^{2h+1}B_h C_{n-h},\qquad
O_n=\sum_{h=0}^n q^h B_h C_{n-h}.$$
The first recurrence and its initial condition are Stump's Theorem 3.1. His Gaussian polynomial in Proposition 3.5 tracks the flag major index. The more recent asymptotic type $B$ Fuss–Catalan formula concerns a sufficiently large power of the alternating ideal. Neither result gives an all-size sign theorem for these area coefficients. [Stump, §3](https://arxiv.org/abs/0808.2822) · [Oblomkov](https://arxiv.org/abs/2609.11691)

To verify the identification and the second formula, cut a path at its last zero. An odd-length path consists of an excursion of length $2(n-h)$, the up-step from the last zero, and a translated even-length meander of length $2h$. Translation by one adds $h$ to its area, one for every odd time in the meander. This gives $O_n$. An even-length path either returns to zero or decomposes in the same way with an odd-length meander of length $2h-1$, so $B_n=C_n+\sum_{h=1}^n q^h C_{n-h}O_{h-1}$. For the ordinary generating series in $z$, these identities read $O(z)=C(z)B(qz)$ and $B(z)=C(z)(1+qzO(qz))$. Substitution and $zC(z)C(qz)=C(z)-1$ yield $B(z)=C(z)+q(C(z)-1)B(q^2z)$, which gives Stump's recurrence coefficient by coefficient.

### Extending a shifted diagram by one antidiagonal

Let $T_m=\{(i,j):1\le i\le j,\ i+j\le m\}$ with componentwise order. Its order ideals are the shifted subdiagrams counted by the rank polynomial $A_m(q)$. All cells of $T_{m+1}\setminus T_m$ are maximal and incomparable. For each ideal $I$ of $T_m$ let $f(I)$ count the new cells whose strict predecessors all belong to $I$. Choosing an arbitrary subset of these cells gives exactly the ideals of $T_{m+1}$ that restrict to $I$. Thus
$$A_{m+1}(q)=\sum_{I\in J(T_m)}q^{|I|}(1+q)^{f(I)}.$$
The centers of these binomial summands depend on $I$. An induction on word length would need to control their sum near its peak.

In particular a monotone-ratio comparison of consecutive **corank** rows fails for every $m\ge7$. Write $b_{m,k}=[q^{D_m-k}]A_m$ and $r=D_{m+1}-D_m=\lceil m/2\rceil$. At the final two common coranks $D_m-1,D_m$, the old counts are both one and the new counts are the unrestricted distinct-part counts $Q(r+1),Q(r)$. Indeed, at total size $v\le m$ every strict partition fits $T_{m+1}$, since each part before its $i$th part is at least two and hence $\mu_i\le v-2(i-1)$. For $r\ge4$ increasing the largest part injects partitions of $r$ into those of $r+1$. It misses $(h+1,h)$ when $r+1=2h+1$ and $(h,h-1,1)$ when $r+1=2h$. This gives $Q(r+1)>Q(r)$, so $b_{m+1,k}/b_{m,k}$ drops over the final step. A drop also occurs inside the upper half at $m=8$, from $10/7$ at $k=3$ to $11/8$ at $k=4$. These are obstructions to a comparison across sizes. The individual rank polynomials in this example are unimodal.

## Exact coefficient checks

Use a word of length $m=2n$ for the odd-part shape and $m=2n+1$ for the even-part shape. Reading positions $m,m-1,\ldots,1$, take a down step for each chosen part and an up step otherwise. The $i$th down step occurs at time at least $2i$ precisely when the $i$th part is at most $m-2i+1$. Thus the admissible words are exactly the walks from zero staying nonnegative.

Let $P_{m,d}$ record the sum of parts for words with $d$ downs. Appending a final step increases every old part by one. A final down also contributes a new part of size one. In both cases the total increment equals the new number $d$ of downs. Hence
$$P_{m,d}=q^d(P_{m-1,d}+P_{m-1,d-1}),\qquad 0\le d\le\lfloor m/2\rfloor.$$
Start at $P_{0,0}=1$, use zero outside the admissible range, and sum over $d$ to obtain the rank polynomial.

```sh
python3 -B verify.py --max-n 384 --direct-n 12 --upper-curvature
```

All 768 rank sequences pass the weak unimodality test. The script checks every coefficient against recursive enumeration of the actual parts and the Catalan recurrences for $1\le n\le12$, verifies each total against $\binom{m}{n}$, and detects the published valley $17,16,17$ at ranks 16–18 of $(9,7,5,3)$. At $n=384$ the unique peaks are at rank 139840 of 147456 and rank 140206 of 147840, respectively. The calculation uses arbitrary-precision integers. Add `--verbose` for the peak ranks and sizes of every shape. These are finite checks.

The curvature scan finds $a_j^2>a_{j-1}a_{j+1}$ at every interior rank $j\ge D/2$ for both families and every $9\le n\le384$. At $n=8$ direct enumeration gives the triple $(448,465,483)$ centered at rank 44 in the odd-part shape and $(392,423,457)$ centered at rank 38 in the even-part shape. Their log-concavity determinants are $-159$ and $-215$, respectively, and both triples are increasing. Proving upper-half log-concavity for the outstanding sizes would suffice for Conjecture 3.4 by the lower-half increase and the direct checks for $n<9$.

The finite verification gives upper-half strict log-concavity through $n=2048$. Across both families, a calculation with explicit rounding and underflow bounds certifies 843,349,446 determinants at $9\le n\le2048$ and $4097\le k\le\min(\lfloor D/2\rfloor,\lfloor2m^{3/2}\rfloor)$. The fixed-corank certificate supplies the indices through 4096 and a first-passage estimate covers $k\ge2m^{3/2}$. [Finite sign verifier and error proof](certified-window.md) · [First-passage estimate](rising-window.md)

At fixed corank $k=D-j$, the coefficient agrees with a polynomial in $n$ through $k=2n+1$. At $k=2n+2$ the polynomial exceeds the count by one. Exact Newton coefficients certify strict log-concavity with relative determinant greater than $1/(40k)$ for both families when $1\le k\le640$ and $n\ge\max(9,\lceil k/2\rceil)$. Together with the rank scan this gives strict log-concavity at every interior upper-half rank of corank at most 640 for all $n\ge9$. [Stabilization proof](paired-steps.md#an-exact-stabilization-identity) · [Newton certificate](fixed-corank.md)

The two corank generating functions share the $q$-Airy denominator of the Dyck excursion series. Its formal roots give an exact expansion for every size. Keeping the first two terms recovers every coefficient through $k=4n+1$ for the odd-part family and $k=4n+3$ for the even-part family. Keeping more terms covers any prescribed linear range. The first correction changes sign between coranks $2n+2$ and $2n+3$ in both families, which prevents using the principal term alone as a one-sided bound. [Expansion, sharp cutoff and coefficient checks](formal-roots.md)
