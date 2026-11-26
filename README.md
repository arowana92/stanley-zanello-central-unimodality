# Stanley–Zanello central unimodality conjecture

**Work in progress.** Richard Stanley and Fabrizio Zanello posed this conjecture in 2013. It is Conjecture 3.4 in the published version of *Unimodality of partitions with distinct parts inside Ferrers shapes*.

For each positive integer $n$, consider the two shapes $(2n-1,2n-3,\ldots,1)$ and $(2n,2n-2,\ldots,2)$. For either shape $\lambda$, let $a_j$ count the partitions of $j$ into distinct positive parts that fit inside $\lambda$. This means the partition has at most $n$ parts and its $i$th largest part is at most $\lambda_i$. The empty partition contributes $a_0=1$.

The conjecture says that for each shape and every $n$, the sequence from $a_0$ through $a_{|\lambda|}$ rises weakly to a peak and then falls weakly. Equal adjacent counts are allowed.

[2013 preprint](https://arxiv.org/abs/1305.6083) · [Authors’ final paper](https://math.mit.edu/~rstan/papers/distinctparts.pdf)

## Partial results for arbitrary sizes

Write $m=2n$ or $2n+1$ for the word length, $D$ for the degree and $k=D-j$ for the number of missing cells at rank $j$. On each fixed window $u m^{3/2}\le k\le v m^{3/2}$ with $0<u<v$, the coefficients are strictly log-concave for all sufficiently large $n$. Every global maximum has $k/m^{3/2}$ tending to the same positive constant in both families. The outer ranges admit further adjacent-coefficient inequalities. The notes give the proofs and the gaps in full unimodality. [Peak window](peak-window.md) · [Tail inequalities](monotonicity.md)

## Literature check

I found no proof or counterexample covering either entire central family in the literature checked on 26 November 2026. Proposition 3.2 of the authors’ paper gives a ballot-word bijection. Theorem 3.7 settles both families for at most three rows. Their nonunimodal four-row example is $(9,7,5,3)$. The four-row shapes in Conjecture 3.4 are $(7,5,3,1)$ and $(8,6,4,2)$. [Stanley and Zanello, §3](https://math.mit.edu/~rstan/papers/distinctparts.pdf)

Alpoge’s *Proof of a conjecture of Stanley–Zanello* counts distinct parts with an upper bound on the largest part and on the number of parts. This gives consecutive row lengths with the largest length sufficiently large relative to the row count. Zbarsky explicitly discusses the small-final-part arithmetic progressions in the concluding section of his later paper. His Corollary 4 covers strict shapes with largest part at least half the total size, which excludes both central shapes for $n\ge4$. [Alpoge](https://arxiv.org/abs/1308.2358) · [Zbarsky](https://arxiv.org/abs/1408.3895)

I checked the publisher’s forward citations and searched for the central statement under both shifted-partition and ballot-path terminology. The cited 2016–2020 works treat Gaussian polynomials, their differences, or alternating gamma vectors. The 2026 citation studies reciprocals of products over subsets of the parts of a given partition. None supplies the missing implication for these rank polynomials. [Publisher’s citation list](https://www.sciencedirect.com/science/article/pii/S0195669815000682) · [Alternating gamma vectors](https://www.combinatorics.org/ojs/index.php/eljc/article/download/v23i2p40/pdf/) · [Gaussian coefficient asymptotics](https://math.mit.edu/~rstan/papers/asymptotics4.pdf) · [Bergeron’s problem](https://arxiv.org/abs/1709.06187) · [Reiner–Stanton generalization](https://arxiv.org/abs/1711.10033) · [Reciprocals of subsum polynomials](https://link.springer.com/article/10.1007/s11139-026-01419-0)

## Exact coefficient checks

Use a word of length $m=2n$ for the odd-part shape and $m=2n+1$ for the even-part shape. Reading positions $m,m-1,\ldots,1$, take a down step for each chosen part and an up step otherwise. The $i$th down step occurs at time at least $2i$ precisely when the $i$th part is at most $m-2i+1$. Thus the admissible words are exactly the walks from zero staying nonnegative.

Let $P_{m,d}$ record the sum of parts for words with $d$ downs. Appending a final step increases every old part by one. A final down also contributes a new part of size one. In both cases the total increment equals the new number $d$ of downs. Hence
$$P_{m,d}=q^d(P_{m-1,d}+P_{m-1,d-1}),\qquad 0\le d\le\lfloor m/2\rfloor.$$
Start at $P_{0,0}=1$, use zero outside the admissible range, and sum over $d$ to obtain the rank polynomial.

```sh
python3 verify.py --max-n 128 --direct-n 12
```

All 256 rank sequences pass the weak unimodality test. The script checks every coefficient against recursive enumeration of the actual parts for $1\le n\le12$, verifies each total against $\binom{m}{n}$, and detects the published valley $17,16,17$ at ranks 16–18 of $(9,7,5,3)$. At $n=128$ the unique peaks are at rank 14993 of 16384 and rank 15110 of 16512, respectively. The calculation uses arbitrary-precision integers. Add `--verbose` for the peak ranks and sizes of every shape. These are finite checks.
