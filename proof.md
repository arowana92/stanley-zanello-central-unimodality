# The two central staircase families

**Theorem (computer-assisted).** For every integer $n\ge1$, let $\lambda$ be either $(2n-1,2n-3,\ldots,1)$ or $(2n,2n-2,\ldots,2)$. Let $a_j$ count the strict partitions of $j$ contained in $\lambda$, including the empty partition at $j=0$. The sequence $a_0,\ldots,a_{|\lambda|}$ is weakly unimodal.

This is Conjecture 3.4 in Stanley and Zanello's MIT version and Conjecture 3.3 in the journal numbering. This computer-assisted research proof was developed in this checkout and awaits independent review. The [literature review](README.md#literature-check) records the primary sources and later citations examined. [Stanley and Zanello, §3](https://math.mit.edu/~rstan/papers/distinctparts.pdf#page=8) · [Journal article](https://doi.org/10.1016/j.ejc.2015.03.007)

## Proof

Put $D=|\lambda|$. Reverse the coefficients to corank $k=D-j$, and write $b_k=a_{|\lambda|-k}$. Reversal preserves weak unimodality. Let $B_n,O_n$ be the polynomials with coefficients $b_k$ in the odd-part and even-part staircases, with ballot lengths $m=2n,2n+1$, respectively. These names refer to the bounding staircase. A contained partition may use parts of either parity. For the ordinary Dyck area polynomial $C_l$,
$$
 B_n=C_n+\sum_{h=0}^{n-1}q^{2h+1}B_h C_{n-h},
 \qquad O_n=\sum_{h=0}^{n}q^h B_h C_{n-h}.
$$
The first identity is Stump’s type $B$ area recurrence. Cutting at the last zero gives the second identity. Both use $C_0=B_0=1$. [Bijection and derivation](README.md#catalan-recurrences-for-the-two-families) · [Stump, Theorem 3.1](https://arxiv.org/pdf/0808.2822#page=9)

Consider sizes in increasing order, taking $B_n$ before $O_n$. Thus every odd-part row on the right has already been treated, including $B_n$ when proving the assertion for $O_n$. Three ingredients give the induction step.

1. **Before the central interval.** If $B_h$ is unimodal then its coefficients satisfy
   $$
   b_i\le b_j\quad\text{for }i<j,\qquad i+j\le .524(2h)^{3/2}-3h-1 .
   $$
   This follows by testing its interval superlevel sets with two polynomials of degrees 20 and 6. Their expectations have certified negative signs by the exact area moments. Each $C_l$ is a sum of interval polynomials with endpoint sums at least $(2\sqrt2/3)l^{3/2}-l$, by the type $A$ diagonal coinvariant theorem and the degrees of alternating monomials. A decreasing step in $q^\sigma B_h(q)(q^u+\cdots+q^v)$ would require $b_{k-\sigma-v}>b_{k+1-\sigma-u}$ in $B_h$. Combining the two endpoint bounds over $h$ rules this out for $2k+1\le M n^{3/2}-n-1$, with $M=(9/8+1/(8\cdot .524^2))^{-1/2}$. The isolated $C_n$ is also nondecreasing over these steps. In particular the corank sequence is nondecreasing up to the start indicated in the table below. [Moment proof, induction and certificate](moment-comparisons.md) · [Type A character argument and attribution](excursion-centers.md#ordinary-excursions-and-two-variable-characters)

2. **The central interval.** Write $s=m^{3/2}$. Its complete range is covered by the following arguments.

   | Staircase size | Central coefficient assertion | Evidence |
   | --- | --- | --- |
   | $1\le n\le63$ | The complete row is unimodal. | [Exact integer recurrence](verify.py) |
   | $64\le n\le2048$ | Strict log-concavity from $\lfloor .1s\rfloor$ through the midpoint $\lfloor D/2\rfloor$ for $m<770$, and through the join at $1.5s$ or the midpoint for $m\ge770$. | [Positive ballot recurrence and roundoff proof](certified-window.md#a-shorter-base-case-for-induction) |
   | $2049\le n<300000$ | The sequence on $[\lfloor .1366s\rfloor,\lceil .6s\rceil]$ is unimodal. | [Sampled Fourier proof and error bounds](fourier-window.md) |
   | $n\ge300000$ | The sequence from $\lceil .1375s\rceil$ onward is unimodal. The initial increase in step 1 extends past this index, since its cutoff at $n\ge4096$ is $.1378s$. | [Uniform last-return estimates and peak interval](size-descent.md#lattice-estimates-at-the-three-cutoffs) |

   In the finite Fourier calculation, the signed area of a strict ballot walk has conditional law $\pm(k+d)$ for an explicit shift $d$. At fixed frequency its convolution with the bridge transform is the free-walk transform. The inverse convolution has absolute sum at most two, so a checked residual bounds the error at every length. Sampled inversion with the alias and frequency tails bounded gives strict increase on one side, strict decrease on the other and strictly decreasing forward differences through their join. The calculation includes both possible parities of the signed walk at every $2049\le N\le300000$. These correspond to $N=n$ for $B_n$ and $N=n+1$ for $O_n$.

   For unbounded $n$ the comparison is analytic and uniform. A gamma average implements the exact last-return convolution for the continuum meander and excursion transforms. Bounding its discrete residual on time bins, inverting by the first-return law and controlling the omitted Fourier frequencies give errors below $.121$ and $13.6$ in the first and centered second differences in lattice units. The cubic Airy integral gives the positive derivative on the left. Strong log-concavity gives negative curvature near the limiting mode and a negative derivative farther to the right. The margins dominate the lattice errors. The proof of the peak interval specifies the signs and bounds at the joins. [Convolution identities](return-expansion.md#gamma-averaging-and-the-first-correction) · [Localized inverse bounds](localized-returns.md) · [Derivative and curvature margins](size-descent.md#from-density-to-signs-and-comparisons)

3. **After the central interval.** For $m\ge4096$ the marked first-hit estimate gives $b_{k-1}>b_k$ when $.6s\le k\le D/2$, $D=|\lambda|$. For $770\le m<4096$ the first-passage estimate supplies this sign from $1.5s$. In the remaining upper-half portion at smaller lengths the finite determinant calculation extends through the midpoint. For ranks $i\le j\le D-i$, Björner and Ekedahl's parabolic Bruhat interval inequality gives $a_i\le a_j$. This supplies weak decrease in corank beyond the midpoint in every size. [Marked first-hit proof](marked-hits.md#signs-and-reproduction) · [First-passage proof](rising-window.md) · [Application of Björner and Ekedahl](monotonicity.md#1-lower-half-for-all-sizes)

There is also an elementary proof of the last step beyond the midpoint within this induction. For an earlier unimodal odd-part row $B_h$, pairing coranks $i$ and $p-i$ through a peak $p$ gives $p\le2\mathbb E[K]$. The exact first moment and the elementary middle-binomial bound imply $2p+4h+2\le h^2$ for $h\ge49$. In a summand $q^s B_h C_l$, all coefficients are therefore nonincreasing from $s+p+\binom l2$ onward, since each term is already on the decreasing side of $B_h$. This threshold is at most $\lfloor n^2/2\rfloor$ when $n=h+l\ge96$ and $s\le2h+1$. For $h<49$ the same estimate follows from $p\le h^2$ and $l\ge48$. The isolated $C_n$ vanishes beyond $\binom n2$. This supplies the lower-half comparisons needed in the induction for both families. The checked base covers the smaller sizes. [First moment](CentralUnimodality/OddMean.lean) · [Convolution estimate](CentralUnimodality/MidpointTail.lean) · [Induction](CentralUnimodality/MidpointInduction.lean)

The nondecreasing prefix and nonincreasing suffix meet the unimodal central interval in the indicated order, so the whole corank row is unimodal. This proves the induction step for both families and every $n$. No type $B$ diagonal coinvariant identification is assumed.

A second computer-assisted proof gives the central peak for every $n\ge150000$ in both families. It bounds the signed first-return transform after pinning its terminal height. The resulting late-return weights and a separate bound on the upper retained frequencies give positive margins for all three spatial sign tests. [Direct peak derivation](localized-returns.md#a-direct-polynomial-peak-certificate-from-150000) · [Independent rational verifier](verify_direct_peak.py)

Retaining the signed quadratic correction gives the central peak for every $n\ge10000$ in both families. The retained first- and second-order errors are below $0.123827$ and $27.478759$. Lean checks the quadratic split identity and its cubic remainder. The end-to-end Lean peak theorem starts at 150,000 rows. [Quadratic peak proof and reproduction](quadratic-peak.md)

## Reproducing the checks

The standard-library Python scripts check rational inequalities in the proofs. The C++17 programs use binary64 round-to-nearest and signed and unsigned 128-bit integers. Keep compiler optimizations compatible with the stated error bounds.

~~~sh
python3 -B verify.py --max-n 64 --direct-n 12 --upper-curvature
python3 -B verify_moment_comparisons.py
python3 -B verify_rising.py
python3 -B verify_hit_tilts.py
python3 -B verify_marked_hits.py
python3 -B verify_return_expansion.py
python3 -B verify_return_bounds.py
python3 -B verify_local_returns.py
python3 -B verify_cubic_tilt.py
python3 -B verify_size_descent.py
python3 -B verify_fourier_grid.py
clang++ -std=c++17 -O3 -fno-fast-math -ffp-contract=off verify_window.cpp -o /tmp/sz_window
/tmp/sz_window --central 2048
clang++ -std=c++17 -O3 -fno-fast-math -ffp-contract=off verify_fourier_window.cpp -o /tmp/sz_fourier_window
/tmp/sz_fourier_window --self-test
/tmp/sz_fourier_window 2049 300000
~~~

The final command requests the full range. To reproduce the recorded margins exactly, use the [seven invocations](fourier-window.md#reproduction) in the certificate.

The small-shape check recursively enumerates the actual decreasing lists of parts. All coefficients of the 24 shapes through $n=12$ agree with the ballot and Catalan recurrences. The Fourier self-test checks signed transform values from the new solver and performs full discrete inversion of the directly enumerated rows. The adjacent-ratio certificate checks 610,906,915 strict inequalities over the stated small-size windows. All seven finite Fourier runs passed in both parities. Across their full length range, the lower bounds on the left, middle and right sign margins were .0788, 101.1 and .929, respectively, in the scaled difference units of the certificate.
