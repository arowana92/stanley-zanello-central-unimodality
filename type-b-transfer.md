# Reducing the even-part conjecture to the odd-part conjecture

**Theorem.** If the even-part staircase with $n\ge 10^6$ rows fails unimodality, an odd-part staircase with $n/8<h\le n$ rows also fails unimodality. The two failures can occur at different coranks. In particular one can settle both families above one million rows by proving just the odd-part conjecture for $h>125000$. No type $B$ diagonal coinvariant conjecture is assumed in this implication.

We also prove an unconditional improvement for each family. Write $m=2n$ for the odd-part staircase and $m=2n+1$ for the even-part staircase, $s=m^{3/2}$, and $b_k$ for the number of diagrams missing $k$ cells. From $\lceil .14s\rceil$ onward the sequence is unimodal and contains every global maximum at $n\ge750000$. The starting point improves to $\lceil .135s\rceil$ at $n\ge10^6$. There are at most two maximizers, consecutive in case of a tie. [Peak bounds](#locating-the-peak) · [Rational certificates](verify_type_b_transfer.py)

## Area polynomials and intervals

Let $B_h$ and $O_n$ be the odd-part and even-part corank polynomials, respectively, and $C_l$ the ordinary Dyck area polynomial of semilength $l$. Each empty case is 1. Splitting a walk at its last zero gives
$$ O_n(q)=\sum_{h=0}^n q^h B_h(q)C_{n-h}(q). \tag{1} $$
The prefix is a Dyck excursion. After the next up-step the remaining walk has length $2h$, and translating it up one adds $h$ to its corank. Stump's type $B$ area polynomial is $B_h$. [Last-zero decomposition and Stump recurrence](README.md#catalan-recurrences-for-the-two-families) · [Stump, Theorem 3.1](https://arxiv.org/pdf/0808.2822#page=9)

For a nonnegative integer polynomial $P$, say it satisfies the comparison at integer $T\ge0$ if
$$ [q^i]P\ \le\ [q^j]P\qquad(0\le i<j,\quad i+j\le T). \tag{2} $$
Extend the coefficients by zero outside the support. This is equivalent to writing $P$ as a sum of intervals $q^a+\cdots+q^b$ with $a+b\ge T$. Indeed, for each positive integer level, take the consecutive components of the set where the coefficients reach that level. If a component $[a,b]$ has $a+b<T$, the indices $a,b+1$ contradict (2). Conversely each interval with $a+b\ge T$ satisfies (2). Endpoint sums add under products of intervals, by the identity $(1+\cdots+q^d)(1+\cdots+q^e)=\sum_{v=0}^{\min(d,e)}q^v(1+\cdots+q^{d+e-2v})$.

Let $D_A(l)$ be the sum of the $l$ cheapest monomials $x^a y^b$ by total degree, counting each pair once. Let $D_B(h)$ be the corresponding sum for $h$ distinct monomials of **odd** total degree. The type $A$ diagonal coinvariant theorem gives an interval decomposition for every $C_l$ with endpoint sums at least $D_A(l)$. Briefly, the alternating part of the diagonal coinvariant ring in each total degree is a polynomial $GL_2$-module. Each irreducible specializes at $(q,1)$ to an interval whose endpoints sum to that degree. A nonzero alternant needs $l$ distinct monomials, and the ordinary area specialization is known. [Degree bound and type $A$ attribution](excursion-centers.md#ordinary-excursions-and-two-variable-characters)

Define
$$ D_{\rm mix}(n)=\min_{0\le h\le n}\big(2h+D_B(h)+D_A(n-h)\big). $$
It equals the sum of the $n$ cheapest entries of the union of the ordinary degree multiset and the odd degree multiset shifted up by two. This follows by fixing how many entries come from each multiset. If all $B_h$ satisfy (2) at $D_B(h)$, (1) therefore gives (2) for $O_n$ at $D_{\rm mix}(n)$.

The counts of ordinary, odd and mixed costs through an integer $t\ge0$ are bounded by $(t+2)^2/2,\ (t+2)^2/4,\ 3(t+2)^2/4$, respectively. For the first the exact count is $(t+1)(t+2)/2$. For the second, the first $r$ odd degrees through $2r-1$ have $r(r+1)$ entries. For the third, add the first bound to the second with the shift. Inverting each upper bound and summing the resulting lower bounds for the ordered entries, using $\sum_{j=1}^n\sqrt j\ge 2n^{3/2}/3$, gives
$$
 D_A(l)\ge(2\sqrt2/3)l^{3/2}-2l,\qquad
 D_B(h)\ge(4/3)h^{3/2}-2h,\qquad
 D_{\rm mix}(n)\ge\frac4{3\sqrt3}n^{3/2}-2n. \tag{3}
$$
The mixed counting function is $3t^2/4+O(t)$. In the even-part scaling the limiting value of $D_{\rm mix}(n)/(2s)$ is $1/(3\sqrt6)=.136082\ldots$. This explains the precision needed at the left end of the peak interval.

## Locating the peak

Use the half Brownian meander area density $F$, its mode $x_*$, and the Airy ground energy $a\in(2.337,2.339)$ from the [cubic contour formula, (1)–(2)](cubic-tilt.md#a-cubic-contour-for-the-derivative). The ground eigenfunction $f$ is positive on $(0,\infty)$ with $f(0)=0$, $f'(0)=1$, and $f''=(x-a)f$. Its integral $c_1$ satisfies
$$ 1.57<c_1<2.04. $$
Indeed, enclose the Taylor coefficients through degree 42 by $d_0=0,d_1=1$, $j(j-1)d_j=d_{j-3}-a d_{j-2}$ with $d_{-1}=0$. If $M$ bounds $3^j|d_j|$ for $40\le j\le42$, the next block of three is bounded by $M/2$, since $(27+9a)/(43\cdot42)<1/2$. Induction gives an absolute tail at most $3M$ on $[0,3]$. Termwise integration costs at most $9M$ in the tail. Beyond 3 one has $f(x)\le f(3)\exp[-\sqrt{3-a}(x-3)]$. This follows by the maximum principle for $-\partial_x^2+(3-a)$, since $f$ is a subsolution and both functions decay. The verifier integrates the interval coefficients and adds $f(3)/\sqrt{3-a}$ for the upper bound.

With $r=a/(3x)$, the derivative in the cubic contour formula has prefactor $3c_1r^6e^{-ar^2/6}/(2\sqrt a)$. The Gaussian moment bound for its normalized integral uses $A\ge 2.337^3/(18x_{\rm right}^2)$ on each interval. Subtract the already certified $.01$ for the higher Airy energies. The radial factor decreases with $r$ throughout $x\le1/4$. Evaluating its lower bound at the left endpoint and the Gaussian bound at the right gives

| Range of $x$ | Lower bound on $F'(x)$ |
| --- | ---: |
| $[.135,.145]$ | $.105$ |
| $[.14,.145]$ | $.18$ |
| $[.145,.25]$ | $.18$ |

For the lattice comparison write $2N=m$ or $m+1$, $s_0=(2N)^{3/2}$, $d=(m+1+\lceil m/2\rceil)/2$ and $z_k=(k+d)/s_0$. On $k\le.6s$ one has $z_k\ge k/s$ at the sizes here. For odd $m$ use $(1+1/m)^{3/2}\le1+2/m$ and $d\ge m/2\ge1.2\sqrt m$. Also $z_k\le k/s+(m+1)/s$. The [localized return bounds](localized-returns.md) give density, forward difference and centered second difference errors below $(.0045,.147,10.3)$ at $N\ge750000$ and $(.0033,.101,6.1)$ at $N\ge10^6$. The derivative bounds give strict increase from the stated starting points up to $z_k=.25$. For the rest use the [peak-interval argument](cubic-tilt.md#the-peak-interval). Its flank bounds $F'>.30$ and $-F'>.20$, and its middle curvature bound $F''<-15.5$, all exceed the required errors in magnitude. For $k<.145s$ the density loss from the continuum maximum exceeds $.10$, and rounding the mode costs less than $.001$. This excludes all global maxima there since $.10>.001+2(.0045)$. The all-size right-tail sign bounds finish the suffix.

## A descent in the even-part row

Suppose $n\ge10^6$ and $O_n$ fails unimodality. By the preceding result there must be some $0\le k<\lceil .135s\rceil$ with $[q^{k+1}]O_n<[q^k]O_n$. In (1), decompose each $C_{n-h}$ into the type $A$ intervals $[u,v]$. The coefficient difference of $q^hB_h(q)(q^u+\cdots+q^v)$ telescopes to $[q^{k+1-h-u}]B_h-[q^{k-h-v}]B_h$. Some difference is negative. For that summand set $i=k-h-v$ and $j=k+1-h-u$. Then $0\le i<j$, and
$$ i+j=2k+1-2h-u-v\le 2k+1-2h-D_A(n-h)\le D_B(h). \tag{4} $$
For the last inequality use $2k+1<2(.135)s+1<D_{\rm mix}(n)$ by (3). Moreover $h>n/8$. Otherwise $D_A(n-h)\ge(2\sqrt2/3)(7n/8)^{3/2}-2n>2(.135)s+1$, contrary to $i+j\ge0$. Both numerical comparisons follow on dividing by $n^{3/2}$ and taking $n=10^6$, the worst endpoint. Thus we have found a failed reflected comparison in an odd-part row with $h>125000$.

## From a failed comparison to an odd-part valley

**Lemma.** If $h\ge125000$ and $B_h$ is unimodal, it satisfies (2) at $D_B(h)$.

Write $s=(2h)^{3/2}$ and $z_i=(i+(3h+1)/2)/s$ for this odd-part row. The $j$th odd degree is at most $2\sqrt j$, since degree $2r+1$ starts at entry $r(r+1)+1$. Consequently $D_B(h)\le4h^{3/2}/3+2\sqrt h$ by an integral upper bound. For any pair under consideration this gives
$$ z_i+z_j\le(D_B(h)+3h+1)/s<.475,\qquad z_i<.238. $$
All the sites used below are in the row, since its degree is $h^2$ and the largest scaled site is at most $.65+1/s$. There exists $t\ge j$ with $b_t>b_i$. To prove this, choose the first grid site at or to the right of $\max(z_j,x_*)$.

For $0<x\le.238$, the cubic contour formula gives $F(x)<1.25$, and for $x\le.186$ it gives $F(x)<.18$. Use $c_1<2.04$, the same absolute excited-state error $.01$, and bound the absolute ground Gaussian integral by $\mathbb E(1+V^2)^3$ for $\operatorname{Var} V=1/(2A)$. The radial factor $r^3e^{-ar^2/6}$ is decreasing with $r$ in this range, so it suffices to check the two right endpoints.

The [Gaussian regression inequality](airy-overlap.md#the-decreasing-side-in-corank) gives $F(z_t)\ge F(x_*)e^{-6(z_t^2-x_*^2)}$, with $F(x_*)\ge1.78$ and $.25<x_*\le.65$. Rounding up adds at most $.0001$ to the squared argument. If $z_j\le.29$, then
$$ F(z_t)\ge 1.78 e^{-6(.29^2-.25^2+.0001)}>1.25+2(.069). $$
Here the expression also bounds the loss when $z_j<x_*$. If $z_j>.29$, then $z_i<.185$, and the same lower bound with $.475$ replacing $.29$ exceeds $.18+2(.069)$. At $N=h\ge125000$ the [order-zero return estimate](localized-returns.md#the-density-at-125000-pairs) has error less than $.069$ at each site. Thus $b_t>b_i$ in both cases. Unimodality gives $b_j\ge\min(b_i,b_t)=b_i$ for $i<j\le t$, proving the lemma. Applying its contrapositive to (4) completes the theorem.

## The type B diagonal coinvariant route

There is also a conjectural source of (2) at **all** odd row counts. Let $W$ be the group of signed permutations on $h$ pairs of variables in $S=\mathbb C[x_1,y_1,\ldots,x_h,y_h]$. Let $M=S^{\det}/(S^W_+ S^{\det})$, the determinant component of the diagonal coinvariants. Equivalently, if $I=S S^{\det}$ and $\mathfrak m$ is the homogeneous maximal ideal, this is $I/\mathfrak m I$. Alternants span the latter quotient. Applying the determinant projection to a positive-degree multiple of an alternant averages the multiplier to a positive-degree invariant, proving the equality of relations.

**Proved degree bound.** No total degree below $D_B(h)$ occurs in $M$, and its lowest component is exactly the following character. Write $h=k(k+1)+r$ with $0\le r<2k+2$, and $L=\sum_{\nu=1}^k\nu(2\nu-1)$. Then it is
$$ (qt)^L\sum_{\substack{J\subseteq\{0,\ldots,2k+1\}\\ |J|=r}}
             q^{\sum J}t^{r(2k+1)-\sum J}. $$
Indeed, changing the sign of a pair forces its monomial to have odd degree. Antisymmetrizing over the pairs then requires distinct monomials. Their determinants form a basis of the alternating polynomials, by disjoint monomial orbits. At the least total degree both the full lower degrees and the choice of $r$ cells at the next degree survive, because any invariant relation would need an alternating multiplier in lower degree. Simultaneous $GL_2$ substitutions in the pairs descend to the quotient. As in type $A$, its $(q,1)$ character therefore satisfies (2) at $D_B(h)$.

**Missing identity.** Identifying this character with $B_h(q)$ for every $h$ is Stump's proposed type $B$ area specialization. Under that identity (2) and (3) give the required increase of $B_n$ and $O_n$ up to $\lceil .135s\rceil$ whenever $n\ge10^6$. The argument above proves the even-to-odd reduction without that identity. Neither implication settles the odd-part conjecture. Oblomkov's asymptotic theorem is for sufficiently large powers at fixed group rank. The first power and its path interpretation are discussed as open questions. [Lu, Conjecture 1.17](https://www2.math.upenn.edu/~jhaglund/thesis/Lingxi.pdf) · [Oblomkov, Questions 9.8–9.9](https://arxiv.org/html/2609.11691v1#S9)

Lu's path area at bases $b=1,2$ gives precisely $B_n,O_n$. Reverse the path from $(n,n)$, interpreting west as up and south as down. Its length is $2n+b-1$ and its nonnegative height is $y-x$. In strip $y\le Y\le y+1$, $0\le y<n$, the full region has $b+2y$ counted cells, including the antidiagonal half-cell and omitting the diagonal half-cell. Strips below the path's starting height are full. At a north step from $(x,y)$ the occupied area in that strip is $y-x$. The missing $b+y+x$ is exactly the down-step's part label in the reversed word, at time $2n-x-y$. Summing gives corank area. Thus the even-part family corresponds to base two. Lu's opposite-degree specialization at $(q,q^{-1})$ measures a different statistic. [Lu, Definitions 1.16 and 2.2, Assumptions 2.3–2.4](https://www2.math.upenn.edu/~jhaglund/thesis/Lingxi.pdf)

## Independent finite checks

The verifier builds $M$ in both degrees over $\mathbb Q$ for $h=1,2,3,4$. The dimensions are $2,6,20,70$ and every $(q,1)$ coefficient equals the corank count from direct enumeration of strict partitions. To reproduce the quotient calculation, first truncate each coordinate exponent at $2h$. The invariants elementary in the $x_i^2$ imply $x_i^{2h}=0$ by evaluating $\prod_j(u-x_j^2)$ at $u=x_i^2$. The same holds for $y$. This truncation preserves the final quotient. In the truncated algebra take the determinant basis of sets of $h$ distinct odd monomials. The invariant ring before truncation is generated by the sums $\sum_i x_i^a y_i^b$ for positive even $a+b$. Indeed orbit sums have even degree at each occupied index, and multiplying power sums gives the distinct-index orbit sum up to multiplicity and terms with fewer occupied indices. Induction gives generation in characteristic zero. Each generator acts by adding $(a,b)$ to one cell of the determinant, with the sorting sign. Fraction-free elimination in each bidegree computes the joint image of these multiplication maps.

Both row comparisons, at $D_B(n)$ and $D_{\rm mix}(n)$ respectively, pass for $1\le n\le96$. Direct enumeration of the actual parts agrees coefficient by coefficient through $n=12$. The verifier also checks (1) and both first-return recurrences through $n=32$. For those recurrences, write $B(z),O(z),C(z)$ for the ordinary generating series in the row count. Last returns give $O=C B(qz)$ and $B=C(1+qz O(qz))$, while $1-C^{-1}=zC(qz)$. Consequently $O=B(qz)+zC(qz)O$ and $B=1+qzO(qz)+zC(qz)B$.

~~~sh
python3 -B verify_type_b_transfer.py
python3 -B verify_local_returns.py
python3 -B verify.py --max-n 96 --direct-n 12 --upper-curvature
~~~
