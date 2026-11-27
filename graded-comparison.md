# A range of Catalan characters at every endpoint

Write $P_{d,e}(q,t)$ for the trapezoidal path polynomial at a fixed endpoint, with the endpoint shift removed. Its words have $d$ nonnegative entries, $g_1\le e$ and $g_{j+1}\le g_j+1$. The $q$ exponent is their sum. The $t$ exponent is $\sum_j(e-g_j)_++\#\{i<j:g_i-g_j\in\{0,1\}\}$. Put $C_N=P_{N,0}$, the ordinary area–dinv Catalan polynomial. These are Loehr's path statistics as used in the [staircase refinement](trapezoid-refinement.md). [Loehr](https://doi.org/10.1016/S0196-8858(03)00028-9) · [Loehr and Warrington, §2.5](https://arxiv.org/pdf/0705.4608#page=11)

Let $c=\binom{e+1}{3}$, $N=d+\binom{e+1}{2}$ and $h=\max\{i:\binom{i+1}{2}\le N\}$. Then $h\ge e$. The comparison is coefficientwise.
$$ (qt)^c P_{d,e}(q,t)\ \le\ C_N(q,t). \tag{1} $$
If $S$ is the least total degree of $C_N$, there is equality in **every bidegree of total degree at most $S+h-e$**. For example, at $(d,e)=(3,2)$ this proves equality through shifted total degree nine. In degree ten, $[q^3t^7]C_6=2$ and $[q^3t^7](qt)P_{3,2}=1$.

## Insertion at a prescribed height

Fix the multiplicities $N_i$ of the heights in a word. Begin with $N_0$ zeros and insert the $N_i$ copies of $i$ in increasing order of $i$. A run of $i$ can follow any occurrence of $i-1$. It may also begin the word when $i\le e$. Erasing the highest letters recovers the preceding word uniquely. If an insertion follows the $j$th copy of $i-1$ it contributes $N_{i-1}-j$ extra inversions, and an initial insertion contributes $N_{i-1}$. At this stage the available costs are exactly $0,1,\ldots,w_i$, where $w_i=N_{i-1}-1+\mathbf 1_{i\le e}$. An allocation of the copies to these slots is a partition in an $N_i$ by $w_i$ rectangle, weighted by its size.

Consequently the contribution is a monomial with exponents
$$ X=\sum_i iN_i,\qquad Y=\sum_i\left((e-i)_+N_i+\binom{N_i}{2}\right) $$
times the product, for $i\ge1$, of Gaussian binomials counting the rectangles just described. A factor with $N_i=0$ is one. If $N_i>0$ and there is no slot, the contribution is zero. Equivalently $(X,Y)$ is the sum of the coordinates of the $d$ cells stacked in column $i$ starting at row $(e-i)_+$.

To pass to an ordinary word add $(e-i)_+$ letters in every column $i$. The new cells fill the triangle $i+j<e$ below the old cells, which adds $c$ to each exponent. For $1\le i<e$ the two rectangle dimensions increase by the same amount $e-i$. At $i=e\ge1$ the extra copy of $e-1$ replaces the initial slot, leaving the rectangle identical. The remaining rectangles agree. Keeping each partition in its larger rectangle gives an injection preserving both shifted statistics. The original multiplicities can be recovered from the new ones. This proves (1).

## When every ordinary word in a degree is reached

The cheapest $N$ lattice sites for the cost $i+j$ fill all diagonals below $h$ and part of diagonal $h$. They form an admissible ordinary profile with zero extra inversions, so their total cost is $S$. In any ordinary profile let $a$ be the cost of its cells minus $S$. If a site of cost $v<h$ is missing, then $a\ge h-v$. Indeed it can be exchanged for an occupied site of cost at least $h$, after which the cost is still at least $S$.

Consider total degree $S+a+b$ with $b$ the sum of the sizes of the insertion partitions and $a+b\le h-e$. All sites below diagonal $h-a$ are present. In particular the triangle below $e$ is present, so subtract it to recover nonnegative $N_i$. For $0\le i<e$ there are at least $h-a-e\ge b$ surviving sites in column $i$, one on each diagonal $e,\ldots,h-a-1$. Each reduced rectangle at $1\le i<e$ thus has both dimensions at least $b$ and accommodates its insertion partition. The other rectangles agree. This inverts the injection for every such word, proving the degree assertion.

The area–dinv polynomial $C_N$ is the character in its two grading variables of the alternating diagonal coinvariants. Linear substitutions on the two sets of variables commute with the symmetric group and preserve the invariant ideal, so every homogeneous component is a polynomial $GL_2$ character. Its weight multiplicities are symmetric and increase weakly to the middle by the irreducible characters of $GL_2$. Equation (1) transfers this property to every degree in the equality range. [Haiman, character of the alternating diagonal coinvariants](https://math.berkeley.edu/~mhaiman/ftp/vanishing/van.pdf) · [Garsia and Haglund, Catalan path formula](https://www.sciencedirect.com/science/article/pii/S0012365X02003436) · [Xin and Zhang, ordinary area–dinv interpretation](https://arxiv.org/abs/2011.04927)

For the whole staircase put $m=2n+\delta$, $\ell=n+\delta$ and $h_0=\max\{i:\binom{i+1}{2}\le\ell\}$. Let $S_0$ be the minimum total degree in $B_m(q,t)$, the sum of the $\ell$ cheapest costs $i+j$. **Every component in degrees $S_0$ through $S_0+h_0-\delta$ has nonnegative Schur coefficients in $q,t$.** Indeed at endpoint $e=2u+\delta$, $d=n-u$, the staircase adds the shift $(qt)^A$, $A=u(u+\delta)$. Here $N=\ell+2A$, hence $h\ge h_0$. The minimum endpoint contributes an entire ordinary Catalan polynomial. For $u\ge1$, the least degree of its shifted summand is at least $S_0+u(u+1)$ by the [cell comparison](trapezoid-refinement.md#the-lower-boundary-of-the-support). Within the stated global range the excess above that summand's minimum is at most
$$ h_0-\delta-u(u+1)\le h_0-\delta-2u\le h-e.$$
The component is therefore a shift of an ordinary Catalan component. Symmetric shifts preserve unimodality of weights, and all summands of the same total degree have the same center. Equivalently the Schur expansion stays nonnegative after the shift. Even a negative determinant twist in this comparison leaves a polynomial character, since the resulting component equals a polynomial supported on nonnegative exponents.

## An additional character when the first diagonal has room

For $1\le d\le e+1$ the least degree of $P_{d,e}$ is $ed$. Its degree-$ed+1$ component is also a $GL_2$ character. For $d=1$ that component is zero. For $d\ge2$ put $r=d-1$ and $V_j=\mathrm{Sym}^j(\mathbb C^2)$. A module with precisely this character is the quotient of
$$
 \bigwedge^r V_e\otimes V_{e+1}
 \quad\text{by the image of}\quad
 (\det)^r\otimes\bigwedge^r V_{e-1}\otimes V_{e+1-r}.
 \tag{2}
$$
To embed the second space, take polynomial slots $z_1,\ldots,z_r$ and a distinguished slot $z_0$, each a pair of variables, and alternate the first $r$ slots. Multiply by $\prod_{i=1}^r\det(z_i,z_0)$. The product is symmetric under permutations of the alternating slots. Its degrees and determinant weight give exactly (2), and multiplication is injective.

Because the degree is fixed, it suffices to keep the exponent of $q$. A configuration with cost $ed+1$ and zero extra inversions has $r$ sites on diagonal $e$ with abscissas $U\subset\{0,\ldots,e\}$. The site on diagonal $e+1$ has abscissa in $U$, or it is $e+1$ and $e\in U$. The latter condition permits the step from $e$ to $e+1$. All these profiles admit exactly one word with zero extra inversions by the insertion formula. A configuration of cost $ed$ with one extra inversion has $d$ distinct sites on diagonal $e$. Its insertion factor contributes one for each adjacent pair $i,i+1$ of occupied sites. Removing $i+1$ from the pair leaves a set $U$ containing $i$ with $i+1\notin U$. Thus the character counts each pair $(U,j)$ with $|U|=r$ and $j\in U\cup(U+1)$ once, at exponent $\sum U+j$.

All pairs with $0\le j\le e+1$ form the target character of (2). To count the complement, put $E_b^a=\sum_{U\subset\{0,\ldots,a-1\},\ |U|=b}q^{\sum U}$ and $[l]=1+q+\cdots+q^{l-1}$, with $[0]=0$. When $j=0$ or $e+1$, the complement contributes $(q^r+q^{e+1})E_r^e$. For $1\le j\le e$ the complement excludes $j-1,j$ from $U$. Leave elements below $j-1$ fixed, lower those above $j$ by one and insert the marked element $j-1$. This gives an $(r+1)$-subset of $\{0,\ldots,e-1\}$ with any one element marked. If $s$ elements precede the mark, the original exponent exceeds the new sum by $1+r-s$. The interior complement consequently contributes $q[r+1]E_{r+1}^e$. The Gaussian identity $[r+1]E_{r+1}^e=q^r[e-r]E_r^e$ makes the entire complement $q^r[e+2-r]E_r^e$, exactly the source character at $t=1$. Both sides are homogeneous of the same total degree, proving (2).

Thus the lowest two total degrees are Schur-positive at **every fixed endpoint**. When $d\ge e+1$, $h-e\ge1$ already gives the second degree. The empty word has only its constant component. For fixed $e$ the number of proved consecutive degrees grows with $d$. The univariate rank differences also receive contributions from higher components, whose Schur expansions are unresolved in general.

## Other exposed lower faces

Fix positive coprime weights $p,v$. For $d>0$ take the $d$ cheapest sites for $pi+vj$ in $i,j\ge0$, $i+j\ge e$. Every choice among the tied sites at the cutoff gives exactly one word at minimum cost. The chosen sites fill columns from their lowest eligible row. If a column $i>e$ occurs, columns $e,\ldots,i-1$ have strictly cheaper bottom sites and are present. Thus any occupied column above $e$ has its insertion slot. For $i\le e$ the initial slot is available. The constant coefficient of the insertion product is one. Conversely equality forces cheapest cells and zero extra inversions since $v>0$.

The tied sites form a consecutive segment with step $(v,-p)$, indexed $0,\ldots,b-1$. If $r$ of them are required, the entire exposed face is a monomial times the Gaussian binomial $\binom{b}{r}_{q^v/t^p}$ by the subset-sum formula. In particular it is unimodal along its primitive lattice direction. When $d=0$ the face is a point. This also applies to the whole staircase's exposed lower face, since the [positive coordinate margins](trapezoid-refinement.md#the-lower-boundary-of-the-support) exclude every nonminimum endpoint at a positive supporting weight.

~~~sh
python3 -B verify_graded_comparison.py
python3 -B verify_trapezoids.py
~~~

The first command checks the insertion product against independent height-word enumeration in 40 endpoint classes. It checks 520 exposed faces and 77 instances of (2) or its one-letter case by direct word enumeration in both families through $n=10$. Where $N\le13$ it also checks (1) throughout both polynomials and every coefficient of the asserted equality range. It compares the whole staircase's bottom range with its predicted sum of Catalan components. The second command independently checks specialization to the directly enumerated strict-partition ranks.
