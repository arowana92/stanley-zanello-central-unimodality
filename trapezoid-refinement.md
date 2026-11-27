# A symmetric refinement at fixed endpoint

Let $m=2n+\delta$ with $\delta=0$ for the odd-part staircase and $\delta=1$ for the even-part staircase. Set $\ell=n+\delta$. Both corank polynomials have an explicit symmetric refinement $B_m(q,t)$ by trapezoidal lattice paths. Its coordinatewise minimal bidegrees, including their coefficients, coincide with those of the ordinary $q,t$-Catalan polynomial of semilength $\ell$.

## The two statistics

Fix the endpoint $e=2u+\delta$ of the ballot walk and put $d=n-u$, $A=u(u+\delta)$. Reverse the walk, negating its signs, so it starts at $e$ and ends at zero. Read its successive heights $g_1,\ldots,g_d$ just before an up-step. These are precisely the nonnegative integer vectors with $g_1\le e$, $g_{i+1}\le g_i+1$. The down-steps before each up-step are prescribed by those heights, and the final descent is forced. Include the empty vector for $d=0$.

For the original walk with increments $X_i$ and heights $H_i$, the identity $H_i^2-H_{i-1}^2=2X_i H_i-1$ gives $\sum X_iH_i=(e^2+m)/2$. The $g_i$ are the heights just after its down-steps, in reverse order. Consequently its corank is
$$ K=\sum_i\lfloor H_i/2\rfloor=A+\sum_i g_i . $$
Define a companion statistic
$$ J=A+\sum_{i<j}{\bf1}_{g_i-g_j\in\{0,1\}}+\sum_i(e-g_i)_+,\qquad
 B_m(q,t)=\sum_{\text{ballot walks}} q^K t^J . $$
The two statistics after subtraction of $A$ are the area and diagonal inversion number of Loehr and Warrington's trapezoidal paths of type $(d,e)$. In their §2.5 the outer path in a nest has $e$ prescribed initial north steps, and omitting those steps gives exactly the heights above. Both statistics in the nest acquire the same additive constant. Thus the symmetry of the scalar nested path formula gives $q,t$ symmetry for each fixed endpoint, preserved by the shift $(qt)^A$. The conjectured nested path formula used in that reduction was subsequently proved by Blasiak, Haiman, Morse, Pun and Seelinger. Loehr's earlier trapezoidal path bijection also gives the equidistribution of area and diagonal inversions needed for the tail inequalities below. [Loehr and Warrington, §2.5](https://arxiv.org/pdf/0705.4608#page=11) · [Blasiak et al., Theorem 4.2.2 and §4.3](https://math.berkeley.edu/~mhaiman/ftp/jjag/lw-main.pdf#page=24) · [Loehr, *Trapezoidal lattice paths and multivariate analogues*](https://doi.org/10.1016/S0196-8858(03)00028-9)

In particular $K$ and $J$ on the *same* uniform walk both have the staircase corank distribution. At the minimum endpoint $e=\delta$ the summand equals the ordinary $q,t$-Catalan polynomial of semilength $\ell$. When $e=0$ this is the usual area vector. When $e=1$, prepend a zero to obtain the ordinary vector of length $n+1$. Its additional diagonal inversions count exactly the zero entries of $g$.

## The lower boundary of the support

For a vector $g$, let $N_i$ be its number of entries equal to $i$. Use the $d$ distinct lattice cells
$$ (i,j),\qquad (e-i)_+\le j<(e-i)_++N_i . $$
They all satisfy $i+j\ge e$. The sum of their first coordinates is $K-A$. The sum of their second coordinates is
$$ \sum_i(e-i)_+N_i+\sum_i\binom{N_i}{2}\ \le\ J-A . $$
The excess counts pairs in which a height precedes a height one lower.

For any $p,q>0$ the least value of $pK+qJ$ in this endpoint class is **exactly** $(p+q)A$ plus the sum of the $d$ cheapest costs $pi+qj$ on $i,j\ge0$, $i+j\ge e$. Indeed select cheapest cells from the bottom of each column. The lowest available costs in successive columns are $pi+q(e-i)_+$, decreasing then increasing or everywhere nondecreasing. Their minimum is attained at some $i\le e$. Ties can be resolved to make the occupied columns an interval starting at a height at most $e$ (order tied lowest cells by $i$). Taking the chosen column indices as a nondecreasing vector realizes them with no additional inversions. The empty class of cells at $d=0$ gives the same formula.

At an arbitrary endpoint, supplement its cells with $(r,r)$ for $0\le r<u+\delta$. These lie strictly below $i+j=e$, are disjoint from the first cells and bring the total to $\ell$. The sum in each coordinate of the added cells is $\binom{u+\delta}{2}=A-\binom{u+1}{2}$. Push the cells in every column down to start at zero, then put the columns in decreasing order of length starting at abscissa zero. Neither coordinate sum increases. Reading the resulting column indices in sorted order gives an ordinary Dyck vector of length $\ell$. Its area and diagonal inversions are the two coordinate sums. Thus every bidegree $(K,J)$ dominates an ordinary Catalan bidegree $(a,b)$ with the additional margins
$$ K\ge a+\binom{u+1}{2},\qquad J\ge b+\binom{u+1}{2}. \tag{1} $$
The minimum-endpoint class already contributes the entire ordinary polynomial. Both inequalities have positive margins for $u>0$. This proves the assertion about the minimal bidegrees and their coefficients. It also proves that the minimum of $pK+qJ$ over the full staircase is the sum of the $\ell$ cheapest $pi+qj$ on the full nonnegative lattice. For the minimum-endpoint class this follows from the endpoint formula (when $\delta=1$ the excluded origin has zero cost).

## Exact lowest homogeneous component

Write $\ell=h(h+1)/2+r$ with $0\le r\le h$, and set $c=\binom{h+1}{3}$, $S=2c+hr$. The least total degree in either staircase refinement is $S$. Its entire degree-$S$ component is
$$
 (qt)^c \sum_{\substack{I\subseteq\{0,\ldots,h\}\\ |I|=r}}
     q^{\sum_{i\in I}i}t^{hr-\sum_{i\in I}i}
 = (qt)^{c+\binom r2}\,t^{r(h+1-r)}
       {h+1\brack r}_{q/t}.
$$
In particular its coefficients increase weakly to the middle by Gaussian binomial unimodality. The notation on the right is the ordinary Gaussian binomial evaluated at $q/t$.

Indeed (1) excludes every $u>0$ from degrees $S$ and $S+1$. In the ordinary Dyck class, equality at degree $S$ requires all sites below the line $i+j=h$ and any $r$ of the sites on that line. Each choice is a Ferrers diagram and has a unique height vector attaining equality. To see uniqueness, any descent ending at height $v$ has an earlier occurrence of $v+1$, since the ordinary vector starts at zero and can increase by at most one per step. That occurrence gives an extra inversion beyond the sum of the second coordinates. Thus equality forces the sorted vector of column indices. The full diagonals contribute $c$ in each coordinate and the partial diagonal contributes the subset sum displayed above. More generally, the degree-$S+1$ component also agrees term for term with the ordinary Catalan polynomial, and an endpoint indexed by $u$ first contributes in degree at least $S+u(u+1)$.

## Exact highest homogeneous component at each endpoint

Put $M=ed+\binom d2$. At fixed endpoint the top component is
$$
 (qt)^A\sum_{z=0}^{M} q^z t^{M-z}.
$$
In particular this component supplies one path of each possible area in that endpoint class. The case $d=0$ consists of one empty vector.

To see the bound, consider the $j$th entry $x=g_j$. If $x>e$, its prefix must have visited every height from $e$ to $x-1$. Each such earlier entry $y$ makes a pair with $y-x\notin\{0,1\}$. There are consequently at least $\sum_j(g_j-e)_+$ pairs missing from the ordinary upper bound $\binom d2$ on the pair count. Since $x+(e-x)_+=e+(x-e)_+$, this gives $K+J-2A\le M$. Equality is equivalent to having exactly the indicated number of missing pairs at every entry.

If all entries are at most $e$, equality means that the vector is weakly decreasing with largest and smallest entries differing by at most one. There is one such vector for each area $0,\ldots,ed$. Otherwise write the maximum as $e+t$ with $1\le t<d$. Before its first occurrence, every entry is smaller and exactly $t$ missing pairs are allowed. This forces the initial sequence $e,e+1,\ldots,e+t-1$. No later entry can lie below $e+t-1$, since the earlier maximum would give one extra missing pair. Once the tail has dropped to $e+t-1$, it cannot return to $e+t$ because $e+t-1$ would have occurred twice. Thus after the forced prefix there are $b$ copies of $e+t$ and then $d-t-b$ copies of $e+t-1$, for $1\le b\le d-t$. Each such vector attains equality. Their areas are
$$
 ed+\binom t2+(t-1)(d-t)+b.
$$
For each $t$ the first area exceeds the last from the preceding group by one. The final area is $M$, proving the formula. In both descriptions the vector of the next area is obtained by increasing one entry by one. This gives a saturated chain spanning the fixed-endpoint area range. The adjacent differences for the full endpoint class also depend on the paths outside this chain.

## Two all-size consequences and an adjacent-sign question

Let $S$ be the sum of the $\ell$ smallest costs $i+j$. Equation (1) gives $K+J\ge S$. In particular, for every integer $v$,
$$
 \Pr(K\le v)\le \Pr(K\ge S-v).
$$
There is a stronger reciprocal bound at small corank. The $\ell$ distinct cells above determine unit squares in the positive quadrant, with interiors disjoint. Of all sets of area $\ell$, the integral of $px+qy$ is smallest on the triangle below its level line of intercept value $\sqrt{2pq\ell}$. This follows by exchanging the equally large portions inside and outside that triangle. The integral there is $(2/3)\sqrt{2pq}\,\ell^{3/2}$. On the squares the integral adds $(p+q)\ell/2$ to the weighted coordinate sum. Minimizing over $p/q$ yields the pathwise inequality
$$
 (K+\ell/2)(J+\ell/2)\ \ge\ 2\ell^3/9 .
$$
Using equality in distribution of $J,K$ gives, for every $v\ge0$,
$$
 \Pr(K\le v)\ \le\ \Pr\!\left(K\ge \frac{2\ell^3}{9(v+\ell/2)}-\frac{\ell}{2}\right). \tag{2}
$$
Both comparisons apply to the finite staircase rows without any limit or rounding convention on the real threshold.

For an adjacent-coefficient argument, it would suffice to prove that every total-degree component of $B_m(q,t)$ has coefficients increasing weakly up to its middle. Equivalently, $B_m$ would have a nonnegative Schur expansion in the **two grading variables**. A degree-$D$ Schur term at $t=1$ is an interval centered at $D/2$. As $D\ge S$, this hypothesis would give $b_i\le b_j$ whenever $i<j$ and $i+j\le S$, including growth through $\lceil S/2\rceil$. Since degree $a$ occurs $a+1$ times in the defining multiset, $S/2=m^{3/2}/6+O(m)$. The nested path theorem proves symmetry and Schur positivity in the separate symmetric-function alphabet with coefficients in $\mathbb N[q,t]$. Positivity of the Schur expansion in the grading variables is additional, and remains unproved here. Even that growth interval would still leave intermediate coranks in Conjecture 3.4. [Blasiak et al., Corollary 3.5.3](https://math.berkeley.edu/~mhaiman/ftp/jjag/lw-main.pdf) · [Bergeron, conjecture on the two Schur expansions](https://bergeron.math.uqam.ca/wp-content/uploads/2022/08/AIM_notes.pdf)

The [exact verifier](verify_trapezoids.py) enumerates the height vectors, checks symmetry and all homogeneous middle comparisons in 130 endpoint classes through $n=10$, and tests the endpoint minimum in four directions. It compares the two lowest homogeneous components to ordinary Catalan, constructs the lowest from subsets of a diagonal, and checks every coefficient of each endpoint's top component. Both specializations agree with direct strict-partition enumeration. The checks in the degrees between the proved components give finite evidence for the adjacent-sign approach.

~~~sh
python3 -B verify_trapezoids.py
~~~
