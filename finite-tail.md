# An effective bound at the high-rank end

For either central shape, let $b_k=a_{D-k}$, where $D$ is its number of cells. Thus $k$ is the number of missing cells. The following computer-assisted inequality holds for both families.
$$b_0<b_1<\cdots<b_{9n+42}\qquad(n\ge100).$$
The common cutoff 100 is sharp for this particular inequality. For the odd-part shape with $n=99$ the first failure of strict growth is the step from corank 930 to 931, and $9n+42=933$ there. The shape itself is unimodal.

The general construction also gives a terminating algorithm. Given any positive integer $c$, it produces an explicit $n_c$ for strict growth through corank $cn$ at every $n\ge n_c$. The numerical bound above uses several block lengths to obtain a smaller cutoff. Neither bound controls the sign change at the global peak.

## A coefficient inequality that survives multiplication

For an integer $s\ge0$, consider the condition on a polynomial $P=\sum p_iq^i$ with nonnegative integer coefficients (extend by zeros).
$$p_i\le p_j\quad\text{whenever }0\le i\le j,\quad i+j\le s. \tag{1}$$
It suffices to check $p_i\le p_{i+1}$ and $p_i\le p_{s-i}$ for $2i<s$. Indeed, when $j>s/2$ and $i+j\le s$, the first comparisons give $p_i\le p_{s-j}$ and the reflection gives $p_{s-j}\le p_j$.

For each positive integer $h$ split $\{i:p_i\ge h\}$ into maximal intervals. The indicators of these intervals, summed over levels, give exactly $P$. Condition (1) holds precisely when every such interval $[u,v]$ has $u+v\ge s$. If $u+v<s$, the required comparison between $u$ and $v+1$ fails at that level and $p_u>p_{v+1}$. Conversely an individual interval with $u+v\ge s$ satisfies (1), and the inequalities add.

Consequently a product of polynomials satisfying (1) with parameters $s_i$ satisfies it with parameter $\sum_i s_i$. For two interval polynomials, remove their initial monomials and put $I_d=1+\cdots+q^d$. The identity
$$I_d I_e=\sum_{j=0}^{\min(d,e)}q^j I_{d+e-2j}$$
puts every interval of this product at the sum of the original centers. Iterate and add. Multiplication by $q^u$ for $u\ge0$ increases the parameter by $2u$.

There is also a strict version. Suppose each factor has positive constant coefficient and strictly increasing coefficients up to $\lfloor s_i/2\rfloor$. The product then increases strictly through $T=\sum_i\lfloor s_i/2\rfloor$. For any $1\le j\le T$, choose $j_i\in[0,\lfloor s_i/2\rfloor]$ summing to $j$. In each factor some level interval starts at $j_i$. Their product contributes its first positive coefficient at $j$. Every other interval product increases weakly from $j-1$ to $j$ by (1).

## Finite bridge checks

Use the nonnegative ballot walks of length $m=2n+\delta$, $\delta\in\{0,1\}$. Their corank is $\sum_{t=1}^m\lfloor H_t/2\rfloor$, where $H_t$ is the height after step $t$. Cutting a walk into blocks makes this statistic additive if heights are kept absolute. For a block of length $L$ starting at an even height $x$, let $P_{L,x,y}$ count surviving walks to $y$ by this block area. A free-end block has polynomial $\sum_y P_{L,x,y}$.

| Steps $L$ | $s$ for each fixed endpoint | $s$ for a free endpoint |
| ---: | ---: | ---: |
| 48 | 124 | |
| 96 | 398 | |
| 192 | 1228 | |
| 384 | 3687 | 5229 |
| 385 | | 5254 |

Every listed polynomial satisfies (1) for every nonnegative even start. For the fixed-end columns at $x=y=0$, and for the free-end columns at $x=0$, the constant coefficient is positive and each step through $\lfloor s/2\rfloor$ is a strict increase.

The test starts with $P_{0,x,y}={\bf1}_{x=y}$ and appends one step using the recurrence
$$P_{t+1,x,y}=q^{\lfloor y/2\rfloor}(P_{t,x,y-1}+P_{t,x,y+1}),\qquad P_{t,x,-1}=0.$$
Computations modulo $q^{s+1}$ suffice. All paths have block area at least $\sum_{j=1}^L \lfloor\max(0,x-j)/2\rfloor$. As soon as twice this bound reaches $s$, (1) is automatic, including for arbitrarily large $x$. For this table all starts $x\ge104$ are covered that way. Unreachable endpoints give the zero polynomial. The checker packs coefficients in a base exceeding $2^L$ even when summing endpoints. It also checks small endpoint polynomials against explicit enumeration of step words, including a degree-truncated comparison.

## Passing from the table to every size

For $n\ge192$ write
$$n=192t+96a+48b+24c+r,\quad t\ge1,\quad a,b,c\in\{0,1\},\quad 0\le r<24.$$
Use a prefix of $2r$ steps, then $t-1$ blocks of 384 steps and $a,b,c$ blocks of 192, 96 and 48 steps, respectively. Finish with a free block of $384+\delta$ steps. Fix the prefix and the intermediate heights. The contribution factors as the prefix monomial times the corresponding block polynomials. Every term satisfies (1) with at least the sum of the tabulated parameters. The term with an alternating up-down prefix and all cuts at height zero satisfies the strict version, with no monomial shift. Summing over these disjoint choices proves strict growth through
$$T=1843(t-1)+614a+199b+62c+
\begin{cases}2614&(\delta=0),\\2627&(\delta=1).\end{cases}$$
For example, at $n=193$ this excludes reversals through coranks 2614 and 2627, respectively. For both parities
$$T-9n\ \ge\ 115t+771-250a-233b-154c-9r\ \ge\ 42.$$
The exact full rank calculation covers $100\le n<192$. For larger sizes it suffices to test unimodality from $b_T$ through $b_{\min(\lfloor D/2\rfloor,\,\lceil4m^{3/2}\rceil)}$, using the [lower-half inequality](monotonicity.md#1-lower-half-for-all-sizes) and [explicit growth beyond the midpoint](first-passage.md) at the other end.

Run the table check and the small-size test from the repository root with Python 3.9 or later.

~~~sh
python3 -B verify_blocks.py
~~~

## Why the search terminates for any fixed linear slope

First consider an ordinary Dyck excursion of length $2r$ returning to zero. Write $C_r(q)$ for its polynomial in the same area. For every fixed $A>0$, its coefficients increase strictly through $\lfloor Ar\rfloor$ for all sufficiently large $r$. Here are the details of the change from the free endpoint in the [fixed-tilt proof](monotonicity.md#3-decrease-near-the-top).

* At area $k$, at least $r-1-k$ interior even times have height zero. At any such time a down-up valley can be raised by two. A removable peak at area $k+1$ has height at least two, so it consumes at least one unit of area at its own time. Double-counting gives $(k+1)[q^{k+1}]C_r\ge(r-1-k)[q^k]C_r$, which gives strict growth when $2k<r-2$ and $[q^k]C_r>0$. All intervening ranks occur by successively lowering peaks of the maximal excursion.
* At a real tilt $z<0$, the transform for $C_r$ is $e_0 K_z^r e_0^{\mathsf T}$ for the same two-step operator as in the cited proof. Conditioning the endpoint to be zero replaces the terminal vector. Its projection onto the top eigenvector is strictly positive because that eigenvector is positive at zero. Thus the analytic expansion has positive prefactor. The spectral gap at nonzero Fourier frequencies, the range of slopes of $p=\log\rho(K_z)$, and $p''>0$ are unchanged. At $p'(z)=k/r$, inversion at $k$ and $k+1$ again gives ratio $e^{-z}(1+o(1))$ uniformly for $1/4\le k/r\le\max(A,1)$. The infimum of $e^{-z}$ exceeds one on this compact set. Together the two bounds prove the excursion assertion.

We need a uniform consequence for *all* endpoints. Fix $B>0$ and put $M=\lceil BL\rceil$. For all sufficiently large even $L$, every $P_{L,x,y}$ increases weakly through degree $M$. To prove this, discard classes of paths whose minimum possible degree exceeds $M$. In every remaining class $x,y=O_B(\sqrt L)$. Indeed the first $j$ steps can lower height by at most $j$, and the same observation applies in reverse time at the other end (including the terminal height in the area). For $x\ge L$ the lower bound already grows quadratically in $L$. For $x<L$ its first $x$ terms sum to $\lfloor(x-1)^2/4\rfloor$. These estimates also bound $y$.

Match each down step to the last unmatched up step when one exists. The unmatched steps descend from $x$ to the path minimum and then ascend to $y$. Their number is at most $x+y$. The substrings before, between, and after them are independent ordinary Dyck excursions once their semilengths are fixed. To see uniqueness, a matched pair encloses only matched steps, and a down step left unmatched occurs before every up step that is still unmatched at the end. Conversely, inserting any Dyck excursions at these vertices recovers precisely this matching and stays nonnegative.

An excursion of semilength $d$ inserted at height $v$ contributes $q^{vd} C_d(q)$. Translating by $v$ adds $vd$ to its area because exactly $d$ of its $2d$ heights are odd. The unmatched steps contribute a fixed nonnegative exponent. Split the polynomial according to the unmatched steps and all excursion lengths. For a resulting product with minimum exponent at most $M$, the sum of its semilengths at heights above $H=8\lceil B+1\rceil$ is at most $M/H\le L/8$ for large $L$. The total semilength is at least $L/2-O_B(\sqrt L)$. Thus at least $L/4$ semilength lies at heights $0,\ldots,H$. The descending and ascending legs together visit these heights in at most $2(H+1)$ slots. Some excursion has semilength $d\ge L/(8(H+1))$.

Apply the excursion assertion to that factor with $A=8(H+1)(B+1)$. It increases weakly through degree $M$. Fixing a monomial in every other factor only shifts it to the right, which preserves weak growth through that degree (coefficients below zero are zero). Summing proves the uniform bridge claim. In the zero-to-zero case the excursion assertion itself gives strict growth. This argument only needs a fixed linear window for ordinary Dyck excursions.

For a requested positive integer slope $c$, try even lengths $L=2,4,8,\ldots$ with $s=(c+1)L$. Test (1) for every fixed-endpoint bridge and strict initial growth through $s/2$ for the zero-to-zero bridge. The finite test at each $L$ uses the same truncation and start-height bound as the table. The uniform bridge claim ensures success eventually, without having to estimate a rate of spectral convergence.

Upon success let $a=s/2$. Use $\lfloor2n/L\rfloor$ such fixed-endpoint blocks followed by the remaining steps. Condition on all cut heights and the remaining steps. Choosing zero for all cut heights and an alternating remainder gives strict growth through $\lfloor2n/L\rfloor a\ge(c+1)n-a$. In particular $n_c=a$ works. Exhausting the sizes below this computable cutoff can then determine the sharp cutoff for that slope. For instance the following search finds $L=64$ and $n_1=64$.

~~~sh
python3 -B verify_blocks.py --slope 1
~~~

The slope is fixed before the search. Covering the peak for arbitrarily large $n$ would require control at coranks of order $n^{3/2}$.
