# Log-concavity at a fixed corank for unbounded size

Let $b_{n,k}$ count partitions missing $k$ cells from one of the two central staircases of size parameter $n$. Fix the parity of its largest part. We prove three assertions.

1. For $n\ge k$, $b_{n,k}$ is a polynomial in $n$ of degree $k$ with leading coefficient $1/k!$.
2. For every $1\le k\le256$ and every $n\ge\max(4,k+1)$, $b_{n,k}^2>b_{n,k-1}b_{n,k+1}$. This uses exact integer certificates of polynomial positivity.
3. For arbitrary $k\ge1$, the same strict inequality holds whenever $n\ge4(k+1)^2$. This uses only row counting.

Together with the [full rank checks](README.md#exact-coefficient-checks), assertion 2 gives strict log-concavity at every interior upper-half rank of corank at most 256 for **all** $n\ge9$. An upper-half rank is a rank $j=D-k\ge D/2$, where $D$ is the area of the shape.

## Removing row ends

Pad the strict partition $\mu$ with zeros to length $n$ and put $t_i=\lambda_i-\mu_i$. The $t_i$ are nonnegative and sum to $k$. A run of $r$ positive entries immediately followed by a zero entry has last deficit exactly one. Throughout this run $\mu_i>0$, and strictness means $t_i\le t_{i+1}+1$. These conditions also suffice. Indeed, counting backwards within the run bounds each deficit by its distance to the first zero, and the row lengths grow by two at every step backwards. Across a boundary from a zero deficit to a positive deficit strictness is automatic. Thus the weight polynomial $U_r(w)$ of a run followed by a zero is independent of its position and the parity. We have $U_0=1$, $U_1=w$. For a positive run at the very end let $V_r(w)$ be its weight polynomial, including the possibility of zero parts there. It depends only on $r$ and the parity because the last $r$ row lengths do. Put $V_0=1$. Both run polynomials have minimum degree $r$ and, for $0<t<1$, both are bounded at $w=t$ by $(t/(1-t))^r$, by allowing arbitrary positive entries.

Write $Z_n(w)=\sum_k b_{n,k}w^k$, $Z_0=1$. Splitting at the first zero deficit gives the formal identity
$$
\sum_{n\ge0} Z_n(w)z^n
=\frac{\sum_{r\ge0}V_r(w)z^r}
       {1-z-\sum_{r\ge1}U_r(w)z^{r+1}}.
$$
Expand the denominator as a geometric series in the nonempty runs, keeping the factor $1-z$ intact. Choose $h$ such runs and the terminal run, with a combined $v$ positive entries. Their length factor is $z^{v+h}/(1-z)^{h+1}$, and their area factor is a product of the run polynomials. For a contribution to $[w^k]$, necessarily $h\le v\le k$. For $n\ge k$ the length coefficient is $\binom{n-v}{h}$, including zero when $0\le n-v<h$. Thus $b_{n,k}$ is a nonnegative integral combination of these binomial polynomials. The only term of degree $k$ has $h=v=k$, all nonterminal runs of length one, and empty terminal run. It contributes $\binom{n-k}{k}$, proving assertion 1.

## Certifying a corank for all larger sizes

For $n\ge k+1$, the determinant $L_k(n)=b_{n,k}^2-b_{n,k-1}b_{n,k+1}$ is a polynomial of degree $2k$. Its leading coefficient is $1/((k+1)(k!)^2)$. At any integer $a\ge k+1$, Newton interpolation gives
$$L_k(n)=\sum_{h=0}^{2k}(\Delta^h L_k)(a)\binom{n-a}{h},\qquad
(\Delta L)(a)=L(a+1)-L(a).$$
For each $1\le k\le256$ take $a=\max(4,k+1)$. Every one of the $2k+1$ integer coefficients is strictly positive for both families. The script recomputes each coefficient, checks that the next difference vanishes, and compares the underlying corank rows against direct enumeration at small sizes. Since the constant term is positive and all binomial factors are nonnegative for $n\ge a$, this certifies every such $n$.

~~~sh
python3 -B verify_corank.py --max-corank 256 --direct-n 12
~~~

The verifier keeps the endpoint height of the ballot walk and discards coefficients above the requested degree. All prefix areas are nondecreasing. Reaching height $2h$ already costs at least $h^2$, the sum of the contributions at the first visits to heights $1,\ldots,2h$. A prefix ending at $2h+1$ costs at least as much. The truncations therefore preserve every retained count. The direct checks also cover coefficients beyond the true degree, where the truncated array is padded with zeros.

## A counting proof when the size is at least quadratic in the corank

For $1\le j\le n$ put $N_j=\binom nj$, and put $N_0=1$. Every zero-one deficit vector of weight $j$ is admissible. If some $t_i\ge2$ with $i<n$, then $t_{i+1}\ge1$. Otherwise the unshortened positive next row would be at least as long as row $i$. The only other possibility is $t_n\ge2$. Subtract the indicated two units and, in the nonterminal case, the additional unit from the next row. Counting the remaining weak compositions, with a zero contribution when $j<d$ units have been subtracted, gives
$$
N_j\ \le\ b_{n,j}\ \le\ N_j+n\binom{n+j-4}{j-3}+\binom{n+j-3}{j-2}.
$$
If $n\ge4j^2$ and $d=2,3$ with $j\ge d$, the ratio of $\binom{n+j-d-1}{j-d}$ to $N_j$ is bounded by
$$
(j/n)^d\left(\frac{n+j}{n-j+1}\right)^j\le (j/n)^d e^{2j^2/(n-j+1)}<2(j/n)^d.
$$
Here $j-1\le j^2/4\le n/16$. Thus $b_{n,j}/N_j\le1+4j^3/n^2$, also valid at $j=0$. For $n\ge4(k+1)^2$ both neighbors at $j=k\pm1$ have relative excess at most $1/(4(k+1))$. The binomial ratio $N_k^2/(N_{k-1}N_{k+1})\ge1+1/k$ exceeds the square of $1+1/(4(k+1))$. This proves assertion 3.
